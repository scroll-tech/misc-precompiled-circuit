// The constraint system matrix for rmd160.

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, Region},
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
    poly::Rotation,
};

use std::marker::PhantomData;
use crate::host::rmd160::{
    ROUNDS_OFFSET,
    PROUNDS_OFFSET,
    R, O, PR, PO,
    RMD160Atomic,
};
use crate::constant;
use halo2_gate_generator::{
    customized_circuits,
    table_item,
    item_count,
    customized_circuits_expand,
    value_for_assign,
    Limb,
    GateCell,
};

use crate::utils::{
    field_to_u64,
    field_to_u32,
};

pub fn u32_to_limbs<F: FieldExt>(v: u32) -> [F; 4] {
    let mut rem = v;
    let mut r = vec![];
    for _ in 0..4 {
        r.append(&mut vec![F::from((rem % 256) as u64)]);
        rem = rem/256;
    }
    r.try_into().unwrap()
}

pub fn limb_to_u32<F: FieldExt>(limb: &Limb<F>) -> [F; 4] {
    let a = field_to_u32(&limb.value);
    u32_to_limbs(a)
}

pub struct RMD160Chip<F: FieldExt> {
    config: RMD160Config,
    _marker: PhantomData<F>,
}


customized_circuits!(RoundGateConfig, 5, 7, 3, 0,
    | a   | b     | c    |  d   | x    | e     | c_next |  offset  | h_sel | r_sel
    | w0  | b0    | c0   |  d0  | r0   | w1_h  | w4_h   |  w1_r    | nil   | nil
    | wb  | b1    | c1   |  d1  | r1   | w1_l  | w4_l   |  w1_rr   | nil   | nil
    | wc  | b2    | c2   |  d2  | r2   | a_next| w2b    |  nil     | nil   | nil
    | w1  | b3    | c3   |  d3  | r3   | nil   | w2c    |  nil     | nil   | nil
);

/* All witness we need to fill the gate */
struct RoundWitness<F: FieldExt> {
    r: u32,  // atomic(b, c, d)
    w0: u32, // a + r + x + offset
    wb: F, // a + r + x + offset u64
    wc: u64, // wb - w0
    w1: u32, // w0 rorate_left w1_r
    w1_h: u32,  //w1 >> w1_r
    w1_l: u32,  //w1 % w1_r
    a_next: u32, // w1 + e
    w2b: F, // w1+e u64
    w2c: u64, // w2b - a_next
    w4_h: u32, // c >> w4_r
    w4_l: u32, // c % w4_r
    c_next: u32, // c rotate_left 10
}


fn get_witnesses<F: FieldExt>(round: usize, rol: &[u32; 5], x: u32, shift: u32, offset:u32, pround: bool) -> RoundWitness<F> {
    let f = if pround {5 - round - 1} else { round };
    let r = u32::atomic(f, rol[1], rol[2], rol[3]);
    let w0 = r.wrapping_add(rol[0]).wrapping_add(x).wrapping_add(offset);
    let wb = F::from(r as u64) + F::from(rol[0] as u64) + F::from(x as u64) + F::from(offset as u64);
    let wc = (field_to_u64(&wb) - (w0 as u64)) >> 32;
    let w1 = w0.rotate_left(shift);
    let w1_h = w0 >> (32 - shift);
    let w1_l = w0 % (2u32.pow(32 - shift));
    let a_next = w1.wrapping_add(rol[4]);
    let w2b = F::from(w1 as u64) + F::from(rol[4] as u64);
    let w2c = (field_to_u64(&w2b) - (a_next as u64)) >> 32;
    let w4_h = rol[2] >> 22;
    let w4_l = rol[2] % (2u32.pow(22));
    let c_next = rol[2].rotate_left(10);

    //println!("round {}, shift {}, offset {} x {}", r, shift ,offset, x);
    //println!("w2c {}", w2c);

    RoundWitness {
        r, w0, wb, wc, w1, w1_h, w1_l, a_next, w2b, w2c, w4_h, w4_l, c_next
    }
}


customized_circuits!(CompressSumConfig, 5, 7, 3, 0,
| a   | b1    | c2   | sum0 | ca0  | bnew  | col6 | col7 | h_sel| r_sel
| b   | c1    | d2   | sum1 | ca1  | cnew  | nil  | nil  | nil  | nil
| c   | d1    | e2   | sum2 | ca2  | dnew  | nil  | nil  | nil  | nil
| d   | e1    | a2   | sum3 | ca3  | enew  | nil  | nil  | nil  | nil
| e   | a1    | b2   | sum4 | ca4  | anew  | nil  | nil  | nil  | nil
);



#[derive(Clone, Debug)]
pub struct RMD160Config {
    compress_sum_config: CompressSumConfig,
    round_config: RoundGateConfig,
}

impl<F: FieldExt> Chip<F> for RMD160Chip<F> {
    type Config = RMD160Config;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> RMD160Chip<F> {
    pub fn new(config: RMD160Config) -> Self {
        RMD160Chip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> RMD160Config {
        let witness= [0; 7]
                .map(|_|cs.advice_column());
        let fixed= [0; 3]
                .map(|_|cs.fixed_column());
        let selector= [];
        witness.map(|x| cs.enable_equality(x));

        let config = RMD160Config {
            compress_sum_config: CompressSumConfig::new(witness, fixed, selector),
            round_config: RoundGateConfig::new(witness, fixed, selector)
        };

        cs.create_gate("sum with bound", |meta| {
            let r0 = config.round_config.get_expr(meta, RoundGateConfig::r0());
            let r1 = config.round_config.get_expr(meta, RoundGateConfig::r1());
            let r2 = config.round_config.get_expr(meta, RoundGateConfig::r2());
            let r3 = config.round_config.get_expr(meta, RoundGateConfig::r3());
            let sum_r = r0 + (r1 + (r2 + r3 * F::from(1u64 << 8)) * F::from(1u64 << 8)) * F::from(1u64 << 8);
            let w0 = config.round_config.get_expr(meta, RoundGateConfig::w0());
            let wb = config.round_config.get_expr(meta, RoundGateConfig::wb());
            let wc = config.round_config.get_expr(meta, RoundGateConfig::wc());
            let a = config.round_config.get_expr(meta, RoundGateConfig::a());
            let x = config.round_config.get_expr(meta, RoundGateConfig::x());
            let offset = config.round_config.get_expr(meta, RoundGateConfig::offset());
            let hsel = config.round_config.get_expr(meta, RoundGateConfig::h_sel());
            vec![
                (wb.clone() - sum_r - a - x - offset) * hsel.clone(),
                //(wc.clone()*(wc.clone() - constant!(F::one()))) * hsel.clone(),
                (w0 + wc * F::from(1u64 << 32) - wb) * hsel,
            ]
        });

        cs.create_gate("sum with w1 rol4", |meta| {
            let a_next = config.round_config.get_expr(meta, RoundGateConfig::a_next());
            let hsel = config.round_config.get_expr(meta, RoundGateConfig::h_sel());
            let w1 = config.round_config.get_expr(meta, RoundGateConfig::w1());
            let w2b = config.round_config.get_expr(meta, RoundGateConfig::w2b());

            let w2c = config.round_config.get_expr(meta, RoundGateConfig::w2c());
            let e = config.round_config.get_expr(meta, RoundGateConfig::e());
            vec![
                (w2b.clone() - w1 - e) * hsel.clone(),
                (w2c.clone()*(w2c.clone() - constant!(F::one()))) * hsel.clone(),
                (a_next + w2c * F::from(1u64 << 32) - w2b) * hsel,
            ]
        });

        cs.create_gate("limbs sum", |meta| {
            let hsel = config.round_config.get_expr(meta, RoundGateConfig::h_sel());

            let b = config.round_config.get_expr(meta, RoundGateConfig::b());
            let b0 = config.round_config.get_expr(meta, RoundGateConfig::b0());
            let b1 = config.round_config.get_expr(meta, RoundGateConfig::b1());
            let b2 = config.round_config.get_expr(meta, RoundGateConfig::b2());
            let b3 = config.round_config.get_expr(meta, RoundGateConfig::b3());
            let sum_b = b0 + (b1 + (b2 + b3 * F::from(1u64 << 8)) * F::from(1u64 << 8)) * F::from(1u64 << 8);

            let c = config.round_config.get_expr(meta, RoundGateConfig::c());
            let c0 = config.round_config.get_expr(meta, RoundGateConfig::c0());
            let c1 = config.round_config.get_expr(meta, RoundGateConfig::c1());
            let c2 = config.round_config.get_expr(meta, RoundGateConfig::c2());
            let c3 = config.round_config.get_expr(meta, RoundGateConfig::c3());
            let sum_c = c0 + (c1 + (c2 + c3 * F::from(1u64 << 8)) * F::from(1u64 << 8)) * F::from(1u64 << 8);

            let d = config.round_config.get_expr(meta, RoundGateConfig::d());
            let d0 = config.round_config.get_expr(meta, RoundGateConfig::d0());
            let d1 = config.round_config.get_expr(meta, RoundGateConfig::d1());
            let d2 = config.round_config.get_expr(meta, RoundGateConfig::d2());
            let d3 = config.round_config.get_expr(meta, RoundGateConfig::d3());
            let sum_d = d0 + (d1 + (d2 + d3 * F::from(1u64 << 8)) * F::from(1u64 << 8)) * F::from(1u64 << 8);

            vec![
                (sum_b - b) * hsel.clone(),
                (sum_c - c) * hsel.clone(),
                (sum_d - d) * hsel.clone(),
            ]
        });

        cs.create_gate("c rotate", |meta| {
            let hsel = config.round_config.get_expr(meta, RoundGateConfig::h_sel());

            let c = config.round_config.get_expr(meta, RoundGateConfig::c());
            let c_next = config.round_config.get_expr(meta, RoundGateConfig::c_next());
            let w4l = config.round_config.get_expr(meta, RoundGateConfig::w4_l());
            let w4h = config.round_config.get_expr(meta, RoundGateConfig::w4_h());

            vec![
                (w4h.clone() * constant!(F::from(1u64 << 22)) + w4l.clone() - c.clone()) * hsel.clone(),
                (w4l * constant!(F::from(1u64 << 10)) + w4h - c_next.clone()) * hsel.clone(),
            ]
        });

        cs.create_gate("w0 rotate", |meta| {
            let hsel = config.round_config.get_expr(meta, RoundGateConfig::h_sel());
            let w0 = config.round_config.get_expr(meta, RoundGateConfig::w0());
            let w1 = config.round_config.get_expr(meta, RoundGateConfig::w1());
            let w1l = config.round_config.get_expr(meta, RoundGateConfig::w1_l());
            let w1h = config.round_config.get_expr(meta, RoundGateConfig::w1_h());
            let shift = config.round_config.get_expr(meta, RoundGateConfig::w1_r());
            let shift2 = config.round_config.get_expr(meta, RoundGateConfig::w1_rr());

            vec![
                (w1h.clone() * shift2.clone() + w1l.clone() - w0) * hsel.clone(),
                (w1l * shift + w1h - w1) * hsel.clone(),
            ]
        });

        config
    }


    fn assign_next(
        &self,
        region: &mut Region<F>,
        start_offset: usize,
        previous: &[Limb<F>; 5],
        input: &Limb<F>,
        round: usize,
        index: usize,
        shift: &[[u32; 16]; 5],
        offset: &[u32; 5],
        pround: bool,
    ) -> Result<[Limb<F>; 5], Error> {
        //println!("rol: {:?}", previous.clone().map(|x| cell_to_u32(&x)));
        self.config.round_config.bind_cell(region, start_offset, &RoundGateConfig::a(), &previous[0])?;
        let b = self.config.round_config.bind_cell(region, start_offset, &RoundGateConfig::b(), &previous[1])?;
        self.config.round_config.bind_cell(region, start_offset, &RoundGateConfig::c(), &previous[2])?;
        let d = self.config.round_config.bind_cell(region, start_offset, &RoundGateConfig::d(), &previous[3])?;
        let e = self.config.round_config.bind_cell(region, start_offset, &RoundGateConfig::e(), &previous[4])?;

        self.config.round_config.bind_cell(region, start_offset, &RoundGateConfig::x(), input)?;

        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w1_r(), F::from(1u64 << shift[round][index]))?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w1_rr(), F::from(1u64 << (32 - shift[round][index])))?;

        let blimbs = limb_to_u32(&previous[1]);
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::b0(), blimbs[0])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::b1(), blimbs[1])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::b2(), blimbs[2])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::b3(), blimbs[3])?;

        let climbs = limb_to_u32(&previous[2]);
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::c0(), climbs[0])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::c1(), climbs[1])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::c2(), climbs[2])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::c3(), climbs[3])?;

        let dlimbs = limb_to_u32(&previous[3]);
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::d0(), dlimbs[0])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::d1(), dlimbs[1])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::d2(), dlimbs[2])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::d3(), dlimbs[3])?;

        let rol = previous.into_iter()
            .map(|c| {
                field_to_u32(&c.value)
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let witness = get_witnesses(round, &rol, field_to_u32(&input.value), shift[round][index], offset[round], pround);
        //self.assign_cell(region, start_offset, RoundGateConfig::r(), F::from(witness.r as u64));
        //
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::offset(), F::from(offset[round] as u64))?;
        let rlimbs = u32_to_limbs(witness.r);

        let mut sum_r = rlimbs[0];
        for i in 1..4 {
            sum_r = sum_r + rlimbs[i] * F::from(1u64 << (8*i));
        }

        assert!(sum_r == F::from(witness.r as u64));

        assert!(witness.w2b == F::from(witness.w1 as u64) + F::from(field_to_u32(&previous[4].value) as u64));
        assert!(witness.wb == F::from(witness.r as u64) + F::from(field_to_u32(&previous[0].value) as u64)
                + F::from(field_to_u32(&input.value) as u64) + F::from(offset[round] as u64));

        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::r0(), rlimbs[0])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::r1(), rlimbs[1])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::r2(), rlimbs[2])?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::r3(), rlimbs[3])?;

        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w0(), F::from(witness.w0 as u64))?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::wb(), witness.wb)?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::wc(), F::from(witness.wc as u64))?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w1(), F::from(witness.w1 as u64))?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w1_h(), F::from(witness.w1_h as u64))?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w1_l(), F::from(witness.w1_l as u64))?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w4_h(), F::from(witness.w4_h as u64))?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w4_l(),F::from(witness.w4_l as u64))?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w2b(),witness.w2b)?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::w2c(),F::from(witness.w2c as u64))?;
        self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::h_sel(), F::one())?;
        let a = self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::a_next(), F::from(witness.a_next as u64))?;
        let c = self.config.round_config.assign_cell(region, start_offset, &RoundGateConfig::c_next(), F::from(witness.c_next as u64))?;
        Ok([e, a, b, c, d])
    }

    fn rotate_inputs(
        &self,
        inputs: &[Limb<F>; 16],
        round_shift: [usize; 16],
    ) -> [Limb<F>; 16] {
        round_shift.map(|i| inputs[i].clone())
    }

    pub fn assign_compress(
        &self,
        region: &mut Region<F>,
        start_offset: usize,
        r0: &[Limb<F>; 5],
        r1: &[Limb<F>; 5],
        r2: &[Limb<F>; 5],
    ) -> Result<[Limb<F>; 5], Error> {
        self.config.round_config.bind_cell(region, start_offset, &CompressSumConfig::a(), &r0[0])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::b(), &r0[1])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::c(), &r0[2])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::d(), &r0[3])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::e(), &r0[4])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::a1(), &r1[0])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::b1(), &r1[1])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::c1(), &r1[2])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::d1(), &r1[3])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::e1(), &r1[4])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::a2(), &r2[0])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::b2(), &r2[1])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::c2(), &r2[2])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::d2(), &r2[3])?;
        self.config.compress_sum_config.bind_cell(region, start_offset, &CompressSumConfig::e2(), &r2[4])?;

        let anew = {
            let anew = field_to_u32(&r0[0].value)
                .wrapping_add(field_to_u32(&r1[1].value))
                .wrapping_add(field_to_u32(&r2[2].value));
            let sum0 = r0[0].value
                + r1[1].value
                + r2[2].value;
            let ca0 = (field_to_u64(&sum0) - anew as u64) >> 32;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::sum0(), sum0)?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::ca0(), F::from(ca0))?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::anew(), F::from(anew as u64))?
        };

        let bnew = {
            let bnew = field_to_u32(&r0[1].value)
                .wrapping_add(field_to_u32(&r1[2].value))
                .wrapping_add(field_to_u32(&r2[3].value));
            let sum1 = r0[1].value
                + r1[2].value
                + r2[3].value;
            let ca1 = (field_to_u64(&sum1) - bnew as u64) >> 32;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::sum1(), sum1)?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::ca1(), F::from(ca1))?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::bnew(), F::from(bnew as u64))?
        };

        let cnew = {
            let cnew = field_to_u32(&r0[2].value)
                .wrapping_add(field_to_u32(&r1[3].value))
                .wrapping_add(field_to_u32(&r2[4].value));
            let sum2 = r0[2].value
                + r1[3].value
                + r2[4].value;
            let ca2 = (field_to_u64(&sum2) - cnew as u64) >> 32;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::sum2(), sum2)?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::ca0(), F::from(ca2))?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::cnew(), F::from(cnew as u64))?
        };

        let dnew = {
            let dnew = field_to_u32(&r0[3].value)
                .wrapping_add(field_to_u32(&r1[4].value))
                .wrapping_add(field_to_u32(&r2[0].value));
            let sum3 = r0[3].value
                + r1[4].value
                + r2[0].value;
            let ca3 = (field_to_u64(&sum3) - dnew as u64) >> 32;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::sum3(), sum3)?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::ca3(), F::from(ca3))?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::dnew(), F::from(dnew as u64))?
        };

        let enew = {
            let enew = field_to_u32(&r0[4].value)
                .wrapping_add(field_to_u32(&r1[0].value))
                .wrapping_add(field_to_u32(&r2[1].value));
            let sum4 = r0[4].value
                + r1[0].value
                + r2[1].value;
            let ca4 = (field_to_u64(&sum4) - enew as u64) >> 32;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::sum4(), sum4)?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::ca4(), F::from(ca4))?;
            self.config.compress_sum_config.assign_cell(region, start_offset, &CompressSumConfig::enew(), F::from(enew as u64))?
        };

        Ok([anew, bnew, cnew, dnew, enew])
    }


    pub fn assign_content(
        &self,
        layouter: &mut impl Layouter<F>,
        start_buf: &[Limb<F>; 5],
        inputs: &[Limb<F>; 16],
    ) -> Result<[Limb<F>; 5], Error> {
        let r = layouter.assign_region(
            || "leaf layer",
            |mut region| {
                let mut r1 = start_buf.clone();
                let mut start_offset = 0;
                for round in 0..5 {
                    for index in 0..16 {
                        r1 = self.assign_next(
                            &mut region,
                            start_offset,
                            &r1,
                            &self.rotate_inputs(inputs, O[round])[index],
                            round,
                            index,
                            &R,
                            &ROUNDS_OFFSET,
                            false,
                        )?;
                        start_offset += 5;
                    }
                }
                /*
                println!("{} {} {} {} {}",
                    cell_to_u32(&r1[0]),
                    cell_to_u32(&r1[1]),
                    cell_to_u32(&r1[2]),
                    cell_to_u32(&r1[3]),
                    cell_to_u32(&r1[4]),
                );
                */

                let mut r2 = start_buf.clone();
                for round in 0..5 {
                    for index in 0..16 {
                        r2 = self.assign_next(
                            &mut region,
                            start_offset,
                            &r2,
                            &self.rotate_inputs(&inputs, PO[round])[index],
                            round,
                            index,
                            &PR,
                            &PROUNDS_OFFSET,
                            true
                        )?;
                        start_offset += 5;
                    }
                }
                self.assign_compress(&mut region, start_offset, start_buf, &r1, &r2)
            }
        )?;
        Ok(r)
    }
}



#[cfg(test)]
mod tests {
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::dev::MockProver;

    use halo2_proofs::{
        circuit::{Chip, Layouter, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error,
        },
    };

    use super::RMD160Chip;
    use super::RMD160Config;
    use crate::host::rmd160::H0;
    use crate::value_for_assign;
    use crate::utils::field_to_u32;
    use halo2_gate_generator::Limb;



    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        limb: Column<Advice>
    }

    #[derive(Clone, Debug)]
    pub struct HelperChip {
        config: HelperChipConfig
    }

    impl Chip<Fr> for HelperChip {
        type Config = HelperChipConfig;
        type Loaded = ();

        fn config(&self) -> &Self::Config {
            &self.config
        }

        fn loaded(&self) -> &Self::Loaded {
            &()
        }
    }

    impl HelperChip {
        fn new(config: HelperChipConfig) -> Self {
            HelperChip{
                config,
            }
        }

        fn configure(cs: &mut ConstraintSystem<Fr>) -> HelperChipConfig {
            let limb= cs.advice_column();
            cs.enable_equality(limb);
            HelperChipConfig {
                limb,
            }
        }

        fn assign_w(
            &self,
            layouter: &mut impl Layouter<Fr>,
            inputs: &[u32; 5],
            offset: usize,
        ) -> Result<[Limb<Fr>; 5], Error> {
            layouter.assign_region(
                || "leaf layer",
                |mut region| {
                    let mut r = vec![];
                    for round in 0..5 {
                        let cell = region.assign_advice(
                            || format!("assign w"),
                            self.config.limb,
                            offset + round,
                            || value_for_assign!(Fr::from(inputs[round] as u64))
                        )?;
                        r.push(Limb::new(Some(cell), Fr::from(inputs[round] as u64)))
                    }
                    Ok(r.try_into().unwrap())
                }
            )
        }

        fn assign_inputs(
            &self,
            layouter: &mut impl Layouter<Fr>,
            inputs: &[Fr; 16],
            offset: usize
        ) -> Result<[Limb<Fr>; 16], Error> {
            layouter.assign_region(
                || "leaf layer",
                |mut region| {
                    let mut r = vec![];
                    for i in 0..16 {
                        let cell = region.assign_advice(
                            || format!("assign input"),
                            self.config.limb,
                            offset + i,
                            || value_for_assign!(inputs[i])
                        )?;
                        r.push(Limb::new(Some(cell), inputs[i]));
                    }
                    Ok(r.try_into().unwrap())
                }
            )
        }
    }

    #[derive(Clone, Debug, Default)]
    struct RMD160Circuit {
        inputs: [Fr; 16],
    }

    #[derive(Clone, Debug)]
    struct TestConfig {
        rmd160config: RMD160Config,
        helperconfig: HelperChipConfig,
    }

    impl Circuit<Fr> for RMD160Circuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            Self::Config {
               rmd160config: RMD160Chip::<Fr>::configure(meta),
               helperconfig: HelperChip::configure(meta)
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let rmd160chip = RMD160Chip::<Fr>::new(config.clone().rmd160config);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let w= helperchip.assign_w(&mut layouter, &H0, 0)?;
            let input = helperchip.assign_inputs(&mut layouter, &self.inputs, 0)?;
            let r = rmd160chip.assign_content(&mut layouter, &w, &input)?;
            println!("{} {} {} {} {}",
                field_to_u32(&r[0].value),
                field_to_u32(&r[1].value),
                field_to_u32(&r[2].value),
                field_to_u32(&r[3].value),
                field_to_u32(&r[4].value),
            );
            Ok(())
        }
    }

    #[test]
    fn test_rmd160_circuit() {
        let test_circuit = RMD160Circuit {inputs: [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16].map(|x| Fr::from(x as u64))} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}


