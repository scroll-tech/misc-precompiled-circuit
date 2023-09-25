use crate::utils::{bn_to_field, field_to_bn};
use halo2_gate_generator::Limb;

use crate::circuits::CommonGateConfig;

use crate::circuits::range::{RangeCheckChip, RangeCheckConfig};

use std::ops::{Div, Mul};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Region},
    plonk::{ConstraintSystem, Error},
};
use num_bigint::BigUint;
use std::marker::PhantomData;

pub struct ModExpChip<F: FieldExt> {
    config: CommonGateConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct Number<F: FieldExt> {
    pub limbs: [Limb<F>; 4],
}

impl<F: FieldExt> Number<F> {
    pub fn add(&self, n: &Self) -> Self {
        Number {
            limbs: [
                Limb::new(None, self.limbs[0].value + n.limbs[0].value),
                Limb::new(None, self.limbs[1].value + n.limbs[1].value),
                Limb::new(None, self.limbs[2].value + n.limbs[2].value),
                Limb::new(None, self.limbs[3].value + n.limbs[3].value),
            ],
        }
    }
    pub fn from_bn(bn: &BigUint) -> Self {
        let limb0 = bn.modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
        let limb1 = (bn - limb0.clone())
            .div(BigUint::from(1u128 << 108))
            .modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
        let limb2 = bn
            .div(BigUint::from(1u128 << 108))
            .div(BigUint::from(1u128 << 108));
        let native = bn % (field_to_bn(&(-F::one())) + BigUint::from(1u128));
        Number {
            limbs: [
                Limb::new(None, bn_to_field(&limb0)),
                Limb::new(None, bn_to_field(&limb1)),
                Limb::new(None, bn_to_field(&limb2)),
                Limb::new(None, bn_to_field(&native)),
            ],
        }
    }
    pub fn to_bn(&self) -> BigUint {
        let limb0 = field_to_bn(&self.limbs[0].value);
        let limb1 = field_to_bn(&self.limbs[1].value);
        let limb2 = field_to_bn(&self.limbs[2].value);
        (limb2 * BigUint::from(1u128 << 108) + limb1) * BigUint::from(1u128 << 108) + limb0
    }
}

impl<F: FieldExt> Chip<F> for ModExpChip<F> {
    type Config = CommonGateConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> ModExpChip<F> {
    pub fn new(config: CommonGateConfig) -> Self {
        ModExpChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        cs: &mut ConstraintSystem<F>,
        range_check_config: &RangeCheckConfig,
    ) -> CommonGateConfig {
        CommonGateConfig::configure(cs, range_check_config)
    }

    pub fn assign_constant(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        number: Number<F>,
        limbbound: u64,
    ) -> Result<Number<F>, Error> {
        let mut limbs = vec![];
        for i in 0..4 {
            let l = self.config.assign_line(
                region,
                range_check_chip,
                offset,
                [Some(number.limbs[i].clone()), None, None, None, None, None],
                [
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    Some(F::from(number.limbs[i].value)),
                    None,
                    None,
                ],
                limbbound,
            )?;
            limbs.push(l[0].clone())
        }
        Ok(Number {
            limbs: limbs.try_into().unwrap(),
        })
    }

    pub fn assign_number(
        &self,
        _region: &mut Region<F>,
        _range_check_chip: &mut RangeCheckChip<F>,
        _offset: &mut usize,
        number: Number<F>,
    ) -> Result<Number<F>, Error> {
        Ok(number)
    }

    /// check whether lhs is less or equal to rhs
    fn le_limb(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Limb<F>,
    ) -> Result<Limb<F>, Error> {
        let bn_rhs = field_to_bn(&rhs.value);
        let bn_lhs = field_to_bn(&lhs.value);
        let (diff_true, diff_false) = (
            Limb::new(None, bn_to_field::<F>(&bn_rhs) - bn_to_field::<F>(&bn_lhs)),
            Limb::new(None, bn_to_field::<F>(&bn_lhs) - bn_to_field::<F>(&bn_rhs) - F::one())
        );
        let (abs, res) = if bn_rhs >= bn_lhs {
            (
                Limb::new(None, bn_to_field::<F>(&(bn_rhs - bn_lhs))),
                Limb::new(None, F::one())
            )
        } else {
            (
                Limb::new(None, bn_to_field::<F>(&(bn_lhs - bn_rhs - BigUint::from(1u64)))),
                Limb::new(None, F::zero())
            )
        };
        let true_limb = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(diff_true.clone()),
                Some(rhs.clone()),
                Some(lhs.clone()),
                None,
                None,
                None,
            ],
            [
                Some(-F::one()),
                Some(F::one()),
                Some(-F::one()),
                None,
                None, None,
                None, None, None
            ],
            0,
        )?[0].clone();

        let false_limb = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(diff_false.clone()),
                Some(rhs.clone()),
                Some(lhs.clone()),
                None,
                None,
                None,
            ],
            [
                Some(-F::one()),
                Some(-F::one()),
                Some(F::one()),
                None,
                None,
                None, None, None,
                Some(-F::one()),
            ],
            0,
        )?[0].clone();

        //res (abs - true_limb) == 0
        let [abs, _, _, res]: [Limb<_>; 4] = self.config.assign_line (
            region,
            range_check_chip,
            offset,
            [
                Some(abs.clone()),
                Some(res.clone()),
                Some(true_limb.clone()),
                Some(res.clone()),
                None,
                None,
            ],
            [
                None,
                None,
                None,
                None,
                None,
                None,
                Some(F::one()), Some(-F::one()),
                None
            ],
            9,
        )?.try_into().unwrap();

        // (res - 1) (abs - false_limb)
        self.config.assign_line (
            region,
            range_check_chip,
            offset,
            [
                Some(res.clone()),
                Some(res.clone()),
                Some(abs.clone()),
                Some(false_limb),
                None,
                None,
            ],
            [
                None,
                None,
                Some(-F::one()),
                Some(F::one()),
                None,
                None,
                Some(-F::one()), Some(F::one()),
                None
            ],
            0,
        )?;
        Ok(res.clone())
    }

    fn lt_number(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<(), Error> {
        // gt2 means lhs[2] >= rhs[2]
        let gt2 = self.le_limb(region, range_check_chip, offset, &rhs.limbs[2], &lhs.limbs[2])?;
        // gt1 means lhs[1] >= rhs[1]
        let gt1 = self.le_limb(region, range_check_chip, offset, &rhs.limbs[1], &lhs.limbs[1])?;
        // gt0 means lhs[0] >= rhs[0]
        let gt0 = self.le_limb(region, range_check_chip, offset, &rhs.limbs[0], &lhs.limbs[0])?;

        let zero = self.config.assign_constant(region, range_check_chip, offset, &F::zero())?;
        let one= self.config.assign_constant(region, range_check_chip, offset, &F::one())?;

        // if gt0 then zero else one means if lhs[0] < rhs[0] then one else zero
        let lt_0 = self.config.select(region, range_check_chip, offset, &gt0, &one, &zero, 0)?;

        // if gt1 then zero else one means if lhs[1] < rhs[1] then one else lt_0
        let lt_1 = self.config.select(region, range_check_chip, offset, &gt1, &one, &lt_0, 0)?;

        // if gt2 then zero else one means if lhs[2] < rhs[2] then one else lt_1
        let lt = self.config.select(region, range_check_chip, offset, &gt2, &one, &lt_1, 0)?;
        self.config.eq_constant(region, range_check_chip, offset, &lt, &F::one())?;
        Ok(())
    }

    pub fn mod_add(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let ret = lhs.add(rhs);
        let limbs = ret
            .limbs
            .to_vec()
            .into_iter()
            .enumerate()
            .map(|(i, l)| {
                let l = self
                    .config
                    .assign_line(
                        region,
                        range_check_chip,
                        offset,
                        [
                            Some(lhs.limbs[i].clone()),
                            Some(rhs.limbs[i].clone()),
                            None,
                            None,
                            Some(l),
                            None,
                        ],
                        [
                            Some(F::one()),
                            Some(F::one()),
                            None,
                            None,
                            Some(F::one()),
                            None,
                            None,
                            None,
                            None,
                        ],
                        0,
                    )
                    .unwrap();
                l[2].clone() // the fifth is the sum result d
            })
            .collect::<Vec<_>>();
        Ok(Number {
            limbs: limbs.try_into().unwrap(),
        })
    }

    pub fn mod_native_mul(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        rem: &Number<F>,
        lhs: &Number<F>,
        rhs: &Number<F>,
        modulus: &Number<F>,
        quotient: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let rem = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(modulus.limbs[3].clone()),
                Some(lhs.limbs[3].clone()),
                Some(rhs.limbs[3].clone()),
                Some(quotient.limbs[3].clone()),
                Some(rem.limbs[3].clone()),
                None,
            ],
            [
                None,
                None,
                None,
                None,
                Some(-F::one()),
                None,
                Some(-F::one()),
                Some(F::one()),
                None,
            ],
            0,
        )?[4].clone();
        Ok(rem)
    }

    pub fn mod_power108m1(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        number: &Number<F>,
    ) -> Result<[Limb<F>; 4], Error> {
        let value = number.limbs[0].value + number.limbs[1].value + number.limbs[2].value;
        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(number.limbs[0].clone()),
                Some(number.limbs[1].clone()),
                Some(number.limbs[2].clone()),
                None,
                Some(Limb::new(None, value)),
                None,
            ],
            [
                Some(F::one()),
                Some(F::one()),
                Some(F::one()),
                None,
                Some(-F::one()),
                None,
                None,
                None,
                None,
            ],
            0,
        )?;
        Ok(l.try_into().unwrap())
    }

    pub fn mod_power216(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        number: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let value = number.limbs[0].value + number.limbs[1].value * (F::from_u128(1u128 << 108));
        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(number.limbs[0].clone()),
                Some(number.limbs[1].clone()),
                None,
                None,
                Some(Limb::new(None, value)),
                None,
            ],
            [
                Some(F::one()),
                Some(F::from_u128(1u128 << 108)),
                None,
                None,
                Some(-F::one()),
                None,
                None,
                None,
                None,
            ],
            0,
        )?;
        Ok(l[2].clone())
    }

    pub fn mod_power108m1_mul(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let bn_modulus = BigUint::from((1u128 << 108) - 1);
        let [_, _, _, ml] = self.mod_power108m1(region, range_check_chip, offset, lhs)?; // ml has at most 110 bits
        let [_, _, _, mr] = self.mod_power108m1(region, range_check_chip, offset, rhs)?; // mr has at most 110 bits
        let v = ml.value * mr.value; // at most 220 bits
        let bn_q = field_to_bn(&v).div(bn_modulus.clone()); // at most 112 bits
        let bn_r = field_to_bn(&v) - bn_q.clone() * bn_modulus; // at most 108 bits
        let q = Limb::new(None, bn_to_field(&bn_q));
        let r = Limb::new(None, bn_to_field(&bn_r));
        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [Some(q), Some(ml), Some(mr), Some(r), None, None],
            [
                Some(F::from_u128((1u128 << 108) - 1)),
                None,
                None,
                Some(F::one()),
                None,
                None,
                None,
                Some(-F::one()),
                None,
            ],
            10,
        )?;
        Ok(l[3].clone())
    }

    ///
    /// # Apply constraint:
    /// (r     * 1    ) + (x0    * y0    * 1    ) + (v     * 1    ) = 0 \
    /// (ws[0] * cs[0]) + (ws[1] * ws[2] * cs[7]) + (ws[4] * cs[4]) = 0
    ///
    pub fn mod_power216_mul(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let x0 = lhs.limbs[0].value;
        let x1 = lhs.limbs[1].value;
        let y0 = rhs.limbs[0].value;
        let y1 = rhs.limbs[1].value;
        let mut v = x0 * y1 + x1 * y0; //0-2^216
        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(lhs.limbs[0].clone()), //x0
                Some(lhs.limbs[1].clone()), //x1
                Some(rhs.limbs[0].clone()), //y0
                Some(rhs.limbs[1].clone()), //y1
                Some(Limb::new(None, v)),
                None,
            ],
            [
                None,
                None,
                None,
                None,
                Some(-F::one()),
                None,
                Some(F::one()),
                Some(F::one()),
                None,
            ],
            0,
        )?;
        let vcell = l[4].clone();

        //  compute v mod 2^108
        let bn_q = field_to_bn(&v).div(BigUint::from(1u128 << 108));
        let bn_r = field_to_bn(&v) - bn_q.clone() * BigUint::from(1u128 << 108);
        let q = Limb::new(None, bn_to_field(&bn_q));
        let r = Limb::new(None, bn_to_field(&bn_r));

        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [Some(q), Some(vcell), None, Some(r), None, None],
            [
                Some(F::from_u128(1u128 << 108)),
                Some(-F::one()),
                None,
                Some(F::one()),
                None,
                None,
                None,
                None,
                None,
            ],
            10,
        )?;
        let rcell = l[2].clone();
        v = rcell.value * F::from_u128(1u128 << 108) + x0 * y0;

        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(rcell),
                Some(lhs.limbs[0].clone()),
                Some(rhs.limbs[0].clone()),
                None,
                Some(Limb::new(None, v)),
                None,
            ],
            [
                Some(F::from_u128(1u128 << 108)),
                None,
                None,
                None,
                Some(-F::one()),
                None,
                None,
                Some(F::one()),
                None,
            ],
            0, // TODO: need to check rcell range
        )?;
        Ok(l[3].clone())
    }

    pub fn mod_power108m1_zero(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        limbs: Vec<Limb<F>>,
        signs: Vec<F>,
    ) -> Result<(), Error> {
        let c = (1u128 << 108) - 1;
        let v = F::from_u128(c * 16u128)
            + limbs[0].value * signs[0]
            + limbs[1].value * signs[1]
            + limbs[2].value * signs[2];
        let q = field_to_bn(&v).div(c);
        self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(Limb::new(None, bn_to_field(&q))),
                Some(limbs[0].clone()),
                Some(limbs[1].clone()),
                Some(limbs[2].clone()),
                None,
                None,
            ],
            [
                Some(-F::from_u128(c)),
                Some(signs[0]),
                Some(signs[1]),
                Some(signs[2]),
                None,
                None,
                None,
                None,
                Some(F::from_u128(c * 16u128)),
            ],
            1, // check rcell range
        )?;
        Ok(())
    }

    ///
    /// # Apply constraint:
    /// (q * -c) + (sum(limb_i * sign_i)) + (c * BUFMULT)  = 0
    ///
    pub fn mod_power216_zero(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        limbs: Vec<Limb<F>>,
        signs: Vec<F>,
    ) -> Result<(), Error> {
        // BUFMULT = 2 may cause overflow
        const BUFMULT: u128 = 8u128; // as long as its > 2-bits wide.
        let f_c = F::from_u128(1u128 << 108) * F::from_u128(1u128 << 108);
        let f_cm = f_c * F::from_u128(BUFMULT);
        let v = (f_c * F::from_u128(BUFMULT))
            + limbs[0].value * signs[0]
            + limbs[1].value * signs[1]
            + limbs[2].value * signs[2];
        let q = field_to_bn(&v).div(field_to_bn(&f_c));
        self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(Limb::new(None, bn_to_field(&q))),
                Some(limbs[0].clone()),
                Some(limbs[1].clone()),
                Some(limbs[2].clone()),
                None,
                None,
            ],
            [
                Some(-f_c),
                Some(signs[0]),
                Some(signs[1]),
                Some(signs[2]),
                None,
                None,
                None,
                None,
                Some(f_cm),
            ],
            1, // check rcell range
        )?;
        Ok(())
    }

    // return 0 if not zero, 1 if zero for number
    pub fn number_is_zero(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        number: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let zero = F::zero();
        let three = F::from(3u64);
        // limb0_zero is 0 if not zero, 1 if zero
        let limb0_zero =
            self.config
                .eq_constant(region, range_check_chip, offset, &number.limbs[0], &zero)?;
        let limb1_zero =
            self.config
                .eq_constant(region, range_check_chip, offset, &number.limbs[1], &zero)?;
        let limb2_zero =
            self.config
                .eq_constant(region, range_check_chip, offset, &number.limbs[2], &zero)?;

        // all the above zero flat is either zero or one thus bounded
        // thus check all of them are 1 equals to check the sum of them are 3
        let sum: Limb<F> = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(limb0_zero.clone()),
                Some(limb1_zero.clone()),
                Some(limb2_zero.clone()),
                None,
                Some(Limb::new(
                    None,
                    limb0_zero.value + limb1_zero.value + limb2_zero.value,
                )),
                None,
            ],
            [
                Some(F::one()),
                Some(F::one()),
                Some(F::one()),
                None,
                Some(-F::one()),
                None,
                None,
                None,
                None,
            ],
            0,
        )?[3]
            .clone();
        let is_zero = self
            .config
            .eq_constant(region, range_check_chip, offset, &sum, &three)?;
        Ok(is_zero)
    }

    pub fn mod_mult(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
        modulus: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let one = self.assign_number(
            region,
            range_check_chip,
            offset,
            Number::from_bn(&BigUint::from(1u128)),
        )?;
        let zero = self.assign_number(
            region,
            range_check_chip,
            offset,
            Number::from_bn(&BigUint::from(0u128)),
        )?;
        let is_zero = self.number_is_zero(region, range_check_chip, offset, modulus)?;
        let modulus_mock: Number<F> =
            self.select(region, range_check_chip, offset, &is_zero, &modulus, &one)?;
        let r: Number<F> =
            self.mod_mult_unsafe(region, range_check_chip, offset, lhs, rhs, &modulus_mock)?;
        let res = self.select(region, range_check_chip, offset, &is_zero, &r, &zero)?;
        self.lt_number(region, range_check_chip, offset, &res, modulus)?;
        Ok(res)
    }

    pub fn mod_mult_unsafe(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
        modulus: &Number<F>,
    ) -> Result<Number<F>, Error> {
        /*
         * x0,x1,x2 * y0,y1,y2 = q0,q1,q2 * m0,m1,m2 + r0,r1,r2
         * mod 2^{108}-1:
         *     (x2+x1+x0)*(y0+y1+y2) = (q0+q1+q2)*(m0+m1+m2)+(r0+r1+r2)
         * mod 2^{216}:
         *     (x1*y0+x0*y1)*2^216+x0*y0 = (q0*m1+q1*m0)*2^{216}+q0*m0+r1+r0
         * native:
         *    x*y = q*m + r
         */

        // TODO: mod p first to avoid small p, k overflow
        // lhs % p assign_line constraint
        // rhs % p  assign_line constraint
        let bn_lhs = lhs.to_bn();
        let bn_rhs = rhs.to_bn();
        let bn_mult = bn_lhs.mul(bn_rhs);
        let bn_modulus = modulus.to_bn();
        let bn_quotient = bn_mult.clone().div(bn_modulus.clone()); //div_rem
        let bn_rem = bn_mult - (bn_quotient.clone() * bn_modulus.clone());
        let modulus = self.assign_number(
            region,
            range_check_chip,
            offset,
            Number::from_bn(&bn_modulus),
        )?;
        let rem = self.assign_number(region, range_check_chip, offset, Number::from_bn(&bn_rem))?;
        let quotient = self.assign_number(
            region,
            range_check_chip,
            offset,
            Number::from_bn(&bn_quotient),
        )?;
        let mod_108m1_lhs = self.mod_power108m1_mul(region, range_check_chip, offset, lhs, rhs)?;
        let mod_108m1_rhs =
            self.mod_power108m1_mul(region, range_check_chip, offset, &quotient, &modulus)?;
        let [r0, r1, r2, mod_108m1_rem] =
            self.mod_power108m1(region, range_check_chip, offset, &rem)?;
        self.mod_power108m1_zero(
            region,
            range_check_chip,
            offset,
            vec![
                mod_108m1_lhs.clone(),
                mod_108m1_rhs.clone(),
                mod_108m1_rem.clone(),
            ],
            vec![F::one(), -F::one(), -F::one()],
        )?;
        let mod_216_lhs = self.mod_power216_mul(region, range_check_chip, offset, lhs, rhs)?;
        let mod_216_rhs =
            self.mod_power216_mul(region, range_check_chip, offset, &quotient, &modulus)?;
        let mod_216_rem = self.mod_power216(region, range_check_chip, offset, &rem)?;

        self.mod_power216_zero(
            region,
            range_check_chip,
            offset,
            vec![mod_216_lhs, mod_216_rhs, mod_216_rem],
            vec![F::one(), -F::one(), -F::one()],
        )?;
        let mod_native = self.mod_native_mul(
            region,
            range_check_chip,
            offset,
            &rem,
            &lhs,
            &rhs,
            &modulus,
            &quotient
        )?;
        Ok(Number {
            limbs: [r0, r1, r2, mod_native],
        })
    }

    /// Selects result based on the condition cond = '1' or '0' \
    /// result = cond * base + (1-cond) * one
    ///
    pub fn select(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        cond: &Limb<F>,
        one: &Number<F>,
        base: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let mut limbs = vec![];
        for i in 0..4 {
            let l = self.config.select(
                region,
                range_check_chip,
                offset,
                cond,
                &one.limbs[i],
                &base.limbs[i],
                0,
            )?;
            limbs.push(l);
        }
        Ok(Number {
            limbs: limbs.try_into().unwrap(),
        })
    }

    pub fn mod_exp(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        base: &Number<F>,
        exp: &Number<F>,
        modulus: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let mut limbs = vec![];
        self.config.decompose_limb(
            region,
            range_check_chip,
            offset,
            &exp.limbs[2],
            &mut limbs,
            40,
        )?; //256 - 216 = 40
        self.config.decompose_limb(
            region,
            range_check_chip,
            offset,
            &exp.limbs[1],
            &mut limbs,
            108,
        )?;
        self.config.decompose_limb(
            region,
            range_check_chip,
            offset,
            &exp.limbs[0],
            &mut limbs,
            108,
        )?;
        let mut acc = self.assign_constant(
            region,
            range_check_chip,
            offset,
            Number::from_bn(&BigUint::from(1 as u128)),
            0,
        )?;
        let one = acc.clone();
        let window = 4;
        let mut selectors = vec![one, base.clone()];
        for _ in 2..(1<<window) {
            selectors.push(self.mod_mult(region, range_check_chip, offset, selectors.last().as_ref().unwrap(), &base, modulus)?);
        }
        selectors.reverse();
        assert_eq!(selectors.len(), 1<<window);
        for limb_group in limbs.chunks_exact(window) {
            let mut choice = selectors.clone();
            for i in 0..window {
                let bit = limb_group[i].clone();
                let (sh, sl) = choice.split_at(choice.len()/2);
                assert_eq!(sh.len(), sl.len());
                let mut next = vec![];
                for (h,l) in sh.into_iter().zip(sl) {
                    next.push(self.select(region, range_check_chip, offset, &bit, l, h)?);
                }
                choice = next;
            }
            assert_eq!(choice.len(), 1);
            let sval = choice[0].clone();
            for _ in 0..window {
                acc = self.mod_mult(region, range_check_chip, offset, &acc, &acc, modulus)?;
            }
            acc = self.mod_mult(region, range_check_chip, offset, &acc, &sval, modulus)?;
        }
        //println!("offset {} {}", offset, range_check_chip.offset());
        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use crate::circuits::range::{RangeCheckChip, RangeCheckConfig};
    use crate::circuits::CommonGateConfig;
    use crate::value_for_assign;
    use halo2_gate_generator::Limb;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr;
    use num_bigint::BigUint;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };

    use super::{ModExpChip, Number};

    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        limb: Column<Advice>,
    }

    #[derive(Clone, Debug)]
    pub struct HelperChip {
        config: HelperChipConfig,
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
            HelperChip { config }
        }

        fn configure(cs: &mut ConstraintSystem<Fr>) -> HelperChipConfig {
            let limb = cs.advice_column();
            cs.enable_equality(limb);
            HelperChipConfig { limb }
        }

        fn assign_base(
            &self,
            _region: &mut Region<Fr>,
            _offset: &mut usize,
            base: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(base))
        }

        fn assign_modulus(
            &self,
            _region: &mut Region<Fr>,
            _offset: &mut usize,
            modulus: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(modulus))
        }

        fn assign_exp(
            &self,
            _region: &mut Region<Fr>,
            _offset: &mut usize,
            exponent: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(exponent))
        }

        fn assign_results(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            result: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            let n = Number::from_bn(result);
            let mut cells = vec![];
            for i in 0..4 {
                let c = region.assign_advice(
                    || format!("assign input"),
                    self.config.limb,
                    *offset + i,
                    || value_for_assign!(n.limbs[i].value),
                )?;
                cells.push(Some(c));
                *offset = *offset + 1;
            }
            let n = Number {
                limbs: [
                    Limb::new(cells[0].clone(), n.limbs[0].value),
                    Limb::new(cells[1].clone(), n.limbs[1].value),
                    Limb::new(cells[2].clone(), n.limbs[2].value),
                    Limb::new(cells[3].clone(), n.limbs[3].value),
                ],
            };
            Ok(n)
        }
    }

    use num_bigint::RandomBits;
    use rand::{thread_rng, Rng};
    const LIMB_WIDTH: usize = 108;

    use std::ops::{Div, Mul};

    #[derive(Clone, Debug)]
    struct TestConfig {
        modexpconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
        rangecheckconfig: RangeCheckConfig,
    }

    #[derive(Clone, Debug, Default)]
    struct TestModpower108m1Circuit {
        a: BigUint,
        bn_test_res: BigUint,
    }

    impl Circuit<Fr> for TestModpower108m1Circuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let rangecheckconfig = RangeCheckChip::<Fr>::configure(meta);
            Self::Config {
                modexpconfig: ModExpChip::<Fr>::configure(meta, &rangecheckconfig),
                helperconfig: HelperChip::configure(meta),
                rangecheckconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            layouter.assign_region(
                || "mod_power108m1",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let a = helperchip.assign_base(&mut region, &mut offset, &self.a)?;
                    let result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let rem =
                        modexpchip.mod_power108m1(&mut region, &mut range_chip, &mut offset, &a)?;
                    println!("\nbn_res \t\t= 0x{}", &self.bn_test_res.to_str_radix(16));
                    println!("\nrem is (hex):");
                    for i in 0..4 {
                        println!("rem[{i}] \t\t= {:?}", &rem[i].value);
                    }
                    for i in 0..4 {
                        println!("result[{}] \t= {:?}", i, &result.limbs[i].value);
                        /* not equal since might overflow at most of 2 bits
                        region.constrain_equal(
                             rem[i].clone().cell.unwrap().cell(),
                             result.limbs[i].clone().cell.unwrap().cell()
                        )?;
                        */
                    }
                    Ok(rem)
                },
            )?;
            Ok(())
        }
    }

    #[derive(Clone, Debug, Default)]
    struct TestModpower108m1mulCircuit {
        a: BigUint,
        b: BigUint,
        bn_test_res: BigUint,
    }

    impl Circuit<Fr> for TestModpower108m1mulCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let rangecheckconfig = RangeCheckChip::<Fr>::configure(meta);
            Self::Config {
                modexpconfig: ModExpChip::<Fr>::configure(meta, &rangecheckconfig),
                helperconfig: HelperChip::configure(meta),
                rangecheckconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            layouter.assign_region(
                || "mod_power108m1_mul",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let _result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let lhs = helperchip.assign_modulus(&mut region, &mut offset, &self.a)?;
                    let rhs = helperchip.assign_base(&mut region, &mut offset, &self.b)?;
                    let res = modexpchip.mod_power108m1_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                    )?;
                    println!("\nbn_rem  \t= {:?}", &self.bn_test_res.to_str_radix(16));
                    println!("result is \t= {:?}", res.value);
                    Ok(res)
                },
            )?;
            Ok(())
        }
    }

    #[derive(Clone, Debug, Default)]
    struct TestModPower216MulCircuit {
        l: BigUint,
        r: BigUint,
        bn_test_res: BigUint,
    }

    impl Circuit<Fr> for TestModPower216MulCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let rangecheckconfig = RangeCheckChip::<Fr>::configure(meta);
            Self::Config {
                modexpconfig: ModExpChip::<Fr>::configure(meta, &rangecheckconfig),
                helperconfig: HelperChip::configure(meta),
                rangecheckconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            layouter.assign_region(
                || "test circuit mod_power216_mul",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let _result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let lhs = helperchip.assign_base(&mut region, &mut offset, &self.l)?;
                    let rhs = helperchip.assign_base(&mut region, &mut offset, &self.r)?;
                    let res = modexpchip.mod_power216_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                    )?;
                    println!("\nbn_rem \t= {}", &self.bn_test_res.to_str_radix(16));
                    println!("res \t= {:?}", res.value);
                    Ok(res)
                },
            )?;
            Ok(())
        }
    }

    #[derive(Clone, Debug, Default)]
    struct Test108m1v216Circuit {
        l: BigUint,
        r: BigUint,
        modulus: BigUint,
        quotient: BigUint,
        rem: BigUint,
    }

    impl Circuit<Fr> for Test108m1v216Circuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let rangecheckconfig: RangeCheckConfig = RangeCheckChip::<Fr>::configure(meta);
            Self::Config {
                modexpconfig: ModExpChip::<Fr>::configure(meta, &rangecheckconfig),
                helperconfig: HelperChip::configure(meta),
                rangecheckconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            layouter.assign_region(
                || "test circuit 108m1 vs 216",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let lhs = helperchip.assign_base(&mut region, &mut offset, &self.l)?;
                    let rhs = helperchip.assign_base(&mut region, &mut offset, &self.r)?;
                    let modulus =
                        helperchip.assign_modulus(&mut region, &mut offset, &self.modulus)?;
                    let quo = helperchip.assign_base(&mut region, &mut offset, &self.quotient)?;
                    let rem = helperchip.assign_base(&mut region, &mut offset, &self.rem)?;
                    let rl_mod_108m1 = modexpchip.mod_power108m1_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                    )?;
                    let qm_mod_108m1 = modexpchip.mod_power108m1_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &quo,
                        &modulus,
                    )?;
                    let [_r0, _r1, _r2, rem_mod_108m1] = modexpchip.mod_power108m1(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &rem,
                    )?;
                    let lr_mod_216 = modexpchip.mod_power216_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                    )?;
                    let qm_mod_216 = modexpchip.mod_power216_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &quo,
                        &modulus,
                    )?;
                    let rem_mod_216: Limb<Fr> =
                        modexpchip.mod_power216(&mut region, &mut range_chip, &mut offset, &rem)?;
                    println!(
                        "rl_mod_108m1  {:?} = {:?} lr_mod_216",
                        rl_mod_108m1.value, lr_mod_216.value
                    );
                    println!(
                        "qm_mod_108m1  {:?} = {:?} qm_mod_216",
                        qm_mod_108m1.value, qm_mod_216.value
                    );
                    println!(
                        "rem_mod_108m1 {:?} = {:?} mod_216_rem",
                        rem_mod_108m1.value, rem_mod_216.value
                    );
                    println!("");
                    region.constrain_equal(
                        rl_mod_108m1.clone().cell.unwrap().cell(),
                        lr_mod_216.clone().cell.unwrap().cell(),
                    )?;
                    region.constrain_equal(
                        qm_mod_108m1.clone().cell.unwrap().cell(),
                        qm_mod_216.clone().cell.unwrap().cell(),
                    )?;
                    region.constrain_equal(
                        rem_mod_108m1.clone().cell.unwrap().cell(),
                        rem_mod_216.clone().cell.unwrap().cell(),
                    )?;
                    Ok(rem)
                },
            )?;
            Ok(())
        }
    }

    #[derive(Clone, Debug, Default)]
    struct TestModMultCircuit {
        l: BigUint,
        r: BigUint,
        modulus: BigUint,
        bn_test_res: BigUint,
    }

    impl Circuit<Fr> for TestModMultCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let rangecheckconfig = RangeCheckChip::<Fr>::configure(meta);
            Self::Config {
                modexpconfig: ModExpChip::<Fr>::configure(meta, &rangecheckconfig),
                helperconfig: HelperChip::configure(meta),
                rangecheckconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            layouter.assign_region(
                || "test circuit mod_mult",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let modulus =
                        helperchip.assign_modulus(&mut region, &mut offset, &self.modulus)?;
                    let lhs = helperchip.assign_base(&mut region, &mut offset, &self.l)?;
                    let rhs = helperchip.assign_base(&mut region, &mut offset, &self.r)?;
                    let rem = modexpchip.mod_mult(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                        &modulus,
                    )?;
                    for i in 0..4 {
                        println!(
                            "rem is {:?}, result is {:?}",
                            &rem.limbs[i].value, &result.limbs[i].value
                        );
                        println!(
                            "remcell is {:?}, resultcell is {:?}",
                            &rem.limbs[i].cell.as_ref().unwrap().value(), &result.limbs[i].cell.as_ref().unwrap().value()
                        );
                        region.constrain_equal(
                            rem.limbs[i].clone().cell.unwrap().cell(),
                            result.limbs[i].clone().cell.unwrap().cell(),
                        )?;
                    }
                    Ok(rem)
                },
            )?;
            Ok(())
        }
    }

    #[derive(Clone, Debug, Default)]
    struct TestModExpCircuit {
        base: BigUint,
        exp: BigUint,
        modulus: BigUint,
        bn_test_res: BigUint,
    }

    impl Circuit<Fr> for TestModExpCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let rangecheckconfig = RangeCheckChip::<Fr>::configure(meta);
            Self::Config {
                modexpconfig: ModExpChip::<Fr>::configure(meta, &rangecheckconfig),
                helperconfig: HelperChip::configure(meta),
                rangecheckconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            layouter.assign_region(
                || "assign mod exp",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let base = helperchip.assign_base(&mut region, &mut offset, &self.base)?;
                    let exp = helperchip.assign_exp(&mut region, &mut offset, &self.exp)?;
                    let modulus =
                        helperchip.assign_modulus(&mut region, &mut offset, &self.modulus)?;
                    let result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let rem = modexpchip.mod_exp(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &base,
                        &exp,
                        &modulus,
                    )?;
                    for i in 0..4 {
                        // println!("rem is {:?}, \t result is {:?}", &rem.limbs[i].value, &result.limbs[i].value);
                        // println!("remcell is \t{:?}", &rem.limbs[i].cell);
                        // println!("resultcell is \t {:?}", &result.limbs[i].cell);
                        region.constrain_equal(
                            rem.limbs[i].clone().cell.unwrap().cell(),
                            result.limbs[i].clone().cell.unwrap().cell(),
                        )?;
                    }
                    // println!("offset final {}", offset);
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    fn run_mod_power108m1_circuit() -> Result<(), CircuitError> {
        // Create an a set of test vectors varying in bit lengths.
        // Test will pass if:
        //  (1) result returned from circuit constrain_equal() to the
        //      assigned result from bn calculation.
        //  (2) prover.verify() for each run verifies without error.
        let mut bn_test_vectors: Vec<BigUint> = Vec::with_capacity(8);
        let bit_len: [usize; 8] = [
            0,
            1,
            LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + 108,
            LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH + 108,
        ];
        for i in 0..8 {
            bn_test_vectors.push(get_random_x_bit_bn(bit_len[i]));
        }
        for testcase in bn_test_vectors {
            let (a_l2, a_l1, a_l0) = get_limbs_from_bn(&testcase);
            let bn_l210sum = &a_l2 + &a_l1 + &a_l0;
            let bn_test_res = bn_l210sum;
            let a = testcase.clone();
            let test_circuit = TestModpower108m1Circuit { a, bn_test_res };
            let prover = match MockProver::run(16, &test_circuit, vec![]) {
                Ok(prover_run) => prover_run,
                Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
            };
            match prover.verify() {
                Ok(_) => (),
                Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
            };
        }
        Ok(())
    }

    fn run_mod_power108m1_mul_circuit() -> Result<(), CircuitError> {
        let a = get_random_x_bit_bn(LIMB_WIDTH + 42);
        let b = get_random_x_bit_bn(47);
        let modulus = BigUint::parse_bytes(b"fffffffffffffffffffffffffff", 16).unwrap();

        let bn_test_res = (a.clone() * b.clone()) % modulus;
        let test_circuit = TestModpower108m1mulCircuit { a, b, bn_test_res };
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };
        Ok(())
    }

    fn run_mod_power216_mul_circuit() -> Result<(), CircuitError> {
        let l = get_random_x_bit_bn(LIMB_WIDTH + LIMB_WIDTH + 42);
        let r = get_random_x_bit_bn(LIMB_WIDTH - 47);
        let modulus = get_random_x_bit_bn(16);
        let bn_test_res = (l.clone() * r.clone()) % modulus;
        let test_circuit = TestModPower216MulCircuit { l, r, bn_test_res };
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };

        let l = BigUint::parse_bytes(b"fffffffffffffffffffffffffff", 16).unwrap();
        let r = BigUint::from(1u128);
        let modulus = BigUint::from(1u128 << 108) * BigUint::from(1u128 << 108);
        let bn_test_res = (l.clone() * r.clone()) % modulus;
        let test_circuit = TestModPower216MulCircuit { l, r, bn_test_res };
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };

        Ok(())
    }

    fn run_mod_power108m1_vs_216_circuits() -> Result<(), CircuitError> {
        // product of l and r cannot exceed LIMB_WIDTH bits or mod 108m1 != mod 216.
        // generate a random number up to L_BITLENGTH to use as the seed for the l bit length.
        // i.e., l (1-80-bits) * r (LIMB_WIDTH - (1-80-bits)) < (2^108)-1)
        const L_BITLENGTH: usize = 80;
        let mut rng = rand::thread_rng();
        let (l, r) = get_random_product_not_exceed_n_bits(rng.gen_range(1..=L_BITLENGTH));
        let modulus = get_random_x_bit_bn(32);
        let mult = l.clone().mul(r.clone());
        let quotient = mult.clone().div(modulus.clone());
        let rem = mult - (quotient.clone() * modulus.clone());
        let test_circuit = Test108m1v216Circuit {
            l,
            r,
            modulus,
            quotient,
            rem,
        };
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };
        Ok(())
    }

    fn run_mod_mult_circuit() -> Result<(), CircuitError> {
        const NUM_TESTS: usize = 6;
        let mut bn_lhs_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_rhs_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_modulus_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let bit_len_l: [usize; NUM_TESTS] = [
            1,
            4,
            8,
            LIMB_WIDTH - 1,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH + 1,
        ];
        let bit_len_r: [usize; NUM_TESTS] = [
            1,
            4,
            8,
            LIMB_WIDTH - 1,
            LIMB_WIDTH + 36,
            LIMB_WIDTH + LIMB_WIDTH + 10,
        ]; // + 12 will error
        let bit_len_m: [usize; NUM_TESTS] = [1, 4, 8, 12, 16, 20];

        for i in 0..NUM_TESTS {
            bn_lhs_test_vectors.push(get_random_x_bit_bn(bit_len_l[i]));
            bn_rhs_test_vectors.push(get_random_x_bit_bn(bit_len_r[i]));
            bn_modulus_test_vectors.push(get_random_x_bit_bn(bit_len_m[i]));
        }
        for i in 0..NUM_TESTS {
            let lhs_testcase = bn_lhs_test_vectors[i].clone();
            let rhs_testcase = bn_rhs_test_vectors[i].clone();
            let modulus_testcase = bn_modulus_test_vectors[i].clone();

            let bn_test_res =
                (lhs_testcase.clone() * rhs_testcase.clone()) % modulus_testcase.clone();
            println!(
                "testcase: (0x{})*(0x{}) mod 0x{} = 0x{}",
                lhs_testcase.clone().to_str_radix(16),
                rhs_testcase.clone().to_str_radix(16),
                modulus_testcase.clone().to_str_radix(16),
                bn_test_res.to_str_radix(16)
            );

            let l = lhs_testcase.clone();
            let r = rhs_testcase.clone();
            let modulus = modulus_testcase.clone();
            let test_circuit = TestModMultCircuit {
                l,
                r,
                modulus,
                bn_test_res,
            };
            let prover = match MockProver::run(16, &test_circuit, vec![]) {
                Ok(prover) => prover,
                Err(e) => panic!("{:#?}", e),
            };
            match prover.verify() {
                Ok(_) => (),
                Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
            };
        }
        Ok(())
    }

    fn run_mod_mult_circuit_zero_modulus() -> Result<(), CircuitError> {
        const NUM_TESTS: usize = 6;
        let mut bn_lhs_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_rhs_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let bit_len_l: [usize; NUM_TESTS] = [
            1,
            4,
            8,
            LIMB_WIDTH - 1,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH + 1,
        ];
        let bit_len_r: [usize; NUM_TESTS] = [
            1,
            4,
            8,
            LIMB_WIDTH - 1,
            LIMB_WIDTH + 36,
            LIMB_WIDTH + LIMB_WIDTH + 10,
        ]; // + 12 will error

        for i in 0..NUM_TESTS {
            bn_lhs_test_vectors.push(get_random_x_bit_bn(bit_len_l[i]));
            bn_rhs_test_vectors.push(get_random_x_bit_bn(bit_len_r[i]));
        }
        for i in 0..NUM_TESTS {
            let lhs_testcase = bn_lhs_test_vectors[i].clone();
            let rhs_testcase = bn_rhs_test_vectors[i].clone();

            let bn_test_res = BigUint::from(0u128);
            println!(
                "testcase: (0x{})*(0x{}) mod 0 = 0x{}",
                lhs_testcase.clone().to_str_radix(16),
                rhs_testcase.clone().to_str_radix(16),
                bn_test_res.to_str_radix(16)
            );

            let l = lhs_testcase.clone();
            let r = rhs_testcase.clone();
            let modulus = BigUint::from(0u128);

            let test_circuit = TestModMultCircuit {
                l,
                r,
                modulus,
                bn_test_res,
            };
            let prover = match MockProver::run(16, &test_circuit, vec![]) {
                Ok(prover) => prover,
                Err(e) => panic!("{:#?}", e),
            };
            match prover.verify() {
                Ok(_) => (),
                Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
            };
        }
        Ok(())
    }

    fn run_modexp_circuit() -> Result<(), CircuitError> {
        // Create an a set of test vectors varying in bit lengths for base, exp & modulus.
        // Test will pass if:
        //  (1) result returned from circuit constrain_equal() to the
        //      assigned result from bn calculation.
        //  (2) prover.verify() for each run verifies without error.
        const NUM_TESTS: usize = 5;
        let mut bn_base_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_modulus_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_exp_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let bit_len_b: [usize; NUM_TESTS] = [1, 4, 8, 250, 255];
        let bit_len_m: [usize; NUM_TESTS] = [1, 4, 8, 255, 254];
        let bit_len_e: [usize; NUM_TESTS] = [
            //change for larger exp bit length.
            1,
            LIMB_WIDTH - 1,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH - 1,
            LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH - 90, // max before overflow (need to check range)
        ];
        for i in 0..NUM_TESTS {
            bn_base_test_vectors.push(get_random_x_bit_bn(bit_len_b[i]));
            bn_modulus_test_vectors.push(get_random_x_bit_bn(bit_len_m[i]));
            bn_exp_test_vectors.push(get_random_x_bit_bn(bit_len_e[i]));
        }
        for i in 0..NUM_TESTS {
            let base_testcase = bn_base_test_vectors[i].clone();
            let modulus_testcase = bn_modulus_test_vectors[i].clone();
            let exp_testcase = bn_exp_test_vectors[i].clone();
            //let bn_test_res = big_pow(base_testcase.clone(), exp_testcase.clone()) % modulus_testcase.clone();
            let bn_test_res = base_testcase
                .clone()
                .modpow(&exp_testcase, &modulus_testcase);
            println!(
                "testcase: (0x{})^(0x{}) mod 0x{} = 0x{}",
                base_testcase.clone().to_str_radix(16),
                exp_testcase.clone().to_str_radix(16),
                modulus_testcase.clone().to_str_radix(16),
                bn_test_res.to_str_radix(16)
            );
            let base = base_testcase.clone();
            let exp = exp_testcase.clone();
            let modulus = modulus_testcase.clone();
            let test_circuit = TestModExpCircuit {
                base,
                exp,
                modulus,
                bn_test_res,
            };
            let prover = match MockProver::run(16, &test_circuit, vec![]) {
                Ok(prover_run) => prover_run,
                Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
            };
            match prover.verify() {
                Ok(_) => (),
                Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
            };
        }
        Ok(())
    }

    fn run_modexp_zero_modulus_circuit() -> Result<(), CircuitError> {
        // Create an a set of test vectors varying in bit lengths for base, exp & modulus.
        // Test will pass if:
        //  (1) result returned from circuit constrain_equal() to the
        //      assigned result from bn calculation.
        //  (2) prover.verify() for each run verifies without error.
        const NUM_TESTS: usize = 5;
        let mut bn_base_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_exp_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let bit_len_b: [usize; NUM_TESTS] = [1, 4, 8, 10, 16];
        let bit_len_e: [usize; NUM_TESTS] = [
            //change for larger exp bit length.
            1,
            LIMB_WIDTH - 1,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH - 1,
            LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH - 90, // max before overflow (need to check range)
        ];
        for i in 0..NUM_TESTS {
            bn_base_test_vectors.push(get_random_x_bit_bn(bit_len_b[i]));
            bn_exp_test_vectors.push(get_random_x_bit_bn(bit_len_e[i]));
        }
        for i in 0..NUM_TESTS {
            let base_testcase: BigUint = bn_base_test_vectors[i].clone();
            let exp_testcase = bn_exp_test_vectors[i].clone();
            //let bn_test_res = big_pow(base_testcase.clone(), exp_testcase.clone()) % modulus_testcase.clone();
            let bn_test_res = BigUint::from(0u128);
            println!(
                "testcase: (0x{})^(0x{}) mod 0 = 0x{}",
                base_testcase.clone().to_str_radix(16),
                exp_testcase.clone().to_str_radix(16),
                bn_test_res.to_str_radix(16)
            );
            let base = base_testcase.clone();
            let exp = exp_testcase.clone();
            let modulus = BigUint::from(0u128);

            let test_circuit = TestModExpCircuit {
                base,
                exp,
                modulus,
                bn_test_res,
            };
            let prover = match MockProver::run(16, &test_circuit, vec![]) {
                Ok(prover_run) => prover_run,
                Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
            };
            match prover.verify() {
                Ok(_) => (),
                Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
            };
        }
        Ok(())
    }


    fn run_modexp_small_p_circuit() -> Result<(), CircuitError> {
        // Create an a set of test vectors varying in bit lengths for base, exp & modulus.
        // Test will pass if:
        //  (1) result returned from circuit constrain_equal() to the
        //      assigned result from bn calculation.
        //  (2) prover.verify() for each run verifies without error.
        const NUM_TESTS: usize = 1;
        let mut bn_base_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_modulus_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_exp_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        for _ in 0..NUM_TESTS {
            let u256_from_str = BigUint::parse_bytes("efffffffffffffffffffffffffffffee".as_bytes(), 16).unwrap();
            bn_base_test_vectors.push(u256_from_str);
            bn_modulus_test_vectors.push(BigUint::from(2u64));
            bn_exp_test_vectors.push(BigUint::from(3u64));
        }
        for i in 0..NUM_TESTS {
            let base_testcase = bn_base_test_vectors[i].clone();
            let modulus_testcase = bn_modulus_test_vectors[i].clone();
            println!("modulus_testcase is {}", modulus_testcase);

            let exp_testcase = bn_exp_test_vectors[i].clone();
            //let bn_test_res = big_pow(base_testcase.clone(), exp_testcase.clone()) % modulus_testcase.clone();
            let bn_test_res = base_testcase
                .clone()
                .modpow(&exp_testcase, &modulus_testcase);
            println!(
                "testcase: (0x{})^(0x{}) mod 0x{} = 0x{}",
                base_testcase.clone().to_str_radix(16),
                exp_testcase.clone().to_str_radix(16),
                modulus_testcase.clone().to_str_radix(16),
                bn_test_res.to_str_radix(16)
            );
            let base = base_testcase.clone();
            let exp = exp_testcase.clone();
            let modulus = modulus_testcase.clone();
            let test_circuit = TestModExpCircuit {
                base,
                exp,
                modulus,
                bn_test_res,
            };
            let prover = match MockProver::run(16, &test_circuit, vec![]) {
                Ok(prover_run) => prover_run,
                Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
            };
            match prover.verify() {
                Ok(_) => (),
                Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
            };
        }
        Ok(())
    }

    #[test]
    fn test_mod_power108m1_only() {
        let output =
            run_mod_power108m1_circuit().expect("\nmod_power108m1_circuit failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_mod_power108m1_zero_only() {
        let output =
            run_mod_power108m1_circuit().expect("\nmod_power108m1_circuit failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_mod_power108m1_mul() {
        let output =
            run_mod_power108m1_mul_circuit().expect("\nmod_power108m1_mul failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_mod_power216_mul() {
        let output =
            run_mod_power216_mul_circuit().expect("\nmod_mult_circuit failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_mod_108m1_vs_216() {
        let output = run_mod_power108m1_vs_216_circuits()
            .expect("\nmod_108m1_vs_216_circuit failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_mod_mult() {
        let output = run_mod_mult_circuit().expect("\nmod_mult_circuit failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_mod_mult_zero_modulus() {
        let output =
            run_mod_mult_circuit_zero_modulus().expect("\nmod_mult_circuit failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_modexp() {
        let output = run_modexp_circuit().expect("\nmodexp_circuit failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_modexp_zero_modulus() {
        let output =
            run_modexp_zero_modulus_circuit().expect("\nmodexp_circuit failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_modexp_small_p() {
        let output = run_modexp_small_p_circuit().expect("\nmodexp_circuit failed prover verify");
        println!("\nproof generation successful!\nresult: {:#?}", output);
    }

    // test helpers:
    use halo2_proofs::dev::VerifyFailure;
    use std::fmt;

    pub enum CircuitError {
        /// Thrown when `MockProver::run` fails to prove the circuit.
        ProverError(Error),
        /// Thrown when verification fails.
        VerifierError(Vec<VerifyFailure>),
    }

    impl fmt::Debug for CircuitError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                CircuitError::ProverError(prover_error) => {
                    write!(f, "prover error in circuit: {}", prover_error)
                }
                CircuitError::VerifierError(verifier_error) => {
                    write!(f, "verifier error in circuit: {:#?}", verifier_error)
                }
            }
        }
    }

    /// # bn_limbs from BigUint
    /// Extracts BigUint to tuple of limbs \
    /// BigUint -> (l2,l1,l0)
    ///
    fn get_limbs_from_bn(bn: &BigUint) -> (BigUint, BigUint, BigUint) {
        let limb0 = bn.modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
        let limb1 = ((bn - limb0.clone()) / BigUint::from(1u128 << 108))
            .modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
        let limb2 = (bn / BigUint::from(1u128 << 108)) / (BigUint::from(1u128 << 108));
        (limb2, limb1, limb0)
    }

    /// # random BigUint x-bits long
    /// returns a BigUint with bit length = bit_length
    fn get_random_x_bit_bn(bit_length: usize) -> BigUint {
        let mut rng = thread_rng();
        let mut b = BigUint::default();
        while b.bits() != bit_length as u64 {
            b = rng.sample(RandomBits::new(bit_length as u64));
        }
        b
    }

    /// # Returns two BigUint values whose product does not exceed LIMB_WIDTH bits.
    fn get_random_product_not_exceed_n_bits(n: usize) -> (BigUint, BigUint) {
        let vmax = BigUint::parse_bytes(b"fffffffffffffffffffffffffff", 16).unwrap();
        let b1 = get_random_x_bit_bn(n);
        let max_bits = LIMB_WIDTH - b1.bits() as usize;
        let mut b2 = vmax.clone();
        while (b2.clone() * b1.clone()) > vmax {
            b2 = get_random_x_bit_bn(max_bits);
        }
        (b1, b2)
    }
}
