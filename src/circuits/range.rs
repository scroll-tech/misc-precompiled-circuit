use crate::utils::{
    field_to_bn,
    bn_to_field,
};
use halo2_gate_generator::{
    customized_circuits,
    table_item,
    item_count,
    customized_circuits_expand,
    constant_from,
    value_for_assign,
    GateCell,
    Limb,
};
use crate::circuits::{
    LookupAssistConfig,
    LookupAssistChip
};
use std::ops::Div;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
    poly::Rotation,
};
use std::marker::PhantomData;
use num_bigint::BigUint;

/*
 * Customized gates range_check(target) with each limb less than 2^12
 * acc will be the sum of the target limbs and rem is the remaining limbs
 * of the target value.
 */
customized_circuits!(RangeCheckConfig, 2, 3, 2, 0,
   | limb   |  acc   | rem   | table | sel
   | nil    |  acc_n | rem_n | nil   | sel_n
);

impl LookupAssistConfig for RangeCheckConfig {
    /// register a column (col) to be range checked by limb size (sz)
    fn register<F: FieldExt> (
        &self,
        cs: &mut ConstraintSystem<F>,
        col: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
        sz: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
    ) {
        cs.lookup_any("check ranges", |meta| {
            let acc = self.get_expr(meta, RangeCheckConfig::acc());
            let rem = self.get_expr(meta, RangeCheckConfig::rem());
            vec![(col(meta), acc), (sz(meta), rem)]
        });
    }
}

pub struct RangeCheckChip<F:FieldExt> {
    config: RangeCheckConfig,
    offset: usize,
    _marker: PhantomData<F>
}

impl<F:FieldExt> LookupAssistChip<F> for RangeCheckChip<F> {
    fn provide_lookup_evidence (
        &mut self,
        region: &mut Region<F>,
        value: F,
        sz: u64,
    ) -> Result<(), Error> {
        self.assign_value_with_range(region, value, sz)
    }
}


impl<F: FieldExt> RangeCheckChip<F> {
    pub fn new(config: RangeCheckConfig) -> Self {
        RangeCheckChip {
            config,
            offset:0,
            _marker: PhantomData,
        }
    }

    pub fn offset(&mut self) -> usize {
        self.offset
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> RangeCheckConfig {
        let witness= [0; 3]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 2].map(|_| cs.fixed_column());
        let selector =[];

        let config = RangeCheckConfig { fixed, selector, witness };

        // Range Check of all limbs
        //
        cs.lookup_any("within ranges", |meta| {
            let limb = config.get_expr(meta, RangeCheckConfig::limb());
            let table = config.get_expr(meta, RangeCheckConfig::table());
            vec![(limb, table)]
        });

        // First we require the rem is continus if it is not zero
        cs.create_gate("range check constraint", |meta| {
            let rem = config.get_expr(meta, RangeCheckConfig::rem());
            let rem_n = config.get_expr(meta, RangeCheckConfig::rem_n());
            let sel = config.get_expr(meta, RangeCheckConfig::sel());

            vec![
                sel * rem.clone() * (rem - rem_n - constant_from!(1)),
            ]

        });

        // Second we make sure if the rem is not zero then
        // carry = carry_n * 2^12 + limb
        cs.create_gate("limb acc constraint", |meta| {
            let limb = config.get_expr(meta, RangeCheckConfig::limb());
            let acc = config.get_expr(meta, RangeCheckConfig::acc());
            let acc_n = config.get_expr(meta, RangeCheckConfig::acc_n());
            let sel = config.get_expr(meta, RangeCheckConfig::sel());
            let sel_n = config.get_expr(meta, RangeCheckConfig::sel_n());

            vec![
                sel.clone() * (acc.clone() - limb - acc_n * constant_from!(1u64<<12) * sel_n),
                sel.clone() * (constant_from!(1) - sel.clone()),
                //(constant_from!(1) - sel) * acc, // if sel is 0 then acc must equal to 0
            ]

        });
        cs.create_gate("end with zero", |meta| {
            let sel = config.get_expr(meta, RangeCheckConfig::sel());
            let acc_n = config.get_expr(meta, RangeCheckConfig::acc_n());
            let sel_n = config.get_expr(meta, RangeCheckConfig::sel_n());
            vec![
                sel * acc_n * (constant_from!(1) - sel_n), // if sel is 0 then acc must equal to 0
            ]
        });

        config
    }

    /// Make sure the (value, sz) pair is lookupable in the range_chip
    pub fn assign_value_with_range (
        &mut self,
        region: &mut Region<F>,
        value: F,
        sz: u64,
    ) -> Result<(), Error> {
        let mut limbs = vec![];
        let mut bn = field_to_bn(&value);
        let mut cs = vec![];
        for _ in 0..sz {
            cs.push(bn_to_field(&bn));
            let limb = bn.modpow(&BigUint::from(1u128), &BigUint::from(1u128<<12));
            bn = (bn - limb.clone()).div(BigUint::from(1u128<<12));
            limbs.push(bn_to_field(&limb));
        }
        cs.reverse();
        limbs.reverse();
        for i in 0..sz {
            let limb = limbs.pop().unwrap();
            let acc = cs.pop().unwrap();
            self.config.assign_cell(region, self.offset, &RangeCheckConfig::limb(), limb)?;
            self.config.assign_cell(region, self.offset, &RangeCheckConfig::acc(), acc)?;
            self.config.assign_cell(region, self.offset, &RangeCheckConfig::rem(), F::from_u128((sz-i) as u128))?;
            self.config.assign_cell(region, self.offset, &RangeCheckConfig::sel(), F::one())?;
            self.offset += 1;
        }
        self.config.assign_cell(region, self.offset, &RangeCheckConfig::limb(), F::zero())?;
        self.config.assign_cell(region, self.offset, &RangeCheckConfig::acc(), F::zero())?;
        self.config.assign_cell(region, self.offset, &RangeCheckConfig::rem(), F::zero())?;
        self.config.assign_cell(region, self.offset, &RangeCheckConfig::sel(), F::zero())?;
        self.offset += 1;
        Ok(())
    }

    /// initialize the table column from 1 to 2^12
    /// initialize needs to be called before using the range_chip
    pub fn initialize(
        &mut self,
        region: &mut Region<F>,
    ) -> Result<(), Error> {
        for i in 0..4096 {
            self.config.assign_cell(region, i, &RangeCheckConfig::table(), F::from_u128(i as u128))?;
        }
        self.offset = 0;
        self.assign_value_with_range(region, F::zero(), 25)?;
        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::dev::MockProver;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner, AssignedCell},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error, VirtualCells,
            Expression
        },
        poly::Rotation,
    };

    use super::{
        RangeCheckChip,
        RangeCheckConfig,
    };
    use crate::value_for_assign;
    use crate::circuits::LookupAssistConfig;


    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        limb: Column<Advice>
    }

    impl HelperChipConfig {
        pub fn range_check_column (&self, cs: &mut VirtualCells<Fr>) -> Expression<Fr> {
            cs.query_advice(self.limb, Rotation::cur())
        }
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
            let limb = cs.advice_column();
            cs.enable_equality(limb);
            HelperChipConfig {
                limb,
            }
        }

        fn assign_value(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            value: Fr,
        ) -> Result<AssignedCell<Fr, Fr>, Error> {
            let c = region.assign_advice(
                || format!("assign input"),
                self.config.limb,
                *offset,
                || value_for_assign!(value)
            )?;
            *offset = *offset + 1;
            Ok(c)
        }

    }

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {
    }

    #[derive(Clone, Debug)]
    struct TestConfig {
        rangecheckconfig: RangeCheckConfig,
        helperconfig: HelperChipConfig,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let rangecheckconfig = RangeCheckChip::<Fr>::configure(meta);
            let helperconfig = HelperChip::configure(meta);

            rangecheckconfig.register(
                meta,
                |c| helperconfig.range_check_column(c),
                |_| Expression::Constant(Fr::from(4 as u64))
            );

            Self::Config {
               rangecheckconfig,
               helperconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            let helper_chip = HelperChip::new(config.clone().helperconfig);
            layouter.assign_region(
                || "range check test",
                |mut region| {
                    let v = Fr::from(1u64<<24 + 1);
                    range_chip.initialize(&mut region)?;
                    range_chip.assign_value_with_range(&mut region, v, 4)?;

                    // assign helper
                    let mut offset = 0;
                    helper_chip.assign_value(&mut region, &mut offset, v)?;
                    Ok(())
                }
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_range_circuit() {
        let test_circuit = TestCircuit {} ;
        let prover = MockProver::run(18, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
