use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::AssignedCell;
use num_bigint::BigUint;

pub fn field_to_bn<F: FieldExt>(f: &F) -> BigUint {
    let bytes = f.to_repr();
    // to_repr is little-endian as per the test below.
    BigUint::from_bytes_le(bytes.as_ref())
}

pub fn bn_to_field<F: FieldExt>(bn: &BigUint) -> F {
    let mut bytes = bn.to_bytes_le();
    bytes.resize(64, 0);
    F::from_bytes_wide(&bytes.try_into().unwrap())
}

pub fn field_to_u32<F: FieldExt>(f: &F) -> u32 {
    f.get_lower_32()
}

pub fn field_to_u64<F: FieldExt>(f: &F) -> u64 {
    let bytes = f.get_lower_128().to_le_bytes();
    u64::from_le_bytes(bytes[0..8].try_into().unwrap())
}

pub fn u32_to_limbs<F: FieldExt>(v: u32) -> [F; 4] {
    let mut rem = v;
    let mut r = vec![];
    for _ in 0..4 {
        r.append(&mut vec![F::from((rem % 256) as u64)]);
        rem = rem / 256;
    }
    r.try_into().unwrap()
}

/* FIXME should not get value based on cell in new halo2 */
pub fn cell_to_value<F: FieldExt>(cell: &AssignedCell<F, F>) -> F {
    //cell.value().map_or(0, |x| field_to_u32(x))
    let mut r = F::zero();
    cell.value().map(|x| r = *x);
    r
}

/* FIXME should not get value based on cell in new halo2 */
pub fn cell_to_u32<F: FieldExt>(cell: &AssignedCell<F, F>) -> u32 {
    //cell.value().map_or(0, |x| field_to_u32(x))
    let mut r = 0;
    cell.value().map(|x| r = field_to_u32(x));
    r
}

pub fn cell_to_limbs<F: FieldExt>(cell: &AssignedCell<F, F>) -> [F; 4] {
    let a = cell_to_u32(cell);
    u32_to_limbs(a)
}

#[macro_export]
macro_rules! curr {
    ($meta: expr, $x: expr) => {
        $meta.query_advice($x, halo2_proofs::poly::Rotation::cur())
    };
}

#[macro_export]
macro_rules! prev {
    ($meta: expr, $x: expr) => {
        $meta.query_advice($x, halo2_proofs::poly::Rotation::prev())
    };
}

#[macro_export]
macro_rules! next {
    ($meta: expr, $x: expr) => {
        $meta.query_advice($x, halo2_proofs::poly::Rotation::next())
    };
}

#[macro_export]
macro_rules! nextn {
    ($meta: expr, $x: expr, $n:expr) => {
        $meta.query_advice($x, halo2_proofs::poly::Rotation($n))
    };
}

#[macro_export]
macro_rules! fixed_curr {
    ($meta: expr, $x: expr) => {
        $meta.query_fixed($x, halo2_proofs::poly::Rotation::cur())
    };
}

#[macro_export]
macro_rules! instance_curr {
    ($meta: expr, $x: expr) => {
        $meta.query_instance($x, halo2_proofs::poly::Rotation::cur())
    };
}

#[macro_export]
macro_rules! fixed_prev {
    ($meta: expr, $x: expr) => {
        $meta.query_fixed($x, halo2_proofs::poly::Rotation::prev())
    };
}

#[macro_export]
macro_rules! fixed_next {
    ($meta: expr, $x: expr) => {
        $meta.query_fixed($x, halo2_proofs::poly::Rotation::next())
    };
}

#[macro_export]
macro_rules! constant_from {
    ($x: expr) => {
        halo2_proofs::plonk::Expression::Constant(F::from($x as u64))
    };
}

#[macro_export]
macro_rules! constant_from_bn {
    ($x: expr) => {
        halo2_proofs::plonk::Expression::Constant(bn_to_field($x))
    };
}

#[macro_export]
macro_rules! constant {
    ($x: expr) => {
        halo2_proofs::plonk::Expression::Constant($x)
    };
}

#[macro_export]
macro_rules! value_for_assign {
    ($x: expr) => {
        halo2_proofs::circuit::Value::known($x)
    };
}

#[cfg(test)]
mod tests {
    use super::{bn_to_field, field_to_bn};
    use halo2_proofs::halo2curves::{bn256::Fr, group::ff::PrimeField};

    #[test]
    fn test_bn_field_roundtrip() {
        let repr = Fr::one().to_repr();
        assert_eq!(
            repr,
            [
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ],
            "F::to_repr() must be little-endian"
        );

        let a = -Fr::one();
        let b = bn_to_field(&field_to_bn(&a));
        assert_eq!(a, b);
    }
}
