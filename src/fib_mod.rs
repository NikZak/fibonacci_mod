use num_prime::detail::{PrimalityBase, PrimalityRefBase};
use num_bigint::BigUint;
macro_rules! impl_fib_mod {
    ($($t:ty)*) => ($(
        impl FibModBase for $t {
            fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self) {
                fib_mod_fast_doubling_pis_per(*self, n, pis_per)
            }
        }
    )*)
}

impl_fib_mod! {u64 u128 usize u32 u16 u8}
pub trait FibModBase
where
    Self:Sized,
    Self: PrimalityBase,
    for<'r> &'r Self: PrimalityRefBase<Self>,
{
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self);
}

impl FibModBase for BigUint {
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self) {
        let mut res_n = BigUint::from(0_usize);
        let mut res_n_p_one = BigUint::from(1_usize);
        fib_mod_fast_doubling_pisper_ref1(self, &n, &pis_per, &mut res_n, &mut res_n_p_one);
        (res_n, res_n_p_one)
    }
}

#[inline(always)]
pub(crate) fn fib_mod_fast_doubling_ref<U>(k: U, n: U, pis_per: U) -> (U, U)
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{
    let mut res_n = U::zero();
    let mut res_n_p_one = U::one();
    fib_mod_fast_doubling_pisper_ref1(&k, &n, &pis_per, &mut res_n, &mut res_n_p_one);
    (res_n, res_n_p_one)
}

/// F_{2k} = F_k * (2 * F_{k+1} - F_k)
/// F_{2k+1} = F_k^2 + F_{k+1}^2
///
/// this is helper function to prevent cloning of U
/// normally U is integer type, so cloning is same as copying
/// however, it is not a given that U implements Copy
#[inline(always)]
fn fib_mod_fast_doubling_pisper_ref1<U>(k: &U, n: &U, pis_per: &U, res_n: &mut U, res_n_p_one: &mut U)
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{

    let k = k % pis_per;
    fib_mod_fast_doubling_ref1(&k, n, res_n, res_n_p_one)

}
#[inline(always)]
fn fib_mod_fast_doubling_ref1<U>(k: &U, n: &U, res_n: &mut U, res_n_p_one: &mut U)
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{

    if k == &U::zero() {
        *res_n = U::zero();
        *res_n_p_one = U::one();
        return;
    } else if k == &U::one() {
        *res_n = U::one();
        *res_n_p_one = U::one();
        return;
    }
    let two = &(U::one() + U::one());

    fib_mod_fast_doubling_ref1(&(k / two), n, res_n, res_n_p_one);
    let c = (&*res_n * &subtract_mod_ref(&(two * &*res_n_p_one), &*res_n, n)) % n;
    let d = (&*res_n * &*res_n + &*res_n_p_one * &*res_n_p_one) % n;
    if k % two == U::zero() {
        *res_n = c;
        *res_n_p_one = d;
    } else {
        *res_n_p_one = (&c + &d) %n;
        *res_n = d;
    }
}

#[inline(always)]
fn fib_mod_fast_doubling_pis_per<U>(k: U, n: U, pis_per: U) -> (U, U)
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{
    let k = k % pis_per.clone();
    fib_mod_fast_doubling(k, n)
}

#[inline(always)]
pub fn fib_mod_fast_doubling<U>(k: U, n: U) -> (U, U)
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{
    if k == U::zero() {
        return (U::zero(), U::one());
    } else if k == U::one() {
        return (U::one(), U::one());
    }
    let res_n;
    let res_n_p_one;
    let two = &(U::one() + U::one());

    (res_n, res_n_p_one) = fib_mod_fast_doubling(k.clone() / two, n.clone());
    let c = (res_n.clone() * subtract_mod(two * res_n_p_one.clone(), res_n.clone(), n.clone())) % n.clone();
    let d = (res_n.pow(2) + res_n_p_one.pow(2) ) % n.clone();

    if k % two == U::zero() {
        (c, d)
    } else {
        (d.clone(), (c + d) % n)
    }
}


#[inline(always)]
fn subtract_mod_ref<U>(a: &U, b: &U, m: &U) -> U
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{
    if a >= b {
        a - b
    } else {
        m - (b - a)
    }
}

#[inline(always)]
fn subtract_mod<U>(a: U, b: U, m: U) -> U
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{
    if a >= b {
        a - b
    } else {
        m - (b - a)
    }
}

#[cfg( test )]
mod tests {
    use super::*;
    extern crate test;
    use test::Bencher;
    use num_bigint::BigUint;
    use crate::rand::get_n_random_numbers_into;
    use crate::pisano::pisano_period;

    fn fibonacci_mod_bench<T>(n: u64, b: &mut Bencher, f: fn(T, T, T) -> (T, T))
        where
            T: PrimalityBase,
            for<'r> &'r T: PrimalityRefBase<T>,
            T: From<u8> + From<u64>
    {
        let numbers = get_n_random_numbers_into::<T>(n, Some(100000), Some(1));
        let modulos = get_n_random_numbers_into::<T>(n, Some(100000), Some(2));

        let pis_pes = numbers.iter().map(|x| pisano_period(x)).collect::<Vec<_>>();
        b.iter(||
            for (i, n) in numbers.iter().enumerate() {
                f(n.clone(), modulos[i].clone(), pis_pes[i].clone());
            }
        );

    }
    #[bench]
    fn bench_fib_mod_fast_doubling_ref_u64(b: &mut Bencher) {
        fibonacci_mod_bench::<u64>(100, b, fib_mod_fast_doubling_ref)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_u64(b: &mut Bencher) {
        fibonacci_mod_bench::<u64>(100, b, fib_mod_fast_doubling_pis_per)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_ref_u128(b: &mut Bencher) {
        fibonacci_mod_bench::<u128>(100, b, fib_mod_fast_doubling_ref)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_u128(b: &mut Bencher) {
        fibonacci_mod_bench::<u128>(100, b, fib_mod_fast_doubling_pis_per)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_ref_biguint(b: &mut Bencher) {
        fibonacci_mod_bench::<BigUint>(100, b, fib_mod_fast_doubling_ref)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_biguint(b: &mut Bencher) {
        fibonacci_mod_bench::<BigUint>(100, b, fib_mod_fast_doubling_pis_per)
    }

    #[test]
    fn test_fib_fast_doubling() {
        let n:u128 = 235;
        let pis_per = 160;
        assert_eq!(0.fib_mod(n, pis_per), (0, 1));
        assert_eq!(1.fib_mod(n, pis_per), (1, 1));
        assert_eq!(fib_mod_fast_doubling_ref(2, n, pis_per), (1, 2));
        assert_eq!(fib_mod_fast_doubling_ref(3, n, pis_per), (2, 3));
        assert_eq!(fib_mod_fast_doubling_ref(4, n, pis_per), (3, 5));
        assert_eq!(fib_mod_fast_doubling_ref(5, n, pis_per), (5, 8));
        assert_eq!(fib_mod_fast_doubling_ref(6, n, pis_per), (8, 13));
        assert_eq!(fib_mod_fast_doubling_ref(7, n, pis_per), (13, 21));
        assert_eq!(fib_mod_fast_doubling_ref(8, n, pis_per), (21, 34));
        assert_eq!(fib_mod_fast_doubling_ref(9, n, pis_per), (34, 55));
        assert_eq!(fib_mod_fast_doubling_ref(10, n, pis_per), (55, 89));
        assert_eq!(fib_mod_fast_doubling_ref(11, n, pis_per), (89, 144));
        assert_eq!(fib_mod_fast_doubling_ref(12, n, pis_per), (144, 233));
        assert_eq!(1548276540.fib_mod(n, pis_per).0, 185);
        assert_eq!((BigUint::from(1548276540_usize)).fib_mod(BigUint::from(356_usize), BigUint::from(132_usize)).0, BigUint::from(288_usize));
    }
}
