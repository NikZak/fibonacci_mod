#![feature(test)]
#![feature(specialization)]
use std::mem;
use num_prime::nt_funcs::factorize;
use num_prime::detail::{PrimalityBase, PrimalityRefBase};
use num_bigint::BigUint;

pub trait PisanoPeriodBase {
    fn pisano_period(&self) -> Self;
}
impl PisanoPeriodBase for u64 {
    fn pisano_period(&self) -> Self {
        pisano_period(self)
    }
}
impl PisanoPeriodBase for u128 {
    fn pisano_period(&self) -> Self {
        pisano_period(self)
    }
}
impl PisanoPeriodBase for usize {
    fn pisano_period(&self) -> Self {
        pisano_period(self)
    }
}
impl PisanoPeriodBase for u32 {
    fn pisano_period(&self) -> Self {
        pisano_period(self)
    }
}

impl PisanoPeriodBase for u16 {
    fn pisano_period(&self) -> Self {
        pisano_period(self)
    }
}

impl PisanoPeriodBase for u8 {
    fn pisano_period(&self) -> Self {
        pisano_period(self)
    }
}

impl PisanoPeriodBase for BigUint {
    fn pisano_period(&self) -> Self {
        pisano_period_ref(self)
    }
}

/// pis_per(m*n) for co-prime m and n is LCM(pis_per(m), pis_per(n))
/// pis_per(p^k) for prime p is likely p^(k-1) * pis_per(p) (not disproved yet)
/// so first factorize and then calculate pis_per for prime factors
fn pisano_period<U>(m: &U) -> U
where
    U: PrimalityBase ,
    for<'r> &'r U: PrimalityRefBase<U>,
{

    let factors = factorize(m.clone());
    let mut lcm_ = U::one();

    for (p, k) in factors.iter() {
        let pis_per_cur = pisano_period_prime(p) * (p.clone()).pow((k-1).try_into().unwrap());
        lcm_ = lcm_.lcm(&pis_per_cur);
    }
    lcm_

}
fn pisano_period_ref<U>(m:& U) -> U
    where
        U: PrimalityBase ,
        for<'r> &'r U: PrimalityRefBase<U>,
{
    let factors = factorize(m.clone());
    let mut lcm_ = U::one();

    for (p, k) in factors.iter() {
        let pis_per_cur = pisano_period_prime_ref(p) * (p.clone()).pow((k-1).try_into().unwrap());
        lcm_ = lcm_.lcm(&pis_per_cur);
    }
    lcm_

}

#[inline(always)]
fn pisano_period_prime_ref<U>(m: &U) -> U
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{
    let previous = &mut U::zero();
    let current = &mut U::one();
    let mut i = U::zero();
    loop {
        let temp = mem::replace(current, &(&*current + &*previous) % m) ;
        *previous = temp;
        if previous == &U::zero() && current == &U::one() {
            return i + U::one();
        }
        i = i + U::one();
    }
}

#[inline(always)]
fn pisano_period_prime<U>(m: &U) -> U
    where
        U: PrimalityBase,
{
    let mut previous = U::zero();
    let mut current = U::one();
    let mut i = U::zero();
    loop {
        (previous, current) = (current.clone(), (current + previous) % m.clone());
        if previous == U::zero() && current == U::one() {
            return i + U::one();
        }
        i = i + U::one();
    }
}

pub trait FibModBase
where
    Self:Sized,
    Self: PrimalityBase,
    for<'r> &'r Self: PrimalityRefBase<Self>,
{
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self);
}
impl FibModBase for u64 {
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self) {
        fib_mod_fast_doubling(*self, n, pis_per)
    }
}
impl FibModBase for u128 {
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self) {
        fib_mod_fast_doubling(*self, n, pis_per)
    }
}
impl FibModBase for usize {
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self) {
        fib_mod_fast_doubling(*self, n, pis_per)
    }
}
impl FibModBase for u32 {
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self) {
        fib_mod_fast_doubling(*self, n, pis_per)
    }
}

impl FibModBase for u16 {
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self) {
        fib_mod_fast_doubling(*self, n, pis_per)
    }
}

impl FibModBase for u8 {
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self) {
        fib_mod_fast_doubling(*self, n, pis_per)
    }
}

impl FibModBase for BigUint {
    fn fib_mod(&self, n: Self, pis_per: Self) -> (Self, Self) {
        let mut res_n = BigUint::from(0_usize);
        let mut res_n_p_one = BigUint::from(1_usize);
        fib_mod_fast_doubling_ref1(self, &n, &pis_per, &mut res_n, &mut res_n_p_one);
        (res_n, res_n_p_one)
    }
}


fn fib_mod_fast_doubling_ref<U>(k: U, n: U, pis_per: U) -> (U, U)
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{
    let mut res_n = U::zero();
    let mut res_n_p_one = U::one();
    fib_mod_fast_doubling_ref1(&k, &n, &pis_per, &mut res_n, &mut res_n_p_one);
    (res_n, res_n_p_one)
}

/// F_{2k} = F_k * (2 * F_{k+1} - F_k)
/// F_{2k+1} = F_k^2 + F_{k+1}^2
///
/// this is helper function to prevent cloning of U
/// normally U is integer type, so cloning is same as copying
/// however, it is not a given that U implements Copy
fn fib_mod_fast_doubling_ref1<U>(k: &U, n: &U, pis_per: &U, res_n: &mut U, res_n_p_one: &mut U)
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{

    let k = k % pis_per;

    if k == U::zero() {
        *res_n = U::zero();
        *res_n_p_one = U::one();
        return;
    } else if k == U::one() {
        *res_n = U::one();
        *res_n_p_one = U::one();
        return;
    }
    let two = &(U::one() + U::one());

    fib_mod_fast_doubling_ref1(&(&k / two), n, pis_per, res_n, res_n_p_one);
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
fn fib_mod_fast_doubling<U>(k: U, n: U, pis_per: U) -> (U, U)
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{

    let k = k % pis_per.clone();

    if k == U::zero() {
        return (U::zero(), U::one());
    } else if k == U::one() {
        return (U::one(), U::one());
    }
    let res_n;
    let res_n_p_one;
    let two = &(U::one() + U::one());

    (res_n, res_n_p_one) = fib_mod_fast_doubling(k.clone() / two, n.clone(), pis_per.clone());
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
    use rand_pcg::Pcg32;
    use rand::{Rng, SeedableRng, };
    use rand::distributions::Standard;
    use rand::prelude::Distribution;
    use std::ops::Rem;
    use num_bigint::BigUint;

    #[test]
    fn test_pisano_per_prime() {
        assert_eq!(pisano_period_prime_ref(&2_u128,             ), 3);
        assert_eq!(pisano_period_prime_ref(&3_u128,             ), 8);
        assert_eq!(pisano_period_prime_ref(&5_u128,             ), 20);
    }
    #[test]
    fn test_pisano_per() {
        assert_eq!(2_u128.pisano_period()             , 3);
        assert_eq!(3_u128.pisano_period(), 8);
        assert_eq!(5_u128.pisano_period(), 20);
        assert_eq!(7_u128.pisano_period(), 16);
        assert_eq!(11_u128.pisano_period(), 10);
        assert_eq!(47_u128.pisano_period(), 32);
        assert_eq!(235_u128.pisano_period(), 160);
        assert_eq!( ( 235*235 as u128 ).pisano_period(), 37600);
        assert_eq!(1234567891011_u128.pisano_period(), 900788112);
        assert_eq!(356_u128.pisano_period(), 132);
    }
    fn get_n_random_numbers<T>(n:u64, max: Option<T>, seed: Option<u64>) -> Vec<T>
    where
        Standard: Distribution<T>,
        T: Rem + Rem<Output = T> + Clone
    {
        let seed = seed.unwrap_or(1);
        let mut rng = Pcg32::seed_from_u64(seed);
        let mut numbers = Vec::new();
        for _ in 0..n {
            let num = rng.gen::<T>();
            if let Some(ref max) = max {
                numbers.push(num % max.clone());
            } else {
                numbers.push(num);
            }
        }
        numbers
    }

    fn get_n_random_numbers_into<T>(n:u64, max: Option<u64>, seed: Option<u64>) -> Vec<T>
    where
        T: From<u64>
    {
        let numbers = get_n_random_numbers::<u64>(n, max, seed);
        let numbers = numbers.iter().map(|x| (*x).try_into().unwrap()).collect::<Vec<_>>();
        numbers
    }

    fn pisano_period_bench<T: From<u64>>(n: u64, b: &mut Bencher, f: fn(&T) -> T)
        where
        T: PrimalityBase,
        for<'r> &'r T: PrimalityRefBase<T>,
    {
        let numbers = get_n_random_numbers_into::<T>(n, Some(100000), None);
        b.iter(||
            for n in &numbers {
                f(n);
            }
        );

    }
    fn fibonacci_mod_bench<T: From<u64>>(n: u64, b: &mut Bencher, f: fn(T, T, T) -> (T, T))
        where
            T: PrimalityBase,
            for<'r> &'r T: PrimalityRefBase<T>,
    {
        let numbers = get_n_random_numbers::<u64>(n, Some(100000), Some(1));
        let numbers = numbers.iter().map(|x| T::from(x.clone())).collect::<Vec<_>>();
        let modulos = get_n_random_numbers::<u64>(n, Some(100000), Some(2));
        let modulos = modulos.iter().map(|x| T::from(*x)).collect::<Vec<_>>();
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
        fibonacci_mod_bench::<u64>(100, b, fib_mod_fast_doubling)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_ref_u128(b: &mut Bencher) {
        fibonacci_mod_bench::<u128>(100, b, fib_mod_fast_doubling_ref)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_u128(b: &mut Bencher) {
        fibonacci_mod_bench::<u128>(100, b, fib_mod_fast_doubling)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_ref_biguint(b: &mut Bencher) {
        fibonacci_mod_bench::<BigUint>(100, b, fib_mod_fast_doubling_ref)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_biguint(b: &mut Bencher) {
        fibonacci_mod_bench::<BigUint>(100, b, fib_mod_fast_doubling)
    }
    #[bench]
    fn bench_pisano_period_ref_biguint(b: &mut Bencher) {
        pisano_period_bench::<BigUint>(100, b, pisano_period_ref)
    }

    #[bench]
    fn bench_pisano_period_biguint(b: &mut Bencher) {
        pisano_period_bench::<BigUint>(100, b, pisano_period)
    }
    #[bench]
    fn bench_pisano_period_ref_u64(b: &mut Bencher) {
        pisano_period_bench::<u64>(100, b, pisano_period_ref)
    }
    #[bench]
    fn bench_pisano_period_u64(b: &mut Bencher) {
        pisano_period_bench::<u64>(100, b, pisano_period)
    }
    #[bench]
    fn bench_pisano_period_ref_u128(b: &mut Bencher) {
        pisano_period_bench::<u128>(100, b, pisano_period_ref)
    }
    #[bench]
    fn bench_pisano_period_u128(b: &mut Bencher) {
        pisano_period_bench::<u128>(100, b, pisano_period)
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

