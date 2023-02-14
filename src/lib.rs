#![feature(test)]
use std::fmt::{Display};
use std::fmt::Debug;
use std::mem;
use num_prime::nt_funcs::factorize;
use num_prime::detail::{PrimalityBase, PrimalityRefBase};

/// pis_per(m*n) for co-prime m and n is LCM(pis_per(m), pis_per(n))
/// pis_per(p^k) for prime p is likely p^(k-1) * pis_per(p) (not disproved yet)
/// so first factorize and then calculate pis_per for prime factors
pub fn pisano_period<U>(m: U) -> U
where
    U: PrimalityBase ,
    for<'r> &'r U: PrimalityRefBase<U>,
{

    let factors = factorize(m);
    let mut lcm_ = U::one();

    for (p, k) in factors.iter() {
        let pis_per_cur = pisano_period_prime(p) * (p.clone()).pow((k-1).try_into().unwrap());
        lcm_ = lcm_.lcm(&pis_per_cur);
    }
    lcm_

}

#[inline(always)]
pub fn pisano_period_prime<U>(m: &U) -> U
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
fn pisano_period_prime1<U>(m: U) -> U
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

pub fn fib_mod_fast_doubling<U>(k: U, n: U, pis_per: U) -> (U, U)
    where
        U: PrimalityBase,
        for<'r> &'r U: PrimalityRefBase<U>,
{
    let mut res_n = U::zero();
    let mut res_n_p_one = U::one();
    fib_mod_fast_doubling_ref(&k, &n, &pis_per, &mut res_n, &mut res_n_p_one);
    (res_n, res_n_p_one)

}

/// F_{2k} = F_k * (2 * F_{k+1} - F_k)
/// F_{2k+1} = F_k^2 + F_{k+1}^2
///
/// this is helper function to prevent cloning of U
/// normally U is integer type, so cloning is same as copying
/// however, it is not a given that U implements Copy
pub fn fib_mod_fast_doubling_ref<U>(k: &U, n: &U, pis_per: &U, res_n: &mut U, res_n_p_one: &mut U)
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

    fib_mod_fast_doubling_ref(&(&k / two), n, pis_per, res_n, res_n_p_one);
    let c = (&*res_n * &subtract_mod(&(two * &*res_n_p_one), &*res_n, n)) % n;
    let d = (&*res_n * &*res_n + &*res_n_p_one * &*res_n_p_one) % n;
    if k % two == U::zero() {
        *res_n = c;
        *res_n_p_one = d;
    } else {
        *res_n_p_one = (&c + &d) %n;
        *res_n = d;
    }
}
fn fib_mod_fast_doubling1<U>(k: U, n: U, pis_per: U) -> (U, U)
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
    let mut res_n;
    let mut res_n_p_one;
    let two = &(U::one() + U::one());

    (res_n, res_n_p_one) = fib_mod_fast_doubling1((k.clone() / two), n.clone(), pis_per.clone());
    let c = (res_n.clone() * subtract_mod1((two * res_n_p_one.clone()), res_n.clone(), n.clone())) % n.clone();
    let d = (res_n.pow(2) + res_n_p_one.pow(2) ) % n.clone();

    if k % two == U::zero() {
        (c, d)
    } else {
        (d.clone(), (c + d) % n)
    }
}

#[inline(always)]
fn subtract_mod<U>(a: &U, b: &U, m: &U) -> U
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
fn subtract_mod1<U>(a: U, b: U, m: U) -> U
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
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use rand::distributions::Standard;
    use rand::prelude::Distribution;
    use std::ops::Rem;
    use num_bigint::BigUint;

    #[test]
    fn test_pisano_per_prime() {
        assert_eq!(pisano_period_prime(&2_u128,             ), 3);
        assert_eq!(pisano_period_prime(&3_u128,             ), 8);
        assert_eq!(pisano_period_prime(&5_u128,             ), 20);
    }
    #[test]
    fn test_pisano_per() {
        assert_eq!(pisano_period(2_u128,             ), 3);
        assert_eq!(pisano_period(3_u128,             ), 8);
        assert_eq!(pisano_period(5_u128,             ), 20);
        assert_eq!(pisano_period(7_u128,             ), 16);
        assert_eq!(pisano_period(11_u128,            ), 10);
        assert_eq!(pisano_period(47_u128,            ), 32);
        assert_eq!(pisano_period(235_u128,           ), 160);
        assert_eq!(pisano_period(235*235 as u128,       ), 37600);
        assert_eq!(pisano_period(1234567891011_u128, ), 900788112);
        assert_eq!(pisano_period(356_u128,           ), 132);
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

    fn pisano_period_bench1<T: From<u64>>(n: u64, b: &mut Bencher)
        where
            T: PrimalityBase,
            for<'r> &'r T: PrimalityRefBase<T>,
            T: From<u64>,
    {
        // let numbers = get_n_random_numbers::<u64>(100, Some(100000));
        // let numbers = numbers.iter().map(|x| T::from(*x)).collect::<Vec<_>>();
        let numbers = get_n_random_numbers_into::<T>(100, Some(100000), None);
        b.iter(||
            for n in &numbers {
                pisano_period_prime1(n.clone());
            }
        );

    }

    fn pisano_period_bench<T: From<u64>>(n: u64, b: &mut Bencher)
        where
        T: PrimalityBase,
        for<'r> &'r T: PrimalityRefBase<T>,
    {
        let numbers = get_n_random_numbers::<u64>(100, Some(100000), None);
        let numbers = numbers.iter().map(|x| T::from(*x)).collect::<Vec<_>>();
        b.iter(||
            for n in &numbers {
                pisano_period_prime(n);
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
        let pis_pes = numbers.iter().map(|x| pisano_period(x.clone())).collect::<Vec<_>>();
        b.iter(||
            for (i, n) in numbers.iter().enumerate() {
                f(n.clone(), modulos[i].clone(), pis_pes[i].clone());
            }
        );

    }
    #[bench]
    fn bench_fib_mod_fast_doubling_u64(b: &mut Bencher) {
        fibonacci_mod_bench::<u64>(100, b, fib_mod_fast_doubling)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling1_u64(b: &mut Bencher) {
        fibonacci_mod_bench::<u64>(100, b, fib_mod_fast_doubling1)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_u128(b: &mut Bencher) {
        fibonacci_mod_bench::<u128>(100, b, fib_mod_fast_doubling)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling1_u128(b: &mut Bencher) {
        fibonacci_mod_bench::<u128>(100, b, fib_mod_fast_doubling1)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling_biguint(b: &mut Bencher) {
        fibonacci_mod_bench::<BigUint>(100, b, fib_mod_fast_doubling)
    }
    #[bench]
    fn bench_fib_mod_fast_doubling1_biguint(b: &mut Bencher) {
        fibonacci_mod_bench::<BigUint>(100, b, fib_mod_fast_doubling1)
    }
    #[bench]
    fn bench_pisano_period_biguint(b: &mut Bencher) {
        pisano_period_bench::<BigUint>(100, b)
    }

    #[bench]
    fn bench_pisano_period1_biguint(b: &mut Bencher) {
        pisano_period_bench1::<BigUint>(100, b)
    }
    #[bench]
    fn bench_pisano_period_u64(b: &mut Bencher) {
        pisano_period_bench::<u64>(100, b)
    }
    #[bench]
    fn bench_pisano_period1_u64(b: &mut Bencher) {
        pisano_period_bench1::<u64>(100, b)
    }
    #[bench]
    fn bench_pisano_period_u128(b: &mut Bencher) {
        pisano_period_bench::<u128>(100, b)
    }
    #[bench]
    fn bench_pisano_period1_u128(b: &mut Bencher) {
        pisano_period_bench1::<u128>(100, b)
    }

    #[test]
    fn test_fib_fast_doubling() {
        let n:u128 = 235;
        let pis_per = 160;
        assert_eq!(fib_mod_fast_doubling(0,          n, pis_per), (0, 1));
        assert_eq!(fib_mod_fast_doubling(1,          n, pis_per), (1, 1));
        assert_eq!(fib_mod_fast_doubling(2,          n, pis_per), (1, 2));
        assert_eq!(fib_mod_fast_doubling(3,          n, pis_per), (2, 3));
        assert_eq!(fib_mod_fast_doubling(4,          n, pis_per), (3, 5));
        assert_eq!(fib_mod_fast_doubling(5,          n, pis_per), (5, 8));
        assert_eq!(fib_mod_fast_doubling(6,          n, pis_per), (8, 13));
        assert_eq!(fib_mod_fast_doubling(7,          n, pis_per), (13, 21));
        assert_eq!(fib_mod_fast_doubling(8,          n, pis_per), (21, 34));
        assert_eq!(fib_mod_fast_doubling(9,          n, pis_per), (34, 55));
        assert_eq!(fib_mod_fast_doubling(10,         n, pis_per), (55, 89));
        assert_eq!(fib_mod_fast_doubling(11,         n, pis_per), (89, 144));
        assert_eq!(fib_mod_fast_doubling(12,         n, pis_per), (144, 233));
        assert_eq!(fib_mod_fast_doubling(1548276540,         n, pis_per).0, 185);
        assert_eq!(fib_mod_fast_doubling(1548276540 as u128, 356, 132).0, 288);
    }
}

