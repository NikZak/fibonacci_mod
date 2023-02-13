use std::fmt::{Display};
use std::mem;
use num_prime::nt_funcs::factorize;
use num_prime::detail::{PrimalityBase, PrimalityRefBase};

/// pis_per(m*n) for co-prime m and n is LCM(pis_per(m), pis_per(n))
/// pis_per(p^k) for prime p is likely p^(k-1) * pis_per(p) (not disproved yet)
/// so first factorize and then calculate pis_per for prime factors
pub fn pisano_period<U>(m: U) -> U
where
    U: PrimalityBase + Display,
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

#[cfg( test )]
mod tests {
    use super::*;
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

    #[test]
    fn test_fib_fast_doubling() {
        let n:u128 = 235;
        let pis_per = 160;
        let mut res_n=0;
        let mut res_n_p_1=0;
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

