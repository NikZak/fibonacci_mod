use num_prime::nt_funcs::factorize;
use num_bigint::BigUint;
use num_prime::detail::PrimalityBase;
use num_prime::detail::PrimalityRefBase;
use crate::fib_mod::fib_mod_fast_doubling;

pub trait PisanoPeriodBase {
    fn pisano_period(&self) -> Self;
}
macro_rules! impl_pisano_period {
    ($($t:ty)*) => ($(
        impl PisanoPeriodBase for $t {
            fn pisano_period(&self) -> Self {
                pisano_period(self)
            }
        }
    )*)
}
impl_pisano_period! {u64 u128 usize u32 u16 u8}

impl PisanoPeriodBase for BigUint {
    fn pisano_period(&self) -> Self {
        pisano_period_ref(self)
    }
}

/// pis_per(m*n) for co-prime m and n is LCM(pis_per(m), pis_per(n))
/// pis_per(p^k) for prime p is likely p^(k-1) * pis_per(p) (not disproved yet)
/// so first factorize and then calculate pis_per for prime factors
pub fn pisano_period<U>(m: &U) -> U
where
    U: PrimalityBase ,
    for<'r> &'r U: PrimalityRefBase<U>,
    U: From<u8>,
{

    let factors = factorize(m.clone());
    let mut lcm_ = U::one();

    for (p, k) in factors.iter() {
        let pis_per_cur = pisano_period_prime_fast(p) * (p.clone()).pow((k-1).try_into().unwrap());
        lcm_ = lcm_.lcm(&pis_per_cur);
    }
    lcm_
}


pub fn pisano_period_ref<U>(m:& U) -> U
    where
        U: PrimalityBase ,
        for<'r> &'r U: PrimalityRefBase<U>,
        U: From<u8>,

{
    let factors = factorize(m.clone());
    let mut lcm_ = U::one();

    for (p, k) in factors.iter() {
        let pis_per_cur = pisano_period_prime_fast_ref(p) * (p.clone()).pow((k-1).try_into().unwrap());
        lcm_ = lcm_.lcm(&pis_per_cur);
    }
    lcm_

}

#[inline(always)]
fn pisano_period_prime_simple<U>(m: &U) -> U
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

#[inline(always)]
fn pisano_period_prime_fast<U>(m: &U) -> U
    where
        U: PrimalityBase ,
        for<'r> &'r U: PrimalityRefBase<U>,
        U: From<u8>
{
    let two = U::from(2_u8);
    let three = U::from(3_u8);
    if m == &two {
        return three;
    }
    let eight = U::from(8_u8);
    if m == &three {
        return eight;
    }
    let five = U::from(5_u8);
    let twenty = U::from(20_u8);
    if m == &five {
        return twenty;
    }

    let one = U::from(1_u8);
    let seven = U::from(7_u8);
    let nine = U::from(9_u8);
    let ten = U::from(10_u8);

    let rem_10 = m.clone() % ten;
    let starting_cand;

    // if m % 10 is 1 or 9 then pisano period is divisor of m-1
    // if m % 10 is 3 or 7 then pisano period is divisor of 2(m+1)

    if rem_10 == one || rem_10 == nine {
        starting_cand = m.clone() - U::one();
    } else if rem_10 == three || rem_10 == seven {
        starting_cand = two * (m.clone() + U::one());
    } else {
        unreachable!("if m is a prime number then m % 10 is either 1, 3, 7 or 9")
    };
    let factors = factorize(starting_cand.clone());

    let mut true_pis_per = U::one();
    for (p, k) in factors.iter() {
        let mut cur_cand = starting_cand.clone() / p.clone();
        let mut cur_mult = *k;
        for _ in (0..*k).rev() {
            if fib_mod_fast_doubling(cur_cand.clone(), m.clone()) == (U::zero(), U::one()) {
                cur_cand = cur_cand / p.clone();
                cur_mult -= 1;
            } else {
                break;
            }
        }
        true_pis_per = true_pis_per * (p.clone()).pow(cur_mult.try_into().unwrap());
    }
    true_pis_per
}

/// Same as pisano_period_prime_fast but uses references instead of cloning
#[inline(always)]
fn pisano_period_prime_fast_ref<U>(m: &U) -> U
    where
        U: PrimalityBase ,
        for<'r> &'r U: PrimalityRefBase<U>,
        U: From<u8>
{
    let two = U::from(2_u8);
    let three = U::from(3_u8);
    if m == &two {
        return three;
    }
    let eight = U::from(8_u8);
    if m == &three {
        return eight;
    }
    let five = U::from(5_u8);
    let twenty = U::from(20_u8);
    if m == &five {
        return twenty;
    }

    let one = U::from(1_u8);
    let seven = U::from(7_u8);
    let nine = U::from(9_u8);
    let ten = U::from(10_u8);

    let rem_10 = m.clone() % ten;
    let starting_cand;

    // if m % 10 is 1 or 9 then pisano period is divisor of m-1
    // if m % 10 is 3 or 7 then pisano period is divisor of 2(m+1)

    if rem_10 == one || rem_10 == nine {
        starting_cand = m - U::one();
    } else if rem_10 == three || rem_10 == seven {
        starting_cand = two * (m + U::one());
    } else {
        unreachable!("if m is a prime number then m % 10 is either 1, 3, 7 or 9")
    };
    let starting_cand = &starting_cand;
    let factors = factorize(starting_cand.clone());

    let mut true_pis_per = U::one();
    for (p, k) in factors.iter() {
        let mut cur_cand = starting_cand / p;
        let mut cur_mult = *k;
        for _ in (0..*k).rev() {
            if fib_mod_fast_doubling(cur_cand.clone(), m.clone()) == (U::zero(), U::one()) {
                cur_cand = cur_cand / p;
                cur_mult -= 1;
            } else {
                break;
            }
        }
        true_pis_per = true_pis_per * (p.clone()).pow(cur_mult.try_into().unwrap());
    }
    true_pis_per

}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate test;
    use test::Bencher;
    use crate::rand::get_n_random_numbers_into;
    use crate::rand::get_n_random_primes_into;
    #[test]
    fn test_pisano_per_prime_fast() {
        assert_eq!(pisano_period_prime_fast(&2_u128,             ), 3);
        assert_eq!(pisano_period_prime_fast(&3_u128,             ), 8);
        assert_eq!(pisano_period_prime_fast(&5_u128,             ), 20);
    }
    #[test]
    fn test_compare_pisano_per_prime_fast() {
        let n = 1000;
        let numbers = get_n_random_primes_into::<u128>(n, Some(100000), Some(1));
        numbers.iter().for_each(|x| {
            assert_eq!(pisano_period_prime_fast::<u128>(x), pisano_period_prime_simple(x), "for prime {}", x);
        });
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
    #[bench]
    fn bench_pisano_period_prime_simple(b: &mut Bencher) {
        pisano_period_prime_bench::<u128>(100, b, pisano_period_prime_simple)
    }
    #[bench]
    fn bench_pisano_period_prime_fast(b: &mut Bencher) {
        pisano_period_prime_bench::<u128>(100, b, pisano_period_prime_fast)
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
    fn pisano_period_prime_bench<T: From<u64>>(n: u64, b: &mut Bencher, f: fn(&T) -> T)
        where
            T: PrimalityBase,
            for<'r> &'r T: PrimalityRefBase<T>,
    {
        let numbers = get_n_random_primes_into::<T>(n, Some(100000), None);
        b.iter(||
            for n in &numbers {
                f(n);
            }
        );

    }

}
