use num_prime::nt_funcs::factorize;
use gcd::Gcd;

/// pis_per(m*n) for co-prime m and n is LCM(pis_per(m), pis_per(n))
/// pis_per(p^k) for prime p is likely p^(k-1) * pis_per(p) (not disproved yet)
/// so first factorize and then calculate pis_per for prime factors
pub fn pisano_period(m: u128) -> u128 {

    let factors = factorize(m);
    let mut gcd_ : u128 = 1;
    let mut lcm_ : u128 = 1;

    for (i, (p, k)) in factors.iter().enumerate() {
        let pis_per_cur = pisano_period_prime(*p)*p.pow((k-1).try_into().unwrap());
        if i == 0 {
            gcd_ = pis_per_cur;
            lcm_ = pis_per_cur;
        } else {
            gcd_ = gcd_.gcd(pis_per_cur);
            lcm_ = lcm_ * pis_per_cur / gcd_;
        }
    }
    lcm_

}

pub fn pisano_period_prime(m: u128) -> u128 {
    let mut previous = 0;
    let mut current = 1;
    for i in 0..m * m {
        fib_step(&mut previous, &mut current, m);
        if previous == 0 && current == 1 {
            return i + 1;
        }
    }
    0
}

#[inline(always)]
fn fib_step(previous: &mut u128, current: &mut u128, m: u128) {
    (*previous, *current) = (*current, (*previous + *current) % m);
}

/// F_{2k} = F_k * (2 * F_{k+1} - F_k)
/// F_{2k+1} = F_k^2 + F_{k+1}^2
pub fn fib_mod_fast_doubling(k: u128, n: u128, pis_per: u128) -> (u128, u128) {

    let k = k % pis_per;

    if k == 0 {
        return (0, 1);
    } else if k == 1 {
        return (1, 1);
    }

    let (a, b) = fib_mod_fast_doubling(k / 2, n, pis_per);
    let c = (a * subtract_mod(2*b, a, n)) % n;
    let d = (a * a + b * b) % n;
    if k % 2 == 0 {
        (c, d)
    } else {
        (d, (c + d) % n)
    }
}

#[inline(always)]
fn subtract_mod(a: u128, b: u128, m: u128) -> u128 {
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
    fn test_pisano_per() {
        assert_eq!(pisano_period(2,             ), 3);
        assert_eq!(pisano_period(3,             ), 8);
        assert_eq!(pisano_period(5,             ), 20);
        assert_eq!(pisano_period(7,             ), 16);
        assert_eq!(pisano_period(11,            ), 10);
        assert_eq!(pisano_period(47,            ), 32);
        assert_eq!(pisano_period(235,           ), 160);
        assert_eq!(pisano_period(235*235,       ), 37600);
        assert_eq!(pisano_period(1234567891011, ), 21618914688);
        assert_eq!(pisano_period(356,           ), 132);
    }

    #[test]
    fn test_fib_fast_doubling() {
        let n = 235;
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
        assert_eq!(fib_mod_fast_doubling(1548276540, n, pis_per).0, 185);
        assert_eq!(fib_mod_fast_doubling(1548276540, 356, 132).0, 288);
    }
}

