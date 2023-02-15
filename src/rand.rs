use std::convert::TryInto;
use std::ops::Rem;
use rand_pcg::Pcg32;
use rand::{Rng, SeedableRng, };
use rand::distributions::Standard;
use rand::prelude::Distribution;
use num_prime::nt_funcs::{next_prime};
use num_prime::detail::PrimalityBase;
use num_traits::ops::checked::CheckedAdd;
use num_prime::detail::PrimalityRefBase;

pub fn get_n_random_numbers_into<T>(n:u64, max: Option<u64>, seed: Option<u64>) -> Vec<T>
where
    T: From<u64>
{
    let numbers = get_n_random_numbers::<u64>(n, max, seed);
    let numbers = numbers.iter().map(|x| (*x).try_into().unwrap()).collect::<Vec<_>>();
    numbers
}
pub fn get_n_random_primes_into<T>(n:u64, max: Option<u64>, seed: Option<u64>) -> Vec<T>
    where
        T: From<u64>
{
    let numbers = get_n_random_primes::<u64>(n, max, seed);
    let numbers = numbers.iter().map(|x| (*x).try_into().unwrap()).collect::<Vec<_>>();
    numbers
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
fn get_n_random_primes<T>(n:u64, max: Option<T>, seed: Option<u64>) -> Vec<T>
where
    Standard: Distribution<T>,
    T: Rem + Rem<Output = T> + Clone + PrimalityBase+ CheckedAdd,
    for<'r> &'r T: PrimalityRefBase<T>,
{
    let seed = seed.unwrap_or(1);
    let mut rng = Pcg32::seed_from_u64(seed);
    let mut numbers = Vec::new();
    for _ in 0..n {
        let mut num = rng.gen::<T>();
        if let Some(ref max) = max {
            num = num % max;
        }
        numbers.push(next_prime(&num, None).unwrap());
    }
    numbers
}
