use crate::priv_prelude::*;

#[derive(PartialOrd, Ord, PartialEq, Eq, Clone, Debug)]
pub struct NonZeroBigUint {
    inner: BigUint,
}

impl NonZeroBigUint {
    pub fn new(val: BigUint) -> Option<NonZeroBigUint> {
        if val.is_zero() {
            None
        } else {
            Some(NonZeroBigUint { inner: val })
        }
    }

    pub fn try_decrement(&self) -> Option<NonZeroBigUint> {
        let inner = &self.inner - 1u32;
        NonZeroBigUint::new(inner)
    }

    pub fn increment(&mut self) {
        self.inner += 1u32;
    }

    pub fn as_big_uint(&self) -> &BigUint {
        &self.inner
    }

    pub fn into_big_uint(self) -> BigUint {
        self.inner
    }

    pub fn bits(&self) -> NonZero<u64> {
        NonZero::new(self.inner.bits()).unwrap()
    }

    pub fn bit(&self, bit: u64) -> bool {
        self.inner.bit(bit)
    }

    pub fn trailing_zeros(&self) -> u64 {
        self.inner.trailing_zeros().unwrap()
    }

    pub fn strict_sub(&self, rhs: &NonZeroBigUint) -> BigUint {
        self.inner.checked_sub(&rhs.inner).unwrap()
    }

    /*
    pub fn nth_prime(n: usize) -> NonZeroBigUint {
        lazy_static! {
            static ref ALL_PRIMES: Mutex<Vec<NonZeroBigUint>> = Mutex::new(Vec::new());
        }

        loop {
            let all_primes = ALL_PRIMES.read().unwrap();
            if let Some(prime) = all_primes.get(n) {
                return prime.clone();
            }

            let next_n = all_primes.len();
            let mut candidate_prime = all_primes.last().cloned().unwrap_or_else(|| NonZeroBigUint::from(2u32));
            loop {
                let mut iter = all_primes.iter();
                let is_prime = loop {
                    match iter.next() {
                        Some(prime) => {
                            if candidate_prime % prime == 0 {
                                break false;
                            }
                            if candidate_prime < prime * prime {
                                break true;
                            }
                        },
                        None => break true,
                    }
                };
                if is_prime {
                    break;
                }
                candidate_prime += 2;
            }
            drop(all_primes);

            let all_primes = ALL_PRIMES.write().unwrap();
            if all_primes.len() == next_n {
                all_primes.push(candidate_prime);
            }
        }
    }

    pub fn prime_factors(self) -> impl Iterator<(NonZeroBigUint, NonZeroUsize)> {
        let mut val = self;
        let mut n = 0;
        iter::from_fn(move || {
            if val.is_one() {
                return None;
            }
            loop {
                let prime = NonZeroBigUint::nth_prime(n);
                if val % prime == 0 {
                    let mut exponent = 1;
                    val.exact_div_assign(&prime);
                    while val % prime == 0 {
                        exponent += 1;
                        val.exact_div_assign(&prime);
                    }
                    return Some((prime, exponent));
                }
                n += 1;
            }
        })
    }

    pub fn greatest_root(&self) -> Option<NonZeroUsize> {
        self.prime_factors().map(|(_prime, exponent)| exponent).reduce(NonZeroUsize::gcd)
    }

    pub fn exact_nth_root(self, n: NonZeroBigUint) -> NonZeroBigUint {
        let mut ret = NonZeroBigUint::one();
        for (prime, exponent) in self.prime_factors() {
            let new_exponent = exponent.exact_div(n);
            ret *= prime.pow(new_exponent);
        }
        ret
    }
    */
}

impl One for NonZeroBigUint {
    fn one() -> NonZeroBigUint {
        NonZeroBigUint {
            inner: BigUint::one(),
        }
    }
}

impl ops::Add<NonZeroBigUint> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: NonZeroBigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner + rhs.inner,
        }
    }
}

impl ops::Add<&NonZeroBigUint> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: &NonZeroBigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner + &rhs.inner,
        }
    }
}

impl ops::Add<NonZeroBigUint> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: NonZeroBigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner + rhs.inner,
        }
    }
}

impl ops::Add<&NonZeroBigUint> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: &NonZeroBigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner + &rhs.inner,
        }
    }
}

impl ops::AddAssign<NonZeroBigUint> for NonZeroBigUint {
    fn add_assign(&mut self, rhs: NonZeroBigUint) {
        self.inner += rhs.inner;
    }
}

impl ops::AddAssign<&NonZeroBigUint> for NonZeroBigUint {
    fn add_assign(&mut self, rhs: &NonZeroBigUint) {
        self.inner += &rhs.inner;
    }
}


impl ops::Add<BigUint> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: BigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner + rhs,
        }
    }
}

impl ops::Add<&BigUint> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: &BigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner + rhs,
        }
    }
}

impl ops::Add<BigUint> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: BigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner + rhs,
        }
    }
}

impl ops::Add<&BigUint> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: &BigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner + rhs,
        }
    }
}

impl ops::AddAssign<BigUint> for NonZeroBigUint {
    fn add_assign(&mut self, rhs: BigUint) {
        self.inner += rhs;
    }
}

impl ops::AddAssign<&BigUint> for NonZeroBigUint {
    fn add_assign(&mut self, rhs: &BigUint) {
        self.inner += rhs;
    }
}

impl ops::Add<usize> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: usize) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner + rhs,
        }
    }
}

impl ops::Add<&usize> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: &usize) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner + rhs,
        }
    }
}

impl ops::Add<usize> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: usize) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner + rhs,
        }
    }
}

impl ops::Add<&usize> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn add(self, rhs: &usize) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner + rhs,
        }
    }
}

impl ops::AddAssign<usize> for NonZeroBigUint {
    fn add_assign(&mut self, rhs: usize) {
        self.inner += rhs;
    }
}

impl ops::AddAssign<&usize> for NonZeroBigUint {
    fn add_assign(&mut self, rhs: &usize) {
        self.inner += *rhs;
    }
}

impl ops::Mul<NonZeroBigUint> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn mul(self, rhs: NonZeroBigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner * rhs.inner,
        }
    }
}

impl ops::Mul<&NonZeroBigUint> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn mul(self, rhs: &NonZeroBigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner * &rhs.inner,
        }
    }
}

impl ops::Mul<NonZeroBigUint> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn mul(self, rhs: NonZeroBigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner * rhs.inner,
        }
    }
}

impl ops::Mul<&NonZeroBigUint> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn mul(self, rhs: &NonZeroBigUint) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner * &rhs.inner,
        }
    }
}

impl ops::MulAssign<NonZeroBigUint> for NonZeroBigUint {
    fn mul_assign(&mut self, rhs: NonZeroBigUint) {
        self.inner *= rhs.inner;
    }
}

impl ops::MulAssign<&NonZeroBigUint> for NonZeroBigUint {
    fn mul_assign(&mut self, rhs: &NonZeroBigUint) {
        self.inner *= &rhs.inner;
    }
}

impl ops::Mul<NonZero<usize>> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn mul(self, rhs: NonZero<usize>) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner * rhs.get(),
        }
    }
}

impl ops::Mul<&NonZero<usize>> for NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn mul(self, rhs: &NonZero<usize>) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: self.inner * rhs.get(),
        }
    }
}

impl ops::Mul<NonZero<usize>> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn mul(self, rhs: NonZero<usize>) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner * rhs.get(),
        }
    }
}

impl ops::Mul<&NonZero<usize>> for &NonZeroBigUint {
    type Output = NonZeroBigUint;

    fn mul(self, rhs: &NonZero<usize>) -> NonZeroBigUint {
        NonZeroBigUint {
            inner: &self.inner * rhs.get(),
        }
    }
}

impl ops::MulAssign<NonZero<usize>> for NonZeroBigUint {
    fn mul_assign(&mut self, rhs: NonZero<usize>) {
        self.inner *= rhs.get();
    }
}

impl ops::MulAssign<&NonZero<usize>> for NonZeroBigUint {
    fn mul_assign(&mut self, rhs: &NonZero<usize>) {
        self.inner *= rhs.get();
    }
}

impl fmt::Display for NonZeroBigUint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.inner, f)
    }
}

