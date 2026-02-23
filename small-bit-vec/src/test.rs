use {
    crate::SmallBitVec,
    rand::{Rng, SeedableRng},
    rand_xoshiro::Xoshiro256StarStar,
};

fn random_identical_stdvec_and_bitvec_of_len(
    rng: &mut Xoshiro256StarStar,
    len: usize,
) -> (Vec<bool>, SmallBitVec) {
    let mut stdvec = Vec::with_capacity(len);
    let mut bitvec = SmallBitVec::with_capacity(len);
    for _ in 0..len {
        let bit = rng.r#gen();
        stdvec.push(bit);
        bitvec.push(bit);
    }
    (stdvec, bitvec)
}

#[test]
fn new() {
    let mut v = SmallBitVec::new();
    assert_eq!(v.len(), 0);
    assert!(v.pop().is_none());
    assert!(v.is_empty());
    assert_eq!(v.capacity(), usize::BITS as usize);
}

#[test]
fn with_capacity() {
    for cap in [0, 1, 2, 10, 20, 100, 200] {
        let bitvec = SmallBitVec::with_capacity(cap);
        assert!(bitvec.capacity() >= cap);
    }
}

#[test]
fn random_pushes() {
    const LEN: usize = 10000;
    let mut rng = Xoshiro256StarStar::seed_from_u64(0x0123456789abcdef);
    let mut stdvec = Vec::new();
    let mut bitvec = SmallBitVec::new();
    for index in 0..LEN {
        assert_eq!(bitvec.len(), index);
        let bit = rng.r#gen();
        stdvec.push(bit);
        bitvec.push(bit);
    }
    for index in 0..LEN {
        assert_eq!(stdvec[index], bitvec.get(index).unwrap());
    }
    assert!(stdvec.iter().copied().eq(bitvec.iter()));

    let mut cloned = bitvec.clone();
    assert!(bitvec.iter().eq(cloned.iter()));
    assert_eq!(bitvec, cloned);

    for bit in stdvec.iter().rev().copied() {
        assert_eq!(cloned.pop().unwrap(), bit);
    }

    let collected: SmallBitVec = stdvec.iter().copied().collect();
    assert!(bitvec.iter().eq(collected.into_iter()));

    for _ in 0..1000 {
        let bit = rng.r#gen();
        let index = rng.r#gen::<usize>() % LEN;
        stdvec[index] = bit;
        bitvec.set(index, bit);
    }
    assert!(stdvec.iter().copied().eq(bitvec.iter()));

    while !bitvec.is_empty() {
        let new_len = rng.r#gen::<usize>() % (bitvec.len() + 1);
        stdvec.truncate(new_len);
        bitvec.truncate(new_len);
        assert_eq!(bitvec, stdvec.as_slice());
    }
}

#[test]
fn gather_bits() {
    const ITERATIONS: usize = 1000;

    fn stdvec_gather_bits(
        vec: &[bool],
        mask: &[bool],
    ) -> Vec<bool> {
        let mut ret = Vec::new();
        for (index, bit) in mask.iter().copied().enumerate() {
            if bit {
                let bit = match vec.get(index).copied() {
                    None => return ret,
                    Some(bit) => bit,
                };
                ret.push(bit);
            }
        }
        if let Some(remaining) = vec.get(mask.len()..) {
            ret.extend(remaining);
        }
        ret
    }

    fn debug_print_stdvec(vec: &[bool]) {
        print!("[");
        for bit in vec.iter().copied() {
            print!("{}", bit as u32);
        }
        println!("]");
    }

    fn check_gather_bits(
        stdvec: &[bool],
        bitvec: &SmallBitVec,
        stdvec_mask: &[bool],
        bitvec_mask: &SmallBitVec,
    ) {
        println!("CHECKING:");
        debug_print_stdvec(stdvec);
        debug_print_stdvec(stdvec_mask);
        println!("");

        let stdvec_output = stdvec_gather_bits(stdvec, stdvec_mask);
        let mut bitvec_output = bitvec.clone();
        bitvec_output.gather_bits(bitvec_mask);
        if !(stdvec_output.iter().copied().eq(bitvec_output.iter())) {
            println!("FAILURE:");
            debug_print_stdvec(stdvec);
            debug_print_stdvec(stdvec_mask);
            println!("");
            println!("{:?}", bitvec);
            println!("{:?}", bitvec_mask);
            println!("");
            debug_print_stdvec(&stdvec_output);
            println!("{:?}", bitvec_output);
        }
        assert!(stdvec_output.iter().copied().eq(bitvec_output.iter()));
    }

    let mut rng = Xoshiro256StarStar::seed_from_u64(0x0123456789abcdef);
    for len in 0..ITERATIONS {
        let (stdvec, bitvec) = random_identical_stdvec_and_bitvec_of_len(&mut rng, len);

        let (stdvec_mask, bitvec_mask) = {
            random_identical_stdvec_and_bitvec_of_len(&mut rng, len)
        };
        check_gather_bits(&stdvec, &bitvec, &stdvec_mask, &bitvec_mask);

        let stdvec_mask: Vec<bool> = std::iter::repeat(false).take(len).collect();
        let bitvec_mask: SmallBitVec = std::iter::repeat(false).take(len).collect();
        check_gather_bits(&stdvec, &bitvec, &stdvec_mask, &bitvec_mask);

        let stdvec_mask: Vec<bool> = std::iter::repeat(true).take(len).collect();
        let bitvec_mask: SmallBitVec = std::iter::repeat(true).take(len).collect();
        check_gather_bits(&stdvec, &bitvec, &stdvec_mask, &bitvec_mask);

        let diff = rng.r#gen::<usize>() % (1 + len);
        let (stdvec_mask, bitvec_mask) = {
            random_identical_stdvec_and_bitvec_of_len(&mut rng, len - diff)
        };
        check_gather_bits(&stdvec, &bitvec, &stdvec_mask, &bitvec_mask);

        let stdvec_mask: Vec<bool> = std::iter::repeat(false).take(len - diff).collect();
        let bitvec_mask: SmallBitVec = std::iter::repeat(false).take(len - diff).collect();
        check_gather_bits(&stdvec, &bitvec, &stdvec_mask, &bitvec_mask);

        let stdvec_mask: Vec<bool> = std::iter::repeat(true).take(len - diff).collect();
        let bitvec_mask: SmallBitVec = std::iter::repeat(true).take(len - diff).collect();
        check_gather_bits(&stdvec, &bitvec, &stdvec_mask, &bitvec_mask);
    }
}

#[cfg(target_arch = "x86_64")]
#[test]
fn pext_fallback() {
    if !std::arch::is_x86_feature_detected!("bmi2") {
        return;
    }

    const ITERATIONS: usize = 1000;
    let mut rng = Xoshiro256StarStar::seed_from_u64(0x0123456789abcdef);
    for _ in 0..ITERATIONS {
        let val = rng.r#gen();
        let mask = rng.r#gen();
        let got = crate::bmi2::pext_fallback(val, mask);
        let expected = unsafe { crate::bmi2::pext_x86_64(val as u64, mask as u64) } as usize;
        assert_eq!(got, expected);
    }
}

#[cfg(target_arch = "x86_64")]
#[test]
fn pdep_fallback() {
    if !std::arch::is_x86_feature_detected!("bmi2") {
        return;
    }

    const ITERATIONS: usize = 1000;
    let mut rng = Xoshiro256StarStar::seed_from_u64(0x0123456789abcdef);
    for _ in 0..ITERATIONS {
        let val = rng.r#gen();
        let mask = rng.r#gen();
        let got = crate::bmi2::pdep_fallback(val, mask);
        let expected = unsafe { crate::bmi2::pdep_x86_64(val as u64, mask as u64) } as usize;
        assert_eq!(got, expected);
    }
}

