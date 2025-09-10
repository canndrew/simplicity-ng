use {
    crate::SmallBitVec,
    rand::{Rng, SeedableRng},
    rand_xoshiro::Xoshiro256StarStar,
};

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

