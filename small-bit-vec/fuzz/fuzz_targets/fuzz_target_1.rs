#![no_main]

use {
    std::iter,
    libfuzzer_sys::fuzz_target,
    arbitrary::Arbitrary,
    small_bit_vec::SmallBitVec,
};

#[derive(Arbitrary, Debug)]
enum Method {
    New,
    WithCapacity {
        capacity: usize,
    },
    FromUsizeAndLen {
        bits: usize,
        len: usize,
    },
    FromUsizeSliceAndLen {
        slice: Vec<usize>,
        len: usize,
    },
    Len,
    IsEmpty,
    Capacity,
    AsUsizeSlice,
    Get {
        index: usize,
    },
    Set {
        index: usize,
        bit: bool,
    },
    Push {
        bit: bool,
    },
    Pop,
    Truncate {
        len: usize,
    },
    CountOnes,
    Iter,
    Insert {
        index: usize,
        bit: bool,
    },
    Remove {
        index: usize,
    },
    ShrinkToFit,
    Reserve {
        additional: usize,
    },
    Clone,
    PartialEq,
    PartialOrd,
    Drop,
    Extend {
        bits: Vec<bool>,
    },
}

fn iter_bits(val: usize) -> impl Iterator<Item = bool> {
    let mut index = 0;
    iter::from_fn(move || {
        if index == usize::BITS as usize {
            None
        } else {
            let ret = (val >> index) & 1 == 1;
            index += 1;
            Some(ret)
        }
    })
}

fn from_iter(iter: impl IntoIterator<Item = bool>) -> usize {
    let mut index = 0;
    let mut ret = 0;
    for bit in iter {
        ret |= (bit as usize) << index;
        index += 1;
    }
    ret
}

impl Method {
    fn perform(&self, vecs: &mut Vec<(SmallBitVec, Vec<bool>)>) {
        match self {
            Method::New => {
                vecs.push((
                    SmallBitVec::new(), 
                    Vec::new(),
                ));
            },
            Method::WithCapacity { capacity } => {
                let capacity = capacity % 0x100_000;
                vecs.push((
                    SmallBitVec::with_capacity(capacity),
                    Vec::new(),
                ));
            },
            Method::FromUsizeAndLen { bits, len } => {
                let len = len % (usize::BITS as usize);
                vecs.push((
                    SmallBitVec::from_usize_and_len(*bits, len),
                    iter_bits(*bits).take(len).collect(),
                ));
            },
            Method::FromUsizeSliceAndLen { slice, len } => {
                let len = len % (1 + slice.len() * (usize::BITS as usize));
                vecs.push((
                    SmallBitVec::from_usize_slice_and_len(slice, len),
                    slice.iter().copied().flat_map(iter_bits).take(len).collect(),
                ));
            },
            Method::Len => {
                if let Some((bvec, svec)) = vecs.last() {
                    let len_0 = bvec.len();
                    let len_1 = svec.len();
                    assert_eq!(len_0, len_1);
                }
            },
            Method::IsEmpty => {
                if let Some((bvec, svec)) = vecs.last() {
                    let v0 = bvec.is_empty();
                    let v1 = svec.is_empty();
                    assert_eq!(v0, v1);
                }
            },
            Method::Capacity => {
                if let Some((bvec, _svec)) = vecs.last() {
                    let _ = bvec.capacity();
                }
            },
            Method::AsUsizeSlice => {
                if let Some((bvec, svec)) = vecs.last() {
                    let slice_0 = bvec.as_usize_slice();
                    let vec_1: Vec<usize> = {
                        svec
                        .chunks(usize::BITS as usize)
                        .map(|slice| from_iter(slice.iter().copied()))
                        .collect()
                    };
                    match slice_0.split_last() {
                        None => assert!(vec_1.is_empty()),
                        Some((word_0, prefix_0)) => {
                            let (word_1, prefix_1) = vec_1.split_last().unwrap();
                            assert_eq!(prefix_0, prefix_1);
                            let mask = !(!0 << bvec.len() % usize::BITS as usize);
                            assert_eq!(mask & word_0, mask & word_1);
                        },
                    }
                }
            },
            Method::Get { index } => {
                if let Some((bvec, svec)) = vecs.last() && let Some(index) = index.checked_rem(bvec.len()) {
                    let v0 = bvec.get(index);
                    let v1 = svec.get(index).copied();
                    assert_eq!(v0, v1);
                }
            },
            Method::Set { index, bit } => {
                if let Some((bvec, svec)) = vecs.last_mut() && let Some(index) = index.checked_rem(bvec.len()) {
                    bvec.set(index, *bit);
                    svec[index] = *bit;
                }
            },
            Method::Push { bit } => {
                if let Some((bvec, svec)) = vecs.last_mut() {
                    bvec.push(*bit);
                    svec.push(*bit);
                }
            },
            Method::Pop => {
                if let Some((bvec, svec)) = vecs.last_mut() {
                    let v0 = bvec.pop();
                    let v1 = svec.pop();
                    assert_eq!(v0, v1);
                }
            },
            Method::Truncate { len } => {
                if let Some((bvec, svec)) = vecs.last_mut() {
                    bvec.truncate(*len);
                    svec.truncate(*len);
                }
            },
            Method::CountOnes => {
                if let Some((bvec, svec)) = vecs.last() {
                    let v0 = bvec.count_ones();
                    let v1 = svec.iter().copied().filter(|bit| *bit).count();
                    assert_eq!(v0, v1);
                }
            },
            Method::Iter => {
                if let Some((bvec, svec)) = vecs.last() {
                    let iter0 = bvec.iter();
                    let iter1 = svec.iter().copied();
                    assert!(iter0.eq(iter1));
                }
            },
            Method::Insert { index, bit } => {
                if let Some((bvec, svec)) = vecs.last_mut() && let Some(index) = index.checked_rem(bvec.len()) {
                    bvec.insert(index, *bit);
                    svec.insert(index, *bit);
                }
            },
            Method::Remove { index } => {
                if let Some((bvec, svec)) = vecs.last_mut() && let Some(index) = index.checked_rem(bvec.len()) {
                    let v0 = bvec.remove(index);
                    let v1 = svec.remove(index);
                    assert_eq!(v0, v1);
                }
            },
            Method::ShrinkToFit => {
                if let Some((bvec, _svec)) = vecs.last_mut() {
                    bvec.shrink_to_fit();
                }
            },
            Method::Reserve { additional } => {
                if let Some((bvec, _svec)) = vecs.last_mut() {
                    let additional = additional % 0x100_000;
                    bvec.reserve(additional);
                }
            },
            Method::Clone => {
                if let Some((bvec, svec)) = vecs.last() {
                    let bvec = bvec.clone();
                    let svec = svec.clone();
                    vecs.push((bvec, svec));
                }
            },
            Method::PartialEq => {
                let len = vecs.len();
                if let Some(i0) = len.checked_sub(1) && let Some(i1) = len.checked_sub(2) {
                    let (bvec0, svec0) = &vecs[i0];
                    let (bvec1, svec1) = &vecs[i1];
                    let v0 = bvec0 == bvec1;
                    let v1 = svec0 == svec1;
                    assert_eq!(v0, v1);
                }
            },
            Method::PartialOrd => {
                let len = vecs.len();
                if let Some(i0) = len.checked_sub(1) && let Some(i1) = len.checked_sub(2) {
                    let (bvec0, svec0) = &vecs[i0];
                    let (bvec1, svec1) = &vecs[i1];
                    let v0 = bvec0.partial_cmp(bvec1);
                    let v1 = svec0.partial_cmp(svec1);
                    assert_eq!(v0, v1);
                }
            },
            Method::Drop => {
                let _ = vecs.pop();
            },
            Method::Extend { bits } => {
                if let Some((bvec, svec)) = vecs.last_mut() {
                    bvec.extend(bits.iter().copied());
                    svec.extend(bits);
                }
            },
        }
    }
}

fuzz_target!(|methods: Vec<Method>| {
    let mut vecs = Vec::new();
    for method in methods {
        //println!("{:?}", method);
        method.perform(&mut vecs);
    }
});


