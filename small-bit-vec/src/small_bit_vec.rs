use std::{
    cmp, fmt, hash, iter, ops, slice,
    ptr::NonNull,
};

/* 
 * FIXME: A lot of code here is stupidly inefficient just because it was the
 * quickest/easiest/safest way to write it. If you're looking for things to optimize, start here.
 */


const USIZE_BITS: usize = usize::BITS as usize;

pub struct SmallBitVec {
    capacity_or_inline_len: usize,
    storage: Storage,
}

unsafe impl Send for SmallBitVec {}
unsafe impl Sync for SmallBitVec {}

union Storage {
    inline: usize,
    heap: NonNull<usize>,
}

impl PartialEq<SmallBitVec> for SmallBitVec {
    fn eq(&self, other: &SmallBitVec) -> bool {
        if self.len() != other.len() {
            return false;
        }
        let slice_0 = self.as_usize_slice();
        let slice_1 = other.as_usize_slice();
        slice_0 == slice_1
    }
}

impl Eq for SmallBitVec {}

impl PartialOrd for SmallBitVec {
    fn partial_cmp(&self, other: &SmallBitVec) -> Option<cmp::Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl Ord for SmallBitVec {
    fn cmp(&self, other: &SmallBitVec) -> cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl hash::Hash for SmallBitVec {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: hash::Hasher,
    {
        hasher.write_usize(self.len());
        hash::Hash::hash(self.as_usize_slice(), hasher);
    }
}

impl Clone for SmallBitVec {
    fn clone(&self) -> SmallBitVec {
        let words = self.as_usize_slice();
        SmallBitVec::from_usize_slice_and_len(words, self.len())
    }
}

impl Drop for SmallBitVec {
    fn drop(&mut self) {
        if !self.is_inline() {
            unsafe {
                let (ptr, len, capacity) = self.heap_vec_parts();
                let vec = Vec::from_raw_parts(ptr, len, capacity);
                drop(vec);
            }
        }
    }
}

impl SmallBitVec {
    pub fn new() -> SmallBitVec {
        SmallBitVec {
            capacity_or_inline_len: 0,
            storage: Storage { inline: 0 },
        }
    }

    pub fn with_capacity(capacity: usize) -> SmallBitVec {
        if capacity <= USIZE_BITS {
            SmallBitVec::new()
        } else {
            let mut vec = Vec::with_capacity(capacity.div_ceil(USIZE_BITS) + 1);
            vec.push(0);
            unsafe { SmallBitVec::from_heap_vec(vec) }
        }
    }

    pub fn from_usize_and_len(bits: usize, len: usize) -> SmallBitVec {
        assert!(len <= USIZE_BITS);
        let bits = mask_bits(bits, len);
        SmallBitVec {
            capacity_or_inline_len: len,
            storage: Storage { inline: bits },
        }
    }

    pub fn from_usize_slice_and_len(slice: &[usize], len: usize) -> SmallBitVec {
        assert!(len <= USIZE_BITS * slice.len());
        let slice = &slice[..len.div_ceil(USIZE_BITS)];
        match slice.split_first() {
            None => SmallBitVec::new(),
            Some((bits, remaining)) => {
                if remaining.is_empty() {
                    SmallBitVec::from_usize_and_len(*bits, len)
                } else {
                    let mut vec = Vec::with_capacity(1 + slice.len());
                    vec.push(len);
                    vec.extend(slice);
                    let mask_len = (len + USIZE_BITS - 1) % USIZE_BITS + 1;
                    let last = vec.last_mut().unwrap();
                    *last = mask_bits(*last, mask_len);
                    unsafe { SmallBitVec::from_heap_vec(vec) }
                }
            },
        }
    }

    pub fn len(&self) -> usize {
        if self.is_inline() {
            self.capacity_or_inline_len
        } else {
            unsafe { self.storage.heap.read() }
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn capacity(&self) -> usize {
        if self.is_inline() {
            USIZE_BITS
        } else {
            self.capacity_or_inline_len
        }
    }

    unsafe fn from_heap_vec(heap_vec: Vec<usize>) -> SmallBitVec {
        let len_bits = heap_vec[0];
        debug_assert_eq!(
            0,
            *heap_vec.last().unwrap() & (!0usize).unbounded_shl(((len_bits + USIZE_BITS - 1) % USIZE_BITS + 1) as u32),
            "len_bits == {}; heap_vec.len() == {}; heap_vec.last() == {}", len_bits, heap_vec.len(), heap_vec.last().unwrap(),
        );
        let (ptr, len, capacity) = heap_vec.into_raw_parts();
        debug_assert_eq!(1 + len_bits.div_ceil(USIZE_BITS), len);
        debug_assert!(capacity > 2);

        let heap = unsafe { NonNull::new_unchecked(ptr) };
        let storage = Storage { heap };
        let capacity_or_inline_len = (capacity - 1) * USIZE_BITS;
        SmallBitVec { capacity_or_inline_len, storage }
    }

    fn is_inline(&self) -> bool {
        self.capacity_or_inline_len <= USIZE_BITS
    }

    unsafe fn heap_vec_parts(&self) -> (*mut usize, usize, usize) {
        unsafe {
            let ptr = self.storage.heap.as_ptr();
            let len = 1 + ptr.read().div_ceil(USIZE_BITS);
            let capacity = 1 + self.capacity_or_inline_len / USIZE_BITS;
            (ptr, len, capacity)
        }
    }

    unsafe fn get_heap_slice(&self) -> &[usize] {
        unsafe {
            let (ptr, len, _capacity) = self.heap_vec_parts();
            slice::from_raw_parts(ptr.add(1), len.unchecked_sub(1))
        }
    }

    unsafe fn get_heap_slice_mut(&mut self) -> &mut [usize] {
        unsafe {
            let (ptr, len, _capacity) = self.heap_vec_parts();
            slice::from_raw_parts_mut(ptr.add(1), len.unchecked_sub(1))
        }
    }

    pub fn as_usize_slice(&self) -> &[usize] {
        if self.is_inline() {
            if self.capacity_or_inline_len == 0 {
                &[]
            } else {
                let inline = unsafe { &self.storage.inline };
                slice::from_ref(inline)
            }
        } else {
            unsafe { self.get_heap_slice() }
        }
    }

    unsafe fn with_heap_vec<R>(&mut self, func: impl FnOnce(&mut Vec<usize>) -> R) -> R {
        unsafe {
            let (ptr, len, capacity) = self.heap_vec_parts();
            let mut vec = Vec::from_raw_parts(ptr, len, capacity);

            // leak the bitvec in case of panic
            self.capacity_or_inline_len = 0;

            let ret = func(&mut vec);

            let new_self = SmallBitVec::from_heap_vec(vec);
            std::ptr::write(self, new_self);

            ret
        }
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        if !(index < self.len()) {
            return None;
        }
        if self.is_inline() {
            let bits = unsafe { self.storage.inline };
            Some(usize_get_bit(bits, index))
        } else {
            let slice = unsafe { self.get_heap_slice() };
            let (word_index, bit_index) = div_mod(index, USIZE_BITS);
            Some(usize_get_bit(slice[word_index], bit_index))
        }
    }

    pub fn set(&mut self, index: usize, bit: bool) {
        assert!(index < self.len());
        if self.is_inline() {
            let word = unsafe { &mut self.storage.inline };
            usize_set_bit(word, index, bit);
        } else {
            let slice = unsafe { self.get_heap_slice_mut() };
            let (word_index, bit_index) = div_mod(index, USIZE_BITS);
            usize_set_bit(&mut slice[word_index], bit_index, bit);
        }
    }

    pub fn push(&mut self, bit: bool) {
        match self.capacity_or_inline_len.cmp(&USIZE_BITS) {
            cmp::Ordering::Less => {
                let inline = unsafe { &mut self.storage.inline };
                usize_set_bit(inline, self.capacity_or_inline_len, bit);
                self.capacity_or_inline_len += 1;
            },
            cmp::Ordering::Equal => {
                let inline = unsafe { self.storage.inline };
                let heap = vec![USIZE_BITS + 1, inline, bit as usize];
                *self = unsafe { SmallBitVec::from_heap_vec(heap) };
            },
            cmp::Ordering::Greater => {
                let len = unsafe { self.storage.heap.read() };
                let (word_index, bit_index) = div_mod(len, USIZE_BITS);
                unsafe {
                    self.with_heap_vec(|vec| {
                        if bit_index == 0 {
                            vec.push(bit as usize);
                        } else {
                            usize_set_bit(&mut vec[1 + word_index], bit_index, bit);
                        }
                        vec[0] += 1;
                    });
                }
            },
        }
    }

    pub fn pop(&mut self) -> Option<bool> {
        let new_len = self.len().checked_sub(1)?;
        if self.is_inline() {
            let inline = unsafe { &mut self.storage.inline };
            let ret = usize_get_bit(*inline, new_len);
            usize_set_bit(inline, new_len, false);
            self.capacity_or_inline_len = new_len;
            Some(ret)
        } else {
            let bit_index = new_len % USIZE_BITS;
            unsafe {
                let ret = self.with_heap_vec(|vec| {
                    vec[0] -= 1;
                    if bit_index == 0 {
                        vec.pop().unwrap() & 1 == 1
                    } else {
                        let last = vec.last_mut().unwrap();
                        let ret = usize_get_bit(*last, bit_index);
                        usize_set_bit(last, bit_index, false);
                        ret
                    }
                });
                Some(ret)
            }
        }
    }

    pub fn first(&self) -> Option<bool> {
        let slice = self.as_usize_slice();
        let word = *slice.first()?;
        Some((word & 1) == 1)
    }

    pub fn last(&self) -> Option<bool> {
        let slice = self.as_usize_slice();
        let word = *slice.last()?;
        let bit_index = (self.len() + USIZE_BITS - 1) % USIZE_BITS;
        Some(usize_get_bit(word, bit_index))
    }

    pub fn truncate(&mut self, len: usize) {
        if len > self.len() {
            return;
        }
        if self.is_inline() {
            self.capacity_or_inline_len = len;
            let inline = unsafe { self.storage.inline };
            self.storage = Storage { inline: mask_bits(inline, len) };
        } else {
            unsafe {
                let len_words = 1 + len.div_ceil(USIZE_BITS);
                let remaining_bits = (len + USIZE_BITS - 1) % USIZE_BITS + 1;
                self.with_heap_vec(|vec| {
                    vec[0] = len;
                    vec.truncate(len_words);
                    let last = vec.last_mut().unwrap();
                    *last = mask_bits(*last, remaining_bits);
                })
            }
        }
    }

    pub fn count_zeros(&self) -> usize {
        self.len() - self.count_ones()
    }

    pub fn count_ones(&self) -> usize {
        let slice = self.as_usize_slice();
        slice.iter().map(|val| val.count_ones() as usize).sum()
    }

    pub fn iter(&self) -> Iter<'_> {
        Iter {
            position: 0,
            len: self.len(),
            slice: self.as_usize_slice(),
        }
    }

    pub fn into_iter(self) -> IntoIter {
        IntoIter {
            position: 0,
            small_bit_vec: self,
        }
    }

    pub fn insert(&mut self, index: usize, bit: bool) {
        let len = self.len();
        assert!(index <= len);
        self.push(false);
        for index in (index..len).rev() {
            let bit = self[index];
            self.set(index + 1, bit);
        }
        self.set(index, bit);
    }

    pub fn remove(&mut self, index: usize) -> bool {
        assert!(index < self.len());
        if self.is_inline() {
            let inline = unsafe { self.storage.inline };
            let ret = (inline >> index) & 1 == 1;
            let lower_bits = mask_bits(inline, index);
            let upper_bits = inline.unbounded_shr((index + 1) as u32) << index;
            self.storage = Storage { inline: lower_bits | upper_bits };
            self.capacity_or_inline_len -= 1;
            ret
        } else {
            unsafe {
                self.with_heap_vec(|vec| {
                    let (word_index, bit_index) = div_mod(index, USIZE_BITS);
                    let ret = usize_get_bit(vec[1 + word_index], bit_index);
                    let lower_bits = mask_bits(vec[1 + word_index], bit_index);
                    let upper_bits = vec[1 + word_index].unbounded_shr((bit_index + 1) as u32) << bit_index;
                    vec[1 + word_index] = lower_bits | upper_bits;
                    for index in (1 + word_index)..(vec.len() - 1) {
                        vec[index] |= (vec[index + 1] & 1) << (USIZE_BITS - 1);
                        vec[index + 1] >>= 1;
                    }
                    vec[0] -= 1;
                    if vec[0] % USIZE_BITS == 0 {
                        vec.pop();
                    }
                    ret
                })
            }
        }
    }

    pub fn retain(&mut self, mut predicate: impl FnMut(bool) -> bool) {
        let mut write_index = 0;
        for read_index in 0..self.len() {
            let bit = self[read_index];
            if predicate(bit) {
                self.set(write_index, bit);
                write_index += 1;
            }
        }
        self.truncate(write_index);
    }

    pub fn shrink_to_fit(&mut self) {
        if self.is_inline() {
            return;
        }
        let len_inline_opt = unsafe {
            self.with_heap_vec(|vec| {
                if vec.len() <= 2 {
                    Some((vec[0], vec.get(1).copied().unwrap_or(0)))
                } else {
                    vec.shrink_to_fit();
                    None
                }
            })
        };
        if let Some((len, inline)) = len_inline_opt {
            *self = SmallBitVec {
                capacity_or_inline_len: len,
                storage: Storage { inline },
            };
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        let required = self.len() + additional;
        if required <= self.capacity() {
            return;
        }
        let required_words = 1 + required.div_ceil(USIZE_BITS);
        if self.is_inline() {
            let inline = unsafe { self.storage.inline };
            let mut vec = Vec::with_capacity(required_words);
            vec.push(self.capacity_or_inline_len);
            if self.capacity_or_inline_len != 0 {
                vec.push(inline);
            }
            *self = unsafe { SmallBitVec::from_heap_vec(vec) };
        } else {
            unsafe {
                self.with_heap_vec(|vec| {
                    let additional = required_words.saturating_sub(vec.len());
                    vec.reserve(additional);
                })
            }
        }
    }
}

pub struct Iter<'a> {
    position: usize,
    len: usize,
    slice: &'a [usize],
}

impl<'a> Iterator for Iter<'a> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.position == self.len {
            return None;
        }
        let (word_index, bit_index) = div_mod(self.position, USIZE_BITS);
        self.position += 1;
        Some(usize_get_bit(self.slice[word_index], bit_index))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.len - self.position;
        (remaining, Some(remaining))
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    fn next_back(&mut self) -> Option<bool> {
        if self.position == self.len {
            return None;
        }
        self.len -= 1;
        let (word_index, bit_index) = div_mod(self.len, USIZE_BITS);
        Some(usize_get_bit(self.slice[word_index], bit_index))
    }
}

impl<'a> ExactSizeIterator for Iter<'a> {}
impl<'a> iter::FusedIterator for Iter<'a> {}

pub struct IntoIter {
    position: usize,
    small_bit_vec: SmallBitVec,
}

impl Iterator for IntoIter {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        let bit = self.small_bit_vec.get(self.position)?;
        self.position += 1;
        Some(bit)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.small_bit_vec.len() - self.position;
        (remaining, Some(remaining))
    }
}

impl DoubleEndedIterator for IntoIter {
    fn next_back(&mut self) -> Option<bool> {
        self.small_bit_vec.pop()
    }
}

impl ExactSizeIterator for IntoIter {}
impl iter::FusedIterator for IntoIter {}

impl FromIterator<bool> for SmallBitVec {
    fn from_iter<I>(iter: I) -> SmallBitVec
    where
        I: IntoIterator<Item = bool>,
    {
        /*
        
            Note: this code works but wasn't a performance improvement

        let mut iter = iter.into_iter();
        let mut num_bits = 0;
        let mut bits = 0;
        while num_bits < USIZE_BITS {
            match iter.next() {
                None => return SmallBitVec {
                    capacity_or_inline_len: num_bits,
                    storage: Storage { inline: bits },
                },
                Some(bit) => {
                    bits |= (bit as usize) << num_bits;
                    num_bits += 1;
                },
            }
        }
        let bit = match iter.next() {
            None => return SmallBitVec {
                capacity_or_inline_len: USIZE_BITS,
                storage: Storage { inline: bits },
            },
            Some(bit) => bit,
        };
        let (lower, _) = iter.size_hint();
        let mut heap_vec = Vec::with_capacity((lower + 1).div_ceil(USIZE_BITS) + 2);
        heap_vec.extend([0, bits, bit as usize]);
        let mut word_index = 1;
        let mut bit_index = 1;
        loop {
            while bit_index < USIZE_BITS {
                match iter.next() {
                    None => {
                        heap_vec[0] = bit_index + word_index * USIZE_BITS;
                        return unsafe {
                            SmallBitVec::from_heap_vec(heap_vec)
                        };
                    },
                    Some(bit) => {
                        heap_vec[word_index + 1] |= (bit as usize) << bit_index;
                        bit_index += 1;
                    },
                }
            }
            match iter.next() {
                None => {
                    heap_vec[0] = bit_index + word_index * USIZE_BITS;
                    return unsafe {
                        SmallBitVec::from_heap_vec(heap_vec)
                    };
                },
                Some(bit) => {
                    bit_index = 1;
                    word_index += 1;
                    heap_vec.push(bit as usize);
                },
            }
        }
        */



        let iter = iter.into_iter();
        let (lower, _) = iter.size_hint();
        let mut ret = SmallBitVec::with_capacity(lower);
        for bit in iter {
            ret.push(bit);
        }
        ret
    }
}

impl Default for SmallBitVec {
    fn default() -> SmallBitVec {
        SmallBitVec::new()
    }
}

impl ops::Index<usize> for SmallBitVec {
    type Output = bool;

    fn index(&self, index: usize) -> &bool {
        if self.get(index).unwrap() { &true } else { &false }
    }
}

impl Extend<bool> for SmallBitVec {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = bool>,
    {
        let iter = iter.into_iter();
        let (lower, _) = iter.size_hint();
        self.reserve(lower);
        for bit in iter {
            self.push(bit);
        }
    }
}

impl IntoIterator for SmallBitVec {
    type IntoIter = IntoIter;
    type Item = bool;

    fn into_iter(self) -> IntoIter {
        self.into_iter()
    }
}

impl<'a> IntoIterator for &'a SmallBitVec {
    type IntoIter = Iter<'a>;
    type Item = bool;

    fn into_iter(self) -> Iter<'a> {
        self.iter()
    }
}

impl fmt::Debug for SmallBitVec {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for bit in self.iter() {
            if bit {
                write!(f, "1")?;
            } else {
                write!(f, "0")?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}

impl<const LEN: usize> PartialEq<[bool; LEN]> for SmallBitVec {
    fn eq(&self, rhs: &[bool; LEN]) -> bool {
        self.iter().eq(rhs.iter().copied())
    }
}

impl<const LEN: usize> PartialEq<&[bool; LEN]> for SmallBitVec {
    fn eq(&self, rhs: &&[bool; LEN]) -> bool {
        self.iter().eq(rhs.iter().copied())
    }
}

impl PartialEq<[bool]> for SmallBitVec {
    fn eq(&self, rhs: &[bool]) -> bool {
        self.iter().eq(rhs.iter().copied())
    }
}

impl PartialEq<&[bool]> for SmallBitVec {
    fn eq(&self, rhs: &&[bool]) -> bool {
        self.iter().eq(rhs.iter().copied())
    }
}

#[inline]
fn div_mod(x: usize, y: usize) -> (usize, usize) {
    let d = x / y;
    let m = x % y;
    (d, m)
}

#[inline]
fn usize_set_bit(word: &mut usize, bit_index: usize, bit: bool) {
    if bit {
        *word |= 1 << bit_index;
    } else {
        *word &= !(1 << bit_index);
    }
}

#[inline]
fn usize_get_bit(word: usize, bit_index: usize) -> bool {
    (word >> bit_index) & 1 == 1
}

#[inline]
fn mask_bits(word: usize, bits: usize) -> usize {
    word & !((!0usize).unbounded_shl(bits as u32))
}

