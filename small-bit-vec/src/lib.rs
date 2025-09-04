#![feature(vec_into_raw_parts)]

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
        let (full_words, remaining_bits) = div_mod(self.len(), USIZE_BITS);
        if slice_0[..full_words] != slice_1[..full_words] {
            return false;
        }
        if remaining_bits == 0 {
            return true;
        }
        let word_0 = slice_0.last().unwrap();
        let word_1 = slice_1.last().unwrap();
        (word_0 ^ word_1) & !((!0) << remaining_bits) == 0
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
        if self.is_inline() {
            SmallBitVec {
                capacity_or_inline_len: self.capacity_or_inline_len,
                storage: Storage {
                    inline: unsafe { self.storage.inline },
                },
            }
        } else {
            let slice = unsafe { self.get_heap_slice() };
            let mut vec = Vec::with_capacity(slice.len() + 1);
            vec.push(self.len());
            vec.extend(slice);
            unsafe { SmallBitVec::from_heap_vec(vec) }
        }
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
        SmallBitVec {
            capacity_or_inline_len: len,
            storage: Storage { inline: bits },
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
            let inline = unsafe { &self.storage.inline };
            slice::from_ref(inline)
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
            let word = unsafe { self.storage.inline };
            let ret = usize_get_bit(word, new_len);
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
                        usize_get_bit(*vec.last().unwrap(), bit_index)
                    }
                });
                Some(ret)
            }
        }
    }

    pub fn truncate(&mut self, len: usize) {
        if len > self.len() {
            return;
        }
        if self.is_inline() {
            self.capacity_or_inline_len = len;
        } else {
            unsafe {
                let len_words = 1 + len.div_ceil(USIZE_BITS);
                self.with_heap_vec(|vec| {
                    vec[0] = len;
                    vec.truncate(len_words);
                })
            }
        }
    }

    pub fn count_ones(&self) -> usize {
        self.iter().filter(|bit| *bit).count()
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
        let len = self.len();
        let ret = self[index];
        for index in index..(len - 1) {
            let bit = self[index + 1];
            self.set(index, bit);
        }
        self.pop().unwrap();
        ret
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
            vec.push(inline);
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

fn usize_set_bit(word: &mut usize, bit_index: usize, bit: bool) {
    if bit {
        *word |= 1 << bit_index;
    } else {
        *word &= !(1 << bit_index);
    }
}

fn usize_get_bit(word: usize, bit_index: usize) -> bool {
    (word >> bit_index) & 1 == 1
}

