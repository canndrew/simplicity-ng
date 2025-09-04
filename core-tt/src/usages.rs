use crate::priv_prelude::*;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Usages {
    bits: SmallBitVec,
}

impl Usages {
    /*
    pub fn root() -> Usages {
        let bits = SmallBitVec::new();
        Usages { bits }
    }
    */

    pub fn zeros(ctx_len: usize) -> Usages {
        let bits = iter::repeat(false).take(ctx_len).collect();
        Usages { bits }
    }

    pub fn ones(ctx_len: usize) -> Usages {
        let bits = iter::repeat(true).take(ctx_len).collect();
        Usages { bits }
    }

    pub fn single_one(ctx_len: usize, index: usize) -> Usages {
        let bits = (0..ctx_len).map(|i| i == index).collect();
        Usages { bits }
    }

    pub fn index_of_single_one(&self) -> Option<usize> {
        let mut iter = self.bits.iter().enumerate().filter_map(|(index, bit)| bit.then_some(index));
        let index = iter.next()?;
        if iter.next().is_some() {
            return None;
        }
        Some(index)
    }

    pub fn len(&self) -> usize {
        self.bits.len()
    }

    pub fn merge<const NUM: usize>(ctx_len: usize, usagess: [&Usages; NUM]) -> Usages {
        let bits: SmallBitVec = {
            (0..ctx_len)
            .map(|index| usagess.iter().any(|usages| usages.bits.get(index).unwrap_or(false)))
            .collect()
        };
        Usages { bits }
    }

    pub fn merge_mut<const NUM: usize>(usagess: [&mut Usages; NUM]) -> Usages {
        let usages_len = {
            let (first, rest) = usagess.split_first().unwrap();
            let usages_len = first.len();
            rest.iter().for_each(|usages| assert_eq!(usages.len(), usages_len));
            usages_len
        };
        let bits: SmallBitVec = {
            (0..usages_len)
            .map(|index| usagess.iter().any(|usages| usages.bits[index]))
            .collect()
        };
        for usages in usagess {
            let mut iter = bits.iter();
            usages.bits.retain(|_| iter.next().unwrap());
            usages.bits.shrink_to_fit();
            assert!(iter.next().is_none());
        }
        let new_usages = Usages { bits };
        new_usages
    }

    /*
    pub fn merge_filtered<const NUM: usize>(
        ctx_len: usize,
        usage_filters: [(&Usages, &[&Usages]); NUM],
    ) -> (Usages, [Usages; NUM]) {
        let bits: SmallBitVec = {
            (0..ctx_len)
            .map(|index| usage_filters.iter().any(|(usages, filter)| usages.filter_get(filter, index).unwrap_or(false)))
            .collect()
        };
        let sub_len = bits.count_ones();
        let mut ret = array::from_fn(|_| Usages { bits: SmallBitVec::with_capacity(sub_len) });

        for (index, bit) in bits.iter().enumerate() {
            if bit {
                for ((usages, filter), usages_out) in usage_filters.iter().zip(&mut ret) {
                    let bit = usages.filter_get(filter, index).unwrap_or(false);
                    usages_out.push(bit);
                }
            }
        }
        let new_usages = Usages { bits };
        (new_usages, ret)
    }
    */

    pub fn pop(&mut self) -> bool {
        self.bits.pop().unwrap()
    }

    pub fn count_ones(&self) -> usize {
        self.bits.count_ones()
    }

    pub fn filter(&mut self, usages: &Usages) {
        assert_eq!(self.len(), usages.len());
        let mut write_position = 0;
        for (index, bit) in usages.bits.iter().enumerate().take(self.len()) {
            if bit {
                let bit = self.bits[index];
                self.bits.set(write_position, bit);
                write_position += 1;
            } else {
                assert!(!self.bits[index]);
            }
        }
        self.bits.truncate(write_position);
        assert_eq!(self.len(), usages.count_ones());
    }

    pub fn unfilter(&mut self, usages: &Usages) {
        assert_eq!(usages.count_ones(), self.len());
        let num_new_vars = usages.len().strict_sub(self.len());
        let mut read_position = self.len();
        self.bits.extend(iter::repeat(false).take(num_new_vars));
        for (index, bit) in usages.bits.iter().enumerate().rev() {
            let bit = if bit {
                read_position = read_position.strict_sub(1);
                self.bits[read_position]
            } else {
                false
            };
            self.bits.set(index, bit);
        }
        assert_eq!(read_position, 0);
    }

    pub fn clone_unfilter(&self, usages: &Usages) -> Usages {
        let mut bits = SmallBitVec::with_capacity(usages.len());
        let mut read_index = 0;
        for bit in usages.bits.iter() {
            let bit = bit && {
                let bit = self.bits[read_index];
                read_index += 1;
                bit
            };
            bits.push(bit);
        }
        debug_assert_eq!(read_index, self.bits.len());
        Usages { bits }
    }

    pub fn push(&mut self, bit: bool) {
        self.bits.push(bit);
    }

    pub fn clone_weaken(&self, ext_len: usize) -> Usages {
        let mut ret = self.clone();
        ret.bits.extend(iter::repeat(false).take(ext_len));
        ret
    }

    pub fn weaken(&mut self, ext_len: usize) {
        self.bits.extend(iter::repeat(false).take(ext_len));
    }

    /*
    pub fn from_iter(iter: impl IntoIterator<Item = bool>) -> Usages {
        Usages {
            bits: SmallBitVec::from_iter(iter),
        }
    }

    pub fn clone_push_true(&self) -> Usages {
        let mut bits = SmallBitVec::with_capacity(self.len() + 1);
        bits.extend(self.bits.iter());
        bits.push(true);
        Usages { bits }
    }

    pub fn clone_push_false(&self) -> Usages {
        let mut bits = SmallBitVec::with_capacity(self.len() + 1);
        bits.extend(self.bits.iter());
        bits.push(false);
        Usages { bits }
    }

    pub fn ones_then_zero(len: usize) -> Usages {
        let mut bits = SmallBitVec::with_capacity(len + 1);
        bits.extend(iter::repeat(false).take(len));
        bits.push(true);
        Usages { bits }
    }

    pub fn zeros_then_one(len: usize) -> Usages {
        let mut bits = SmallBitVec::with_capacity(len + 1);
        bits.extend(iter::repeat(true).take(len));
        bits.push(false);
        Usages { bits }
    }

    pub fn filter_get(&self, filter: &[&Usages], index: usize) -> Option<bool> {
        let mut usages = self;
        let mut index = index;
        let mut bit = usages.bits.get(index)?;

        for next_usages in filter {
            if !bit {
                return Some(false);
            }
            index = usages.bits.iter().take(index).filter(|bit| *bit).count();
            usages = next_usages;
            bit = usages[index];
        }
        Some(bit)
    }

    pub fn filter_eq(usages_0: &Usages, filter_0: &[&Usages], usages_1: &Usages, filter_1: &[&Usages]) -> bool {
        let mut index = 0;
        loop {
            match (usages_0.filter_get(filter_0, index), usages_1.filter_get(filter_1, index)) {
                (None, None) => break true,

                (Some(true), None) |
                (None, Some(true)) |
                (Some(false), Some(true)) |
                (Some(true), Some(false)) => break false,

                (Some(false), None) |
                (None, Some(false)) |
                (Some(false), Some(false)) |
                (Some(true), Some(true)) => (),
            }
            index += 1;
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = bool> {
        self.bits.iter()
    }

    pub fn extend(&mut self, iter: impl IntoIterator<Item = bool>) {
        self.bits.extend(iter)
    }
    */

    pub fn clone_filter(&self, usages: &Usages) -> Usages {
        let sub_len = usages.count_ones();
        let mut bits = SmallBitVec::with_capacity(sub_len);

        let mut iter = usages.bits.iter();
        for (read_index, bit) in iter.by_ref().take(self.bits.len()).enumerate() {
            if bit {
                let bit = self.bits[read_index];
                bits.push(bit);
            }
        }
        /*
        for bit in iter {
            if bit {
                bits.push(false);
            }
        }
        */
        Usages { bits }
    }

    pub fn subst<N: Name>(&self, filter: &Usages, var_term: &RawTm<N>) -> ControlFlow<Usages, (Usages, Usages, RawTm<N>)> {
        let var_term_num_usages = var_term.usages.bits.len();
        let mut self_usages = self.clone_unfilter(filter);
        if self_usages.bits[var_term_num_usages] {
            let mut merged = Usages::merge(filter.bits.len(), [&self_usages, &var_term.usages]);
            self_usages.filter(&merged);
            let sub_var_term = var_term.clone_filter(&merged);
            merged.bits.remove(var_term_num_usages);
            ControlFlow::Continue((merged, self_usages, sub_var_term))
        } else {
            self_usages.bits.remove(var_term_num_usages);
            ControlFlow::Break(self_usages)
        }
    }
}

impl ops::Index<usize> for Usages {
    type Output = bool;

    fn index(&self, index: usize) -> &bool {
        &self.bits[index]
    }
}

impl fmt::Debug for Usages {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.bits, f)
    }
}

