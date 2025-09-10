use crate::priv_prelude::*;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Usages {
    bits: SmallBitVec,
}

impl Usages {
    pub fn root() -> Usages {
        let bits = SmallBitVec::new();
        Usages { bits }
    }

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

    pub fn or_assign_prefix(&mut self, usages: &Usages) {
        for index in 0..usages.len() {
            let bit = self.bits[index] || usages.bits[index];
            self.bits.set(index, bit);
        }
    }

    pub fn or_assign(&mut self, usages: &Usages) {
        debug_assert_eq!(self.len(), usages.len());
        for index in 0..self.len() {
            let bit = self.bits[index] || usages.bits[index];
            self.bits.set(index, bit);
        }
    }

    pub fn pop(&mut self) -> bool {
        self.bits.pop().unwrap()
    }

    pub fn last(&self) -> bool {
        self.bits.last().unwrap()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn is_zeros(&self) -> bool {
        self.bits.iter().all(|bit| !bit)
    }

    pub fn is_ones(&self) -> bool {
        self.bits.iter().all(|bit| bit)
    }

    pub fn is_single(&self, index: usize) -> bool {
        self.bits.iter().enumerate().all(|(i, bit)| (i == index) == bit)
    }

    pub fn count_ones(&self) -> usize {
        self.bits.count_ones()
    }

    pub fn clone_filter_prefix(&self, ctx_len: usize, usages: &Usages) -> Usages {
        assert_eq!(self.len(), ctx_len);
        let sub_len = usages.bits.iter().take(ctx_len).filter(|bit| *bit).count();
        let mut bits = SmallBitVec::with_capacity(sub_len);
        for (index, bit) in usages.bits.iter().enumerate().take(ctx_len) {
            if bit {
                let bit = self.bits[index];
                bits.push(bit);
            } else {
                debug_assert!(!self.bits[index]);
            }
        }
        Usages { bits }
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

    pub fn zero_unused(&mut self, usages: &Usages) {
        assert_eq!(self.count_ones(), usages.len());
        let mut read_index = 0;
        for index in 0..self.len() {
            if self.bits[index] {
                self.bits.set(index, usages.bits[read_index]);
                read_index += 1;
            }
        }
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
    */

    pub fn iter(&self) -> impl Iterator<Item = bool> {
        self.bits.iter()
    }

    pub fn extend(&mut self, iter: impl IntoIterator<Item = bool>) {
        self.bits.extend(iter)
    }

    pub fn remove(&mut self, index: usize) {
        self.bits.remove(index);
    }

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

    pub fn subst<S: Scheme>(
        &self,
        filter: &Usages,
        var_term: &RawTm<S>,
    ) -> ControlFlow<Usages, (Usages, Usages, RawTm<S>)> {
        let var_term_num_usages = var_term.usages.bits.len();
        let mut self_usages = self.clone_unfilter(filter);
        if self_usages.bits[var_term_num_usages] {
            if let RawTmKind::Stuck { stuck } = var_term.weak.get_clone()
            && let RawStuckKind::Var = stuck.weak.get_clone()
            && let new_index = var_term.usages.index_of_single_one().unwrap()
            && (new_index..var_term_num_usages).all(|index| !self_usages.bits[index])
            {
                self_usages.bits.remove(var_term_num_usages);
                self_usages.bits.set(new_index, true);
                ControlFlow::Break(self_usages)
            } else {
                let mut merged = Usages::merge(filter.bits.len(), [&self_usages, &var_term.usages]);
                self_usages.filter(&merged);
                let sub_var_term = var_term.clone_filter(&merged);
                merged.bits.remove(var_term_num_usages);
                ControlFlow::Continue((merged, self_usages, sub_var_term))
            }
        } else {
            self_usages.bits.remove(var_term_num_usages);
            ControlFlow::Break(self_usages)
        }
    }

    pub fn strengthenable(&self, index: usize) -> bool {
        assert!(index <= self.bits.len());
        self.bits.iter().skip(index).all(|bit| !bit)
    }

    pub fn try_strengthen(&self, index: usize) -> Option<Usages> {
        debug_assert!(index <= self.bits.len());
        if self.bits.iter().skip(index).all(|bit| !bit) {
            let bits = SmallBitVec::from_iter(self.bits.iter().take(index));
            Some(Usages { bits })
        } else {
            None
        }
    }

    pub fn split_eta<S: Scheme>(
        &self,
        filter: &Usages,
        elim: &RawStuck<S>,
    ) -> Option<ControlFlow<Usages, (Usages, Usages, RawStuck<S>)>> {
        debug_assert_eq!(filter.len(), elim.usages.len());
        debug_assert!(filter.bits.iter().zip(elim.usages.bits.iter()).all(|(bit0, bit1)| bit0 || bit1));

        let num_ones = filter.count_ones();
        if !self.bits[num_ones] && !self.bits[num_ones + 1] {
            let mut self_bits = self.bits.iter();
            let mut new_self_bits = SmallBitVec::new();
            for bit in filter.bits.iter() {
                if bit {
                    let self_bit = self_bits.next().unwrap();
                    new_self_bits.push(self_bit);
                } else {
                    new_self_bits.push(false);
                }
            }
            new_self_bits.extend(self_bits.skip(2));
            let new_self_usages = Usages { bits: new_self_bits };
            Some(ControlFlow::Break(new_self_usages))
        } else if self.bits[num_ones] && self.bits[num_ones + 1] {
            let mut self_bits = self.bits.iter();
            let mut new_self_bits = SmallBitVec::new();
            let mut new_filter_bits = SmallBitVec::new();
            let mut new_elim_bits = SmallBitVec::new();

            for (filter_bit, elim_bit) in filter.bits.iter().zip(elim.usages.bits.iter()) {
                let new_self_bit = if filter_bit {
                    let self_bit = self_bits.next().unwrap();
                    if self_bit {
                        new_filter_bits.push(true);
                        new_elim_bits.push(elim_bit);
                        true
                    } else {
                        elim_bit
                    }
                } else {
                    new_filter_bits.push(false);
                    new_elim_bits.push(true);
                    true
                };
                new_self_bits.push(new_self_bit);
            }
            new_self_bits.extend(self_bits.skip(2));
            
            let new_self_usages = Usages { bits: new_self_bits };
            let new_filter = Usages { bits: new_filter_bits };
            let new_elim = Weaken {
                usages: Usages { bits: new_elim_bits },
                weak: elim.weak.clone(),
            };
            Some(ControlFlow::Continue((new_self_usages, new_filter, new_elim)))
        } else {
            None
        }
    }

    pub fn filter_index(&self, index: usize) -> Option<usize> {
        let mut iter = self.bits.iter();
        let new_index = iter.by_ref().take(index).filter(|bit| *bit).count();
        let bit = iter.next().unwrap();
        bit.then_some(new_index)
    }

    pub fn strong_ctx_len(&self) -> usize {
        for index in (0..self.bits.len()).rev() {
            if self.bits[index] {
                return 1 + index;
            }
        }
        0
    }

    pub fn set(&mut self, index: usize, bit: bool) {
        self.bits.set(index, bit);
    }

    pub fn with_usages_from_ctx<S: Scheme>(&self, raw_ctx: &RawCtx<S>) -> Usages {
        let mut raw_ctx = raw_ctx;
        let mut ret = self.clone();
        for index in (0..self.len()).rev() {
            let cons = raw_ctx.cons_opt.as_ref().unwrap();
            raw_ctx = &cons.parent;
            if ret.bits[index] {
                for i in 0..index {
                    if cons.var_ty.usages.bits[i] {
                        ret.bits.set(i, true);
                    }
                }
            }
        }
        debug_assert!(raw_ctx.cons_opt.is_none());
        ret
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

