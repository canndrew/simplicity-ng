use crate::priv_prelude::*;

pub trait Substitute<S: Scheme> {
    type RawSubstOutput: Substitute<S, RawSubstOutput = Self::RawSubstOutput> + Clone + PartialEq;
    fn to_subst_output(&self, num_usages: usize) -> Self::RawSubstOutput;
    fn subst(&self, filter: &Usages, var_term: RawTm<S>) -> Weaken<Self::RawSubstOutput>;
    fn eliminates_var(&self, index: usize) -> bool;
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Weaken<T> {
    pub usages: Usages,
    pub weak: T,
}

impl<T> Weaken<T> {
    pub(crate) fn clone_filter(&self, usages: &Usages) -> Self
    where
        T: Clone,
    {
        Weaken {
            usages: self.usages.clone_filter(usages),
            weak: self.weak.clone(),
        }
    }

    pub(crate) fn clone_unfilter(&self, usages: &Usages) -> Self
    where
        T: Clone,
    {
        Weaken {
            usages: self.usages.clone_unfilter(usages),
            weak: self.weak.clone(),
        }
    }

    pub fn unfilter(mut self, usages: &Usages) -> Self {
        self.usages.unfilter(usages);
        self
    }

    pub(crate) fn filter_self(mut self) -> (Usages, Self) {
        let num_usages = self.usages.count_ones();
        let usages = mem::replace(&mut self.usages, Usages::ones(num_usages));
        (usages, self)
    }

    pub(crate) fn weaken(&mut self, ext_len: usize) {
        self.usages.weaken(ext_len);
    }

    pub(crate) fn clone_weaken(&self, ext_len: usize) -> Self
    where
        T: Clone,
    {
        let usages = self.usages.clone_weaken(ext_len);
        let weak = self.weak.clone();
        Weaken { usages, weak }
    }

    pub(crate) fn unfilter_out<R>(&self, func: impl FnOnce(&T) -> Weaken<R>) -> Weaken<R> {
        func(&self.weak).unfilter(&self.usages)
    }

    pub(crate) fn try_strengthen_to_index(&self, index: usize) -> Option<Weaken<T>>
    where
        T: Clone,
    {
        let usages = self.usages.try_strengthen(index)?;
        let weak = self.weak.clone();
        Some(Weaken { usages, weak })
    }

    pub fn to_subst_output<S: Scheme>(&self) -> Weaken<T::RawSubstOutput>
    where
        T: Substitute<S>,
    {
        let Weaken { usages, weak } = self;
        let usages = usages.clone();
        let weak = weak.to_subst_output(usages.count_ones());
        Weaken { usages, weak }
    }

    pub fn subst<S: Scheme>(&self, filter: &Usages, var_term: &RawTm<S>) -> Weaken<T::RawSubstOutput>
    where
        T: Substitute<S>,
    {
        debug_assert_eq!(self.usages.len(), filter.count_ones());
        let ret = match self.usages.subst(filter, var_term) {
            ControlFlow::Break(usages) => {
                let weak = self.weak.to_subst_output(usages.count_ones());
                Weaken { usages, weak }
            },
            ControlFlow::Continue((unfilter, sub_filter, var_term)) => {
                let mut ret = self.weak.subst(&sub_filter, var_term);
                ret.usages.unfilter(&unfilter);
                ret
            },
        };
        debug_assert_eq!(ret.usages.len() + 1, filter.len());
        ret
    }

    pub fn eliminates_var<S: Scheme>(&self, index: usize) -> bool
    where
        T: Substitute<S>,
    {
        let Some(index) = self.usages.filter_index(index) else {
            return false;
        };
        self.weak.eliminates_var(index)
    }
}

