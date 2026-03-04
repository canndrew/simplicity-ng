use crate::priv_prelude::*;

pub trait Substitute<S: Scheme> {
    type RawSubstOutput: Substitute<S, RawSubstOutput = Self::RawSubstOutput> + Clone + PartialEq;
    fn to_subst_output(&self, num_usages: usize) -> Self::RawSubstOutput;
    fn subst(&self, filter: &Usages, var_term: RawTm<S>) -> Weaken<Self::RawSubstOutput>;
    fn eliminates_var(&self, index: usize) -> bool;
    fn contains_subterm(&self, subterm: RawTm<S>) -> bool;
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

    pub(crate) fn clone_filter_prefix(&self, ctx_len: usize, usages: &Usages) -> Self
    where
        T: Clone,
    {
        Weaken {
            usages: self.usages.clone_filter_prefix(ctx_len, usages),
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

    pub(crate) fn weaken(self, ext_len: usize) -> Self {
        let mut ret = self;
        ret.usages.weaken(ext_len);
        ret
    }

    pub(crate) fn clone_weaken(&self, ext_len: usize) -> Self
    where
        T: Clone,
    {
        let usages = self.usages.clone_weaken(ext_len);
        let weak = self.weak.clone();
        Weaken { usages, weak }
    }

    /*
    pub(crate) fn unfilter_out<R>(&self, func: impl FnOnce(&T) -> Weaken<R>) -> Weaken<R> {
        func(&self.weak).unfilter(&self.usages)
    }
    */

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

    pub fn contains_subterm<S: Scheme>(&self, subterm: &RawTm<S>) -> bool
    where
        T: Substitute<S>,
    {
        if !self.usages.is_superset_of_prefix(&subterm.usages) {
            return false;
        }

        let subterm = subterm.clone_filter_prefix(subterm.usages.len(), &self.usages);
        self.weak.contains_subterm(subterm)
    }
}

pub(crate) trait BundleOfContextualRaw<S: Scheme> {
    type Output;

    fn into_common_ctx_raw(self) -> (Ctx<S>, Self::Output);
}

macro_rules! impl_bundle_of_contextual_raw_for_tuple (
    ($($name:ident,)*) => (
        impl<S: Scheme, $($name,)*> BundleOfContextualRaw<S> for ($(&$name,)*)
        where
            $($name: Contextual<S> + Clone,)*
        {
            type Output = ($(Weaken<$name::Raw>,)*);

            #[allow(unused_mut)]
            #[allow(unused_variables)]
            #[allow(unused_assignments)]
            #[allow(non_snake_case)]
            fn into_common_ctx_raw(self) -> (Ctx<S>, ($(Weaken<$name::Raw>,)*)) {
                let ($($name,)*) = self;

                let mut longest_ctx: Ctx<S> = Ctx::root();
                let mut argument_number_of_longest_ctx = 0;
                let mut current_argument_number = 0;

                $(
                    let this_ctx = $name.ctx();
                    if this_ctx.len() > longest_ctx.len() {
                        longest_ctx = this_ctx;
                        argument_number_of_longest_ctx = current_argument_number;
                    }
                    current_argument_number += 1;
                )*
                
                current_argument_number = 0;
                $(
                    let (this_ctx, this_raw) = $name.clone().into_raw();
                    let diff = longest_ctx.len().strict_sub(this_ctx.len());
                    if longest_ctx.raw_ctx.nth_parent(diff) != &this_ctx.raw_ctx {
                        panic!(
                            "into_common_ctx(): arguments {} and {} \
                            come from contexts that have diverged.",
                            cmp::min(current_argument_number, argument_number_of_longest_ctx),
                            cmp::max(current_argument_number, argument_number_of_longest_ctx),
                        );
                    }
                    let $name = this_raw.weaken(diff);
                    current_argument_number += 1;
                )*

                (longest_ctx, ($($name,)*))
            }
        }
    );
);

impl_bundle_of_contextual_raw_for_tuple!();
impl_bundle_of_contextual_raw_for_tuple!(T0,);
impl_bundle_of_contextual_raw_for_tuple!(T0, T1,);
impl_bundle_of_contextual_raw_for_tuple!(T0, T1, T2,);
impl_bundle_of_contextual_raw_for_tuple!(T0, T1, T2, T3,);
impl_bundle_of_contextual_raw_for_tuple!(T0, T1, T2, T3, T4,);
impl_bundle_of_contextual_raw_for_tuple!(T0, T1, T2, T3, T4, T5,);
impl_bundle_of_contextual_raw_for_tuple!(T0, T1, T2, T3, T4, T5, T6,);
impl_bundle_of_contextual_raw_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7,);

impl<const LEN: usize, S: Scheme, T> BundleOfContextualRaw<S> for [&T; LEN]
where
    T: Contextual<S> + Clone,
{
    type Output = [Weaken<T::Raw>; LEN];

    fn into_common_ctx_raw(self) -> (Ctx<S>, [Weaken<T::Raw>; LEN]) {
        let mut longest_ctx: Ctx<S> = Ctx::root();
        let mut index_of_longest_ctx = 0;

        for (index, thing) in self.iter().enumerate() {
            let this_ctx = thing.ctx();
            if this_ctx.len() > longest_ctx.len() {
                longest_ctx = this_ctx;
                index_of_longest_ctx = index;
            }
        }

        let mut index = 0;
        let things_raw = self.map(|thing| {
            let (this_ctx, this_raw) = thing.clone().into_raw();
            let diff = longest_ctx.len().strict_sub(this_ctx.len());
            if longest_ctx.raw_ctx.nth_parent(diff) != &this_ctx.raw_ctx {
                panic!(
                    "into_common_ctx(): items {} and {} \
                    come from contexts that have diverged.",
                    cmp::min(index, index_of_longest_ctx),
                    cmp::max(index, index_of_longest_ctx),
                );
            }
            index += 1;
            this_raw.weaken(diff)
        });

        (longest_ctx, things_raw)
    }
}

pub(crate) fn merge_ctxs<S, Ts>(bundle: Ts) -> (Ctx<S>, Ts::Output)
where
    S: Scheme,
    Ts: BundleOfContextualRaw<S>,
{
    BundleOfContextualRaw::into_common_ctx_raw(bundle)
}


