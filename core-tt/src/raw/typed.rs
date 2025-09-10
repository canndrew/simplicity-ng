use crate::priv_prelude::*;

pub type RawTyped<S, T> = Weaken<RawTypedKind<S, T>>;

#[derive_where(Debug, Clone, PartialEq, Eq, Hash; T)]
pub struct RawTypedKind<S: Scheme, T> {
    pub(crate) raw_ty: RawTy<S>,
    pub(crate) inner: Weaken<T>,
}

impl<S: Scheme, T> Substitute<S> for RawTypedKind<S, T>
where
    T: Substitute<S>,
    T: Clone + PartialEq,
{
    type RawSubstOutput = RawTypedKind<S, T::RawSubstOutput>;

    fn to_subst_output(&self, _num_usages: usize) -> RawTypedKind<S, T::RawSubstOutput> {
        let RawTypedKind { raw_ty, inner } = self;
        let raw_ty = raw_ty.clone();
        let inner = inner.to_subst_output();
        RawTypedKind { raw_ty, inner }
    }

    fn subst(&self, filter: &Usages, var_term: RawTm<S>) -> RawTyped<S, T::RawSubstOutput> {
        let RawTypedKind { raw_ty, inner } = self;
        let raw_ty = raw_ty.subst(filter, &var_term);
        let inner = inner.subst(filter, &var_term);
        RawTyped::from_parts(raw_ty, inner)
    }

    fn eliminates_var(&self, index: usize) -> bool {
        self.raw_ty.eliminates_var(index) ||
        self.inner.eliminates_var(index)
    }
}

impl<S: Scheme, T> RawTyped<S, T> {
    pub(crate) fn from_parts(mut raw_ty: RawTy<S>, mut inner: Weaken<T>) -> RawTyped<S, T> {
        let usages = Usages::merge_mut([&mut raw_ty.usages, &mut inner.usages]);

        let weak = RawTypedKind { raw_ty, inner };
        Weaken { usages, weak }
    }

    pub(crate) fn to_parts(&self) -> (RawTy<S>, Weaken<T>)
    where
        T: Clone,
    {
        let Weaken { usages, weak: RawTypedKind { raw_ty, inner } } = self;
        let raw_ty = raw_ty.clone_unfilter(usages);
        let inner = inner.clone_unfilter(usages);
        (raw_ty, inner)
    }

    pub(crate) fn into_parts(self) -> (RawTy<S>, Weaken<T>) {
        let Weaken { usages, weak: RawTypedKind { raw_ty, inner } } = self;
        let raw_ty = raw_ty.unfilter(&usages);
        let inner = inner.unfilter(&usages);
        (raw_ty, inner)
    }

    pub(crate) fn inner_unfiltered(&self) -> Weaken<T>
    where
        T: Clone,
    {
        self.weak.inner.clone_unfilter(&self.usages)
    }
}

impl<S: Scheme, T> RawScope<S, RawTypedKind<S, T>>
where
    T: Substitute<S>,
    T: Clone + PartialEq,
{
    pub(crate) fn from_parts_1(raw_ty: RawScope<S, Intern<RawTyKind<S>>>, inner: RawScope<S, T>) -> RawScope<S, RawTypedKind<S, T>> {
        let (raw_ty, var_ty) = raw_ty.into_inner();
        let (inner, _inner_var_ty) = inner.into_inner();
        let inner = RawTyped::from_parts(raw_ty, inner);
        RawScope::new(var_ty, inner)
    }

    pub(crate) fn into_parts(self) -> (RawScope<S, Intern<RawTyKind<S>>>, RawScope<S, T>) {
        let (inner, var_ty) = self.into_inner();
        let (raw_ty, inner) = inner.into_parts();
        let raw_ty = RawScope::new(var_ty.clone(), raw_ty);
        let inner = RawScope::new(var_ty, inner);
        (raw_ty, inner)
    }
}

impl<S: Scheme, T> RawScope<S, RawScopeKind<S, RawTypedKind<S, T>>>
where
    T: Substitute<S>,
    T: Clone + PartialEq,
{
    /*
    pub(crate) fn from_parts_2(raw_ty: RawScope<S, RawTy<S>>, inner: RawScope<S, T>) -> RawScope<S, RawTyped<S, T>> {
        let raw_ty = raw_ty.into_inner();
        let inner = inner.into_inner();
        let inner = RawTyped::from_parts(raw_ty, inner);
        RawScope::new(inner)
    }
    */

    pub(crate) fn into_parts(self) -> (RawScope<S, RawScopeKind<S, Intern<RawTyKind<S>>>>, RawScope<S, RawScopeKind<S, T>>) {
        let (inner, var_ty_0) = self.into_inner();
        let (inner, var_ty_1) = inner.into_inner();
        let (raw_ty, inner) = inner.into_parts();
        let raw_ty = RawScope::new(
            var_ty_0.clone(),
            RawScope::new(
                var_ty_1.clone(),
                raw_ty,
            ),
        );
        let inner = RawScope::new(
            var_ty_0,
            RawScope::new(
                var_ty_1,
                inner,
            ),
        );
        (raw_ty, inner)
    }
}

