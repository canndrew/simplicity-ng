use crate::priv_prelude::*;

pub type RawScope<S, T> = Weaken<RawScopeKind<S, T>>;

#[derive_where(Debug, PartialEq, Eq, PartialOrd, Ord, Hash; T)]
pub struct RawScopeKind<S: Scheme, T> {
    pub(crate) var_ty: RawTy<S>,
    pub(crate) inner: Weaken<T>,
}

impl<S: Scheme, T: Clone> Clone for RawScopeKind<S, T> {
    fn clone(&self) -> RawScopeKind<S, T> {
        RawScopeKind {
            var_ty: self.var_ty.clone(),
            inner: self.inner.clone(),
        }
    }
}

impl<S: Scheme, T> RawScope<S, T> {
    pub(crate) fn new(mut var_ty: RawTy<S>, mut inner: Weaken<T>) -> RawScope<S, T> {
        let var_used = inner.usages.pop();
        let usages = Usages::merge_mut([&mut inner.usages, &mut var_ty.usages]);
        inner.usages.push(var_used);
        let weak = RawScopeKind { var_ty, inner };
        Weaken { usages, weak }
    }

    pub(crate) fn bind(self, term: &RawTm<S>) -> Weaken<T::RawSubstOutput>
    where
        T: Substitute<S>,
    {
        let Weaken { mut usages, weak } = self;
        debug_assert_eq!(usages.len(), term.usages.len());
        usages.push(true);
        weak.inner.subst(&usages, term)
    }

    pub(crate) fn into_inner(self) -> (Weaken<T>, RawTy<S>) {
        let Weaken { mut usages, weak } = self;
        let RawScopeKind { var_ty, inner } = weak;

        let var_ty = var_ty.unfilter(&usages);
        usages.push(true);
        let inner = inner.unfilter(&usages);
        (inner, var_ty)
    }

    pub(crate) fn var_ty_unfiltered(&self) -> RawTy<S> {
        self.weak.var_ty.clone_unfilter(&self.usages)
    }

    pub(crate) fn inner_unfiltered_strengthen(&self) -> Weaken<T>
    where
        T: Clone,
    {
        let mut inner = self.inner_unfiltered_with_var();
        let var_used = inner.usages.pop();
        assert!(!var_used);
        inner
    }

    pub(crate) fn inner_unfiltered_with_var(&self) -> Weaken<T>
    where
        T: Clone,
    {
        let mut filter = self.usages.clone();
        filter.push(true);
        self.weak.inner.clone_unfilter(&filter)
    }

    pub(crate) fn var_used(&self) -> bool {
        self.weak.inner.usages.last()
    }
}

impl<S: Scheme> RawScope<S, Intern<RawTyKind<S>>> {
    pub(crate) fn unique_eta_term_opt(
        &self,
        ty_var_etas: &mut Vec<(usize, usize)>,
    ) -> Option<RawScope<S, Intern<RawTmKind<S>>>> {
        let (inner, var_ty) = self.clone().into_inner();
        let inner_term = inner.unique_eta_term_opt(ty_var_etas)?;
        let scope_term = RawScope::new(var_ty, inner_term);
        Some(scope_term)
    }
}

impl<S: Scheme> RawScope<S, Intern<RawTmKind<S>>> {
    pub(crate) fn unique_eta_term_opt(
        &self,
        ty_var_etas: &mut Vec<(usize, usize)>,
    ) -> Option<RawScope<S, Intern<RawTmKind<S>>>> {
        let (inner, var_ty) = self.clone().into_inner();
        let inner_term = inner.unique_eta_term_opt(ty_var_etas)?;
        let scope_term = RawScope::new(var_ty, inner_term);
        Some(scope_term)
    }
}

impl<S: Scheme, T> Substitute<S> for RawScopeKind<S, T>
where
    T: Substitute<S>,
    T: Clone + PartialEq,
{
    type RawSubstOutput = RawScopeKind<S, T::RawSubstOutput>;

    fn to_subst_output(&self, _num_usages: usize) -> RawScopeKind<S, T::RawSubstOutput> {
        RawScopeKind {
            var_ty: self.var_ty.clone(),
            inner: self.inner.to_subst_output(),
        }
    }

    fn subst(&self, filter: &Usages, var_term: RawTm<S>) -> RawScope<S, T::RawSubstOutput> {
        let var_ty = self.var_ty.subst(filter, &var_term);
        let mut filter = filter.clone();
        filter.push(true);
        let inner = self.inner.subst(&filter, &var_term);
        if inner.usages.last() && let Some(eta_term) = var_ty.unique_eta_term_opt(&mut Vec::new()) {
            let filter = Usages::ones(inner.usages.count_ones());
            let mut inner = inner.subst(&filter, &eta_term);
            inner.weaken(1);
            RawScope::new(var_ty, inner)
        } else {
            RawScope::new(var_ty, inner)
        }
    }

    fn eliminates_var(&self, index: usize) -> bool {
        self.var_ty.eliminates_var(index) ||
        self.inner.eliminates_var(index)
    }
}

pub fn raw_scope<S: Scheme, T: Contextual<S>>(
    raw_ctx: &RawCtx<S>,
    var_ty: &RawTy<S>,
    func: impl FnOnce(Tm<S>) -> T,
) -> RawScope<S, T::Raw> {
    let ctx_len = var_ty.usages.len();
    let raw_ctx = raw_ctx.cons(var_ty.clone());
    let var_term = {
        let ty = var_ty.clone_weaken(1);
        let term = RawTm::var(ctx_len + 1, ctx_len, var_ty);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };

    let inner = func(var_term);

    let (inner_ctx, mut inner) = inner.into_raw();
    let diff = (ctx_len + 1).strict_sub(inner_ctx.len());
    assert_eq!(raw_ctx.nth_parent(diff), &inner_ctx.raw_ctx);
    inner.weaken(diff);

    RawScope::new(var_ty.clone(), inner)
}

pub fn raw_scope_2<S: Scheme, T: Contextual<S>>(
    raw_ctx: &RawCtx<S>,
    var_ty_0: &RawTy<S>,
    var_ty_1: &RawTy<S>,
    func: impl FnOnce(Tm<S>, Tm<S>) -> T,
) -> RawScope<S, RawScopeKind<S, T::Raw>> {
    let ctx_len = var_ty_0.usages.len();
    assert_eq!(ctx_len + 1, var_ty_1.usages.len());

    let raw_ctx = raw_ctx.cons(var_ty_0.clone()).cons(var_ty_1.clone());
    let var_term_0 = {
        let ty = var_ty_0.clone_weaken(2);
        let term = RawTm::var(ctx_len + 2, ctx_len, var_ty_0);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };
    let var_term_1 = {
        let ty = var_ty_1.clone_weaken(1);
        let term = RawTm::var(ctx_len + 2, ctx_len + 1, var_ty_1);
        let term = RawTyped::from_parts(ty, term);
        Tm { 
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };

    let inner = func(var_term_0, var_term_1);

    let (inner_ctx, mut inner) = inner.into_raw();
    let diff = (ctx_len + 2).strict_sub(inner_ctx.len());
    assert_eq!(raw_ctx.nth_parent(diff), &inner_ctx.raw_ctx);
    inner.weaken(diff);

    RawScope::new(
        var_ty_0.clone(),
        RawScope::new(
            var_ty_1.clone(),
            inner,
        ),
    )
}

pub fn raw_scope_3<S: Scheme, T: Contextual<S>>(
    raw_ctx: &RawCtx<S>,
    var_ty_0: &RawTy<S>,
    var_ty_1: &RawTy<S>,
    var_ty_2: &RawTy<S>,
    func: impl FnOnce(Tm<S>, Tm<S>, Tm<S>) -> T,
) -> RawScope<S, RawScopeKind<S, RawScopeKind<S, T::Raw>>> {
    let ctx_len = var_ty_0.usages.len();
    assert_eq!(ctx_len + 1, var_ty_1.usages.len());
    assert_eq!(ctx_len + 2, var_ty_2.usages.len());

    let raw_ctx = {
        raw_ctx
        .cons(var_ty_0.clone())
        .cons(var_ty_1.clone())
        .cons(var_ty_2.clone())
    };
    let var_term_0 = {
        let ty = var_ty_0.clone_weaken(3);
        let term = RawTm::var(ctx_len + 3, ctx_len, var_ty_0);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };
    let var_term_1 = {
        let ty = var_ty_1.clone_weaken(2);
        let term = RawTm::var(ctx_len + 3, ctx_len + 1, var_ty_1);
        let term = RawTyped::from_parts(ty, term);
        Tm { 
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };
    let var_term_2 = {
        let ty = var_ty_2.clone_weaken(1);
        let term = RawTm::var(ctx_len + 3, ctx_len + 2, var_ty_2);
        let term = RawTyped::from_parts(ty, term);
        Tm { 
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };

    let inner = func(var_term_0, var_term_1, var_term_2);

    let (inner_ctx, mut inner) = inner.into_raw();
    let diff = (ctx_len + 3).strict_sub(inner_ctx.len());
    assert_eq!(raw_ctx.nth_parent(diff), &inner_ctx.raw_ctx);
    inner.weaken(diff);

    RawScope::new(
        var_ty_0.clone(),
        RawScope::new(
            var_ty_1.clone(),
            RawScope::new(
                var_ty_2.clone(),
                inner,
            ),
        ),
    )
}

pub fn try_raw_scope<S: Scheme, Y>(
    raw_ctx: &RawCtx<S>,
    var_ty: &RawTy<S>,
    func: impl FnOnce(Tm<S>) -> Y,
) -> <Y::Residual as Residual<RawScope<S, <Y::Output as Contextual<S>>::Raw>>>::TryType
where
    Y: Try,
    Y::Output: Contextual<S>,
    Y::Residual: Residual<RawScope<S, <Y::Output as Contextual<S>>::Raw>>,
{
    let ctx_len = var_ty.usages.len();
    let raw_ctx = raw_ctx.cons(var_ty.clone());
    let var_term = {
        let ty = var_ty.clone_weaken(1);
        let term = RawTm::var(ctx_len + 1, ctx_len, var_ty);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };
    let inner_res = func(var_term);
    match inner_res.branch() {
        ControlFlow::Break(err) => {
            <
                <
                    Y::Residual as Residual<RawScope<S, <Y::Output as Contextual<S>>::Raw>>
                >::TryType as FromResidual
            >::from_residual(err)
        },
        ControlFlow::Continue(inner) => {
            let raw_scope = {
                let (inner_ctx, mut inner) = inner.into_raw();
                let diff = (ctx_len + 1).strict_sub(inner_ctx.len());
                assert_eq!(raw_ctx.nth_parent(diff), &inner_ctx.raw_ctx);
                inner.weaken(diff);
                RawScope::new(var_ty.clone(), inner)
            };
            <
                <
                    Y::Residual as Residual<RawScope<S, <Y::Output as Contextual<S>>::Raw>>
                >::TryType as Try
            >::from_output(raw_scope)
        },
    }
}

