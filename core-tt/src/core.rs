use crate::priv_prelude::*;

pub trait Name: PartialEq + Eq + PartialOrd + Ord + fmt::Debug + Clone {
    /*
    fn for_loop_elim_name() -> Self;
    fn for_loop_state_name() -> Self;
    */
}

pub(crate) trait ContextualSealed<N: Name> {
    type Raw: RawContextual<N> + Clone;

    fn raw_ctx(&self) -> &RawCtx<N>;
    fn raw(&self) -> &Self::Raw;
    fn into_raw(self) -> Self::Raw;
    fn from_raw(raw_ctx: RawCtx<N>, raw: Self::Raw) -> Self;
}

#[allow(private_bounds)]
pub trait Contextual<N: Name>: ContextualSealed<N> {}

impl<N: Name, T: ContextualSealed<N>> Contextual<N> for T {}

#[allow(private_bounds)]
pub trait SubstInvariant<N: Name>: ContextualSealed<N, Raw: RawContextual<N, SubstOutput = Self::Raw>>
{}

impl<N: Name, T: ContextualSealed<N, Raw: RawContextual<N, SubstOutput = T::Raw>>> SubstInvariant<N> for T
{}

#[derive(Clone, PartialEq)]
pub struct Ctx<N: Name> {
    pub(crate) ctx_len: usize,
    pub(crate) raw_ctx: RawCtx<N>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Ty<N: Name> {
    pub(crate) raw_ctx: RawCtx<N>,
    pub(crate) raw_ty: RawTy<N>,
}

#[derive(Clone, PartialEq)]
pub struct Tm<N: Name> {
    pub(crate) raw_ctx: RawCtx<N>,
    pub(crate) raw_typed_term: RawTyped<N, RawTm<N>>,
}

#[derive(Clone, PartialEq)]
pub struct Stuck<N: Name> {
    pub(crate) raw_ctx: RawCtx<N>,
    pub(crate) raw_typed_stuck: RawTyped<N, RawStuck<N>>,
}

pub struct Scope<N: Name, T: Contextual<N>> {
    pub(crate) raw_ctx: RawCtx<N>,
    pub(crate) raw_typed_scope: RawTyped<N, RawScope<N, T::Raw>>,
}

impl<N: Name, T: Contextual<N>> Clone for Scope<N, T>
where
    T::Raw: Clone,
{
    fn clone(&self) -> Scope<N, T> {
        let raw_ctx = self.raw_ctx.clone();
        let raw_typed_scope = self.raw_typed_scope.clone();
        Scope { raw_ctx, raw_typed_scope }
    }
}

#[derive(Clone)]
pub enum TyKind<N: Name> {
    Stuck {
        stuck: Stuck<N>,
    },
    Universe,
    Nat,
    Equal {
        eq_term_0: Tm<N>,
        eq_term_1: Tm<N>,
    },
    Never,
    Unit,
    Sum {
        lhs_name: N,
        lhs_ty: Ty<N>,
        rhs_ty: Ty<N>,
    },
    Sigma {
        head_name: N,
        head_ty: Ty<N>,
        tail_ty: Scope<N, Ty<N>>,
    },
    Pi {
        arg_name: N,
        arg_ty: Ty<N>,
        res_ty: Scope<N, Ty<N>>,
    },
}

#[derive(Clone)]
pub enum TmKind<N: Name> {
    Stuck {
        stuck: Stuck<N>,
    },
    Type {
        ty: Ty<N>,
    },
    Zero,
    Succs {
        count: NonZeroBigUint,
        pred_term: Tm<N>,
    },
    Refl,
    Unit,
    InjLhs {
        lhs_term: Tm<N>,
    },
    InjRhs {
        rhs_term: Tm<N>,
    },
    Pair {
        head_term: Tm<N>,
        tail_term: Tm<N>,
    },
    Func {
        res_term: Scope<N, Tm<N>>,
    },
}

#[derive(Clone)]
pub enum StuckKind<N: Name> {
    Var {
        index: usize,
    },
    ForLoop {
        elim: Stuck<N>,
        motive: Scope<N, Ty<N>>,
        zero_inhab: Tm<N>,
        succ_inhab: Scope<N, Scope<N, Tm<N>>>,
    },
    /*
    Max {
        max_term_0: Stuck<N>,
        max_term_1: Tm<N>,
    },
    Add {
        elim: Stuck<N>,
        elim_multiplicity: NonZeroBigUint,
        terms: OrdMap<Tm<N>, NonZeroBigUint>,
    },
    Mul {
        elim: Stuck<N>,
        elim_exponent: NonZeroBigUint,
        terms: OrdMap<Tm<N>, NonZeroBigUint>,
    },
    */
    Cong {
        elim: Stuck<N>,
        motive: Scope<N, Scope<N, Scope<N, Ty<N>>>>,
        inhab: Scope<N, Tm<N>>,
    },
    Explode {
        elim: Stuck<N>,
        motive: Scope<N, Ty<N>>,
    },
    Relay {
        elim: Stuck<N>,
        motive: Scope<N, Ty<N>>,
        inhab: Tm<N>,
    },
    Case {
        elim: Stuck<N>,
        motive: Scope<N, Ty<N>>,
        lhs_inhab: Scope<N, Tm<N>>,
        rhs_inhab: Scope<N, Tm<N>>,
    },
    Split {
        elim: Stuck<N>,
        motive: Scope<N, Ty<N>>,
        inhab: Scope<N, Scope<N, Tm<N>>>,
    },
    App {
        elim: Stuck<N>,
        arg_term: Tm<N>,
    },
}

impl<N: Name> Ctx<N> {
    pub fn root() -> Ctx<N> {
        Ctx {
            ctx_len: 0,
            raw_ctx: RawCtx::root(),
        }
    }

    pub fn is_root(&self) -> bool {
        self.ctx_len == 0
    }

    pub fn len(&self) -> usize {
        self.ctx_len
    }

    pub fn cons(&self, var_name: &N, var_ty: &Ty<N>) -> Ctx<N> {
        let ty_ctx_len = var_ty.raw_ty.usages.len();
        let diff = self.ctx_len.strict_sub(ty_ctx_len);
        assert_eq!(self.raw_ctx.nth_parent(diff), &var_ty.raw_ctx);
        let raw_ty = var_ty.raw_ty.clone_weaken(diff);
        let raw_ctx = self.raw_ctx.cons(Some(var_name.clone()), raw_ty);
        Ctx { ctx_len: self.ctx_len + 1, raw_ctx }
    }

    /*
    pub fn cons<T>(&self, ty: &Ty<N>, func: impl FnOnce(Tm<N>) -> T) -> T {
        let ty_ctx_len = ty.raw_ty.usages.len();
        let diff = self.ctx_len.strict_sub(ty_ctx_len);
        assert_eq!(self.raw_ctx.nth_parent(diff), &ty.raw_ctx);
        let raw_ty = ty.raw_ty.clone_weaken(diff);
        let raw_typed_term = RawTyped::from_parts(raw_ty.clone_weaken(1), RawTm::var(self.ctx_len + 1, self.ctx_len));
        let var_term = Tm {
            raw_ctx: self.raw_ctx.cons(raw_ty),
            raw_typed_term,
        };
        func(var_term)
    }
    */

    fn get_raw_ty_weakened(&self, index: usize) -> RawTy<N> {
        let de_brujin = self.ctx_len.strict_sub(index + 1);
        let raw_ctx = self.raw_ctx.nth_parent(de_brujin);
        let var_ty = &raw_ctx.cons_opt.as_ref().unwrap().var_ty;

        var_ty.clone_weaken(de_brujin + 1)
    }

    pub fn get_ty(&self, index: usize) -> Ty<N> {
        let raw_ty = self.get_raw_ty_weakened(index);
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty,
        }
    }

    pub fn var(&self, index: usize) -> Stuck<N> {
        let raw_ty = self.get_raw_ty_weakened(index);
        let raw_stuck = RawStuck::var(self.ctx_len, index);
        let raw_typed_stuck = RawTyped::from_parts(raw_ty, raw_stuck);
        Stuck {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_stuck,
        }
    }

    fn merge_ctx_2<T0: ContextualSealed<N>, T1: ContextualSealed<N>>(
        thing_0: &T0,
        thing_1: &T1,
    ) -> Ctx<N> {
        let ctx_len_0 = thing_0.raw().usages_len(); 
        let ctx_len_1 = thing_1.raw().usages_len(); 
        let raw_ctx_0 = thing_0.raw_ctx();
        let raw_ctx_1 = thing_1.raw_ctx();

        let (ctx_len, raw_ctx, cmp_ctx_0, cmp_ctx_1) = match ctx_len_0.cmp(&ctx_len_1) {
            cmp::Ordering::Less => {
                let diff = ctx_len_1 - ctx_len_0;
                (ctx_len_1, raw_ctx_1, raw_ctx_0, raw_ctx_1.nth_parent(diff))
            },
            cmp::Ordering::Equal => (ctx_len_0, raw_ctx_0, raw_ctx_0, raw_ctx_1),
            cmp::Ordering::Greater => {
                let diff = ctx_len_0 - ctx_len_1;
                (ctx_len_0, raw_ctx_0, raw_ctx_0.nth_parent(diff), raw_ctx_1)
            },
        };
        assert_eq!(cmp_ctx_0, cmp_ctx_1);
        let raw_ctx = raw_ctx.clone();
        Ctx { ctx_len, raw_ctx }
    }

    fn merge_into_ctx_2<T0: ContextualSealed<N>, T1: ContextualSealed<N>>(
        thing_0: &T0,
        thing_1: &T1,
    ) -> (Ctx<N>, T0::Raw, T1::Raw) {
        let ctx = Ctx::merge_ctx_2(thing_0, thing_1);

        let thing_0 = thing_0.raw().clone_weaken(ctx.ctx_len.strict_sub(thing_0.raw().usages().len()));
        let thing_1 = thing_1.raw().clone_weaken(ctx.ctx_len.strict_sub(thing_1.raw().usages().len()));

        (ctx, thing_0, thing_1)
    }

    /*
    fn common_ctx_2<T0: ContextualSealed<N>, T1: ContextualSealed<N>>(
        thing_0: &T0,
        thing_1: &T1,
    ) -> (RawCtx, Usages, T0::Raw, T1::Raw) {
        let Ctx { ctx_len, raw_ctx } = Ctx::merge_ctx_2(thing_0, thing_1);

        let usages = Usages::merge(ctx_len, [thing_0.raw().usages(), thing_1.raw().usages()]);
        let thing_0 = thing_0.raw().clone_filter(&usages);
        let thing_1 = thing_1.raw().clone_filter(&usages);

        (raw_ctx, usages, thing_0, thing_1)
    }
    */

    pub fn universe(&self) -> Ty<N> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::universe(self.ctx_len),
        }
    }

    pub fn nat(&self) -> Ty<N> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::nat(self.ctx_len),
        }
    }

    pub fn zero(&self) -> Tm<N> {
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(RawTy::nat(self.ctx_len), RawTm::zero(self.ctx_len)),
        }
    }

    pub fn never(&self) -> Ty<N> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::never(self.ctx_len),
        }
    }

    pub fn unit_ty(&self) -> Ty<N> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::unit(self.ctx_len),
        }
    }

    pub fn unit_term(&self) -> Tm<N> {
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(RawTy::unit(self.ctx_len), RawTm::unit(self.ctx_len)),
        }
    }
}

impl<N: Name> Ty<N> {
    pub fn ctx(&self) -> Ctx<N> {
        Ctx {
            ctx_len: self.raw_ty.usages.len(),
            raw_ctx: self.raw_ctx.clone(),
        }
    }

    pub fn with_ctx(&self, ctx: &Ctx<N>) -> Ty<N> {
        let diff = ctx.ctx_len.strict_sub(self.raw_ty.usages.len());
        assert_eq!(&self.raw_ctx, ctx.raw_ctx.nth_parent(diff));
        let raw_ctx = ctx.raw_ctx.clone();
        let raw_ty = self.raw_ty.clone_weaken(diff);
        Ty { raw_ctx, raw_ty }
    }

    pub fn to_scope(&self) -> Scope<N, Ty<N>> {
        let Ty { raw_ctx, raw_ty } = self;
        let RawTyKind::Pi { arg_name: _, arg_ty, res_ty } = &*raw_ty.kind else {
            unreachable!()
        };
        let arg_ty = arg_ty.clone_unfilter(&raw_ty.usages);
        let res_ty = res_ty.clone_unfilter(&raw_ty.usages);
        let raw_typed_scope = RawTyped::from_parts(arg_ty, res_ty);
        Scope {
            raw_ctx: raw_ctx.clone(),
            raw_typed_scope,
        }
    }
    
    pub fn kind(&self) -> TyKind<N> {
        let Ty { raw_ctx, raw_ty } = self;
        match &*raw_ty.kind {
            RawTyKind::Stuck { stuck } => {
                let raw_stuck = stuck.clone_unfilter(&raw_ty.usages);
                let raw_ty = RawTy::universe(raw_ty.usages.len());
                let stuck = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: RawTyped::from_parts(raw_ty, raw_stuck),
                };
                TyKind::Stuck { stuck }
            },
            RawTyKind::Universe => TyKind::Universe,
            RawTyKind::Nat => TyKind::Nat,
            RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } => {
                let eq_ty = eq_ty.clone_unfilter(&raw_ty.usages);
                let eq_term_0 = eq_term_0.clone_unfilter(&raw_ty.usages);
                let eq_term_1 = eq_term_1.clone_unfilter(&raw_ty.usages);
                let eq_term_0 = RawTyped::from_parts(eq_ty.clone(), eq_term_0);
                let eq_term_1 = RawTyped::from_parts(eq_ty, eq_term_1);
                let eq_term_0 = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: eq_term_0,
                };
                let eq_term_1 = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: eq_term_1,
                };
                TyKind::Equal { eq_term_0, eq_term_1 }
            },
            RawTyKind::Never => TyKind::Never,
            RawTyKind::Unit => TyKind::Unit,
            RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_ty = lhs_ty.clone_unfilter(&raw_ty.usages);
                let rhs_ty = rhs_ty.clone_unfilter(&raw_ty.usages);
                let lhs_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: lhs_ty,
                };
                let rhs_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: rhs_ty,
                };
                TyKind::Sum { lhs_name: lhs_name.clone(), lhs_ty, rhs_ty }
            },
            RawTyKind::Sigma { head_name, head_ty, tail_ty } => {
                let head_ty = head_ty.clone_unfilter(&raw_ty.usages);
                let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);
                let tail_ty = RawTyped::from_parts(head_ty.clone(), tail_ty);
                let head_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: head_ty,
                };
                let tail_ty = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: tail_ty,
                };
                TyKind::Sigma { head_name: head_name.clone(), head_ty, tail_ty }
            },
            RawTyKind::Pi { arg_name, arg_ty, res_ty } => {
                let arg_ty = arg_ty.clone_unfilter(&raw_ty.usages);
                let res_ty = res_ty.clone_unfilter(&raw_ty.usages);
                let res_ty = RawTyped::from_parts(arg_ty.clone(), res_ty);
                let arg_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: arg_ty,
                };
                let res_ty = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: res_ty,
                };
                TyKind::Pi { arg_name: arg_name.clone(), arg_ty, res_ty }
            },
        }
    }

    pub fn universe() -> Ty<N> {
        Ty {
            raw_ctx: RawCtx::root(),
            raw_ty: RawTy::universe(0),
        }
    }

    pub fn nat() -> Ty<N> {
        Ty {
            raw_ctx: RawCtx::root(),
            raw_ty: RawTy::nat(0),
        }
    }

    pub fn never() -> Ty<N> {
        Ty {
            raw_ctx: RawCtx::root(),
            raw_ty: RawTy::never(0),
        }
    }

    pub fn unit() -> Ty<N> {
        Ty {
            raw_ctx: RawCtx::root(),
            raw_ty: RawTy::unit(0),
        }
    }

    pub fn sum(
        lhs_name: &N,
        lhs_ty: &Ty<N>,
        rhs_ty: &Ty<N>,
    ) -> Ty<N> {
        let (ctx, lhs_ty, rhs_ty) = Ctx::merge_into_ctx_2(lhs_ty, rhs_ty);
        let raw_ctx = ctx.raw_ctx;
        let raw_ty = RawTy::sum(lhs_name.clone(), lhs_ty, rhs_ty);
        Ty { raw_ctx, raw_ty }
    }

    pub fn sigma(
        &self,
        head_name: &N,
        tail_ty: impl FnOnce(Tm<N>) -> Ty<N>,
    ) -> Ty<N> {
        let head_ty = self;
        let tail_ty = raw_scope(&head_ty.raw_ctx, Some(head_name.clone()), &head_ty.raw_ty, tail_ty);

        let raw_ctx = head_ty.raw_ctx.clone();
        let raw_ty = RawTy::sigma(head_name.clone(), head_ty.raw().clone(), tail_ty);
        Ty { raw_ctx, raw_ty }
    }

    pub fn pi(
        &self,
        arg_name: &N,
        res_ty: impl FnOnce(Tm<N>) -> Ty<N>,
    ) -> Ty<N> {
        let arg_ty = self;
        let res_ty = raw_scope(&arg_ty.raw_ctx, Some(arg_name.clone()), &arg_ty.raw_ty, res_ty);

        let raw_ctx = arg_ty.raw_ctx.clone();
        let raw_ty = RawTy::pi(arg_name.clone(), arg_ty.raw().clone(), res_ty);
        Ty { raw_ctx, raw_ty }
    }

    pub fn func(
        &self,
        arg_name: &N,
        res_term: impl FnOnce(Tm<N>) -> Tm<N>,
    ) -> Tm<N> {
        let arg_ty = self;
        let res_term = raw_scope(&arg_ty.raw_ctx, Some(arg_name.clone()), &arg_ty.raw_ty, res_term);

        let (res_ty, res_term) = res_term.into_parts();

        let ty = RawTy::pi(arg_name.clone(), arg_ty.raw().clone(), res_ty);
        let term = RawTm::func(res_term);
        let term = RawTyped::from_parts(ty, term);

        Tm { raw_ctx: arg_ty.raw_ctx.clone(), raw_typed_term: term }
    }

    pub fn named_scope<T: Contextual<N>>(&self, var_name: &N, func: impl FnOnce(Tm<N>) -> T) -> Scope<N, T> {
        self.scope_inner(Some(var_name.clone()), func)
    }

    pub fn scope<T: Contextual<N>>(&self, func: impl FnOnce(Tm<N>) -> T) -> Scope<N, T> {
        self.scope_inner(None, func)
    }

    fn scope_inner<T: ContextualSealed<N>>(&self, var_name_opt: Option<N>, func: impl FnOnce(Tm<N>) -> T) -> Scope<N, T> {
        let raw_scope = raw_scope(&self.raw_ctx, var_name_opt, &self.raw_ty, func);
        let raw_typed_scope = RawTyped::from_parts(self.raw_ty.clone(), raw_scope);
        Scope {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_scope,
        }
    }

    #[allow(private_bounds)]
    pub fn try_scope<Y>(
        &self,
        func: impl FnOnce(Tm<N>) -> Y,
    ) -> <Y::Residual as Residual<Scope<N, Y::Output>>>::TryType
    where
        Y: Try,
        Y::Output: Contextual<N>,
        Y::Residual: Residual<Scope<N, Y::Output>>,
        Y::Residual: Residual<RawScope<N, <Y::Output as ContextualSealed<N>>::Raw>>,
    {
        let raw_scope = try_raw_scope(&self.raw_ctx, None, &self.raw_ty, func)?;
        let raw_typed_scope = RawTyped::from_parts(self.raw_ty.clone(), raw_scope);
        let scope = Scope {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_scope,
        };
        <<Y::Residual as Residual<Scope<N, Y::Output>>>::TryType as Try>::from_output(scope)
    }

    pub fn to_term(&self) -> Tm<N> {
        let Ty { raw_ctx, raw_ty } = self;
        let ctx_len = raw_ty.usages.len();

        let term = RawTm::type_(raw_ty.clone());
        let term = RawTyped::from_parts(RawTy::universe(ctx_len), term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }
}

impl<N: Name> Tm<N> {
    pub fn ctx(&self) -> Ctx<N> {
        Ctx {
            ctx_len: self.raw_typed_term.usages.len(),
            raw_ctx: self.raw_ctx.clone(),
        }
    }

    pub fn ty(&self) -> Ty<N> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, _) = raw_typed_term.to_parts();
        Ty {
            raw_ctx: raw_ctx.clone(),
            raw_ty,
        }
    }

    pub fn kind(&self) -> TmKind<N> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        match &*raw_term.kind {
            RawTmKind::Stuck { stuck } => {
                let raw_stuck = stuck.clone_unfilter(&raw_term.usages);
                let stuck = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: RawTyped::from_parts(raw_ty, raw_stuck),
                };
                TmKind::Stuck { stuck }
            },
            RawTmKind::Type { ty } => {
                let ty = ty.clone_unfilter(&raw_term.usages);
                let ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: ty,
                };
                TmKind::Type { ty }
            },
            RawTmKind::Zero => TmKind::Zero,
            RawTmKind::Succs { count, pred_term } => {
                let count = count.clone();
                let pred_term = pred_term.clone_unfilter(&raw_term.usages);
                let pred_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(RawTy::nat(ctx_len), pred_term),
                };
                TmKind::Succs { count, pred_term }
            },
            RawTmKind::Refl => TmKind::Refl,
            RawTmKind::Unit => TmKind::Unit,
            RawTmKind::InjLhs { lhs_term } => {
                let RawTyKind::Sum { lhs_name: _, lhs_ty, rhs_ty: _ } = &*raw_ty.kind else {
                    unreachable!();
                };

                let lhs_term = lhs_term.clone_unfilter(&raw_term.usages);
                let lhs_ty = lhs_ty.clone_unfilter(&raw_ty.usages);
                let lhs_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(lhs_ty, lhs_term),
                };
                TmKind::InjLhs { lhs_term }
            },
            RawTmKind::InjRhs { rhs_term } => {
                let RawTyKind::Sum { lhs_name: _, lhs_ty: _, rhs_ty } = &*raw_ty.kind else {
                    unreachable!();
                };

                let rhs_term = rhs_term.clone_unfilter(&raw_term.usages);
                let rhs_ty = rhs_ty.clone_unfilter(&raw_ty.usages);
                let rhs_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(rhs_ty, rhs_term),
                };
                TmKind::InjRhs { rhs_term }
            },
            RawTmKind::Pair { head_term, tail_term } => {
                let RawTyKind::Sigma { head_name: _, head_ty, tail_ty } = &*raw_ty.kind else {
                    unreachable!();
                };

                let head_term = head_term.clone_unfilter(&raw_term.usages);
                let tail_term = tail_term.clone_unfilter(&raw_term.usages);
                let head_ty = head_ty.clone_unfilter(&raw_ty.usages);
                let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);
                let tail_ty = tail_ty.bind(&head_term);
                let head_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(head_ty, head_term),
                };
                let tail_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(tail_ty, tail_term),
                };
                TmKind::Pair { head_term, tail_term }
            },
            RawTmKind::Func { res_term } => {
                let RawTyKind::Pi { arg_name: _, arg_ty, res_ty } = &*raw_ty.kind else {
                    unreachable!();
                };

                let res_term = res_term.clone_unfilter(&raw_term.usages);
                let arg_ty = arg_ty.clone_unfilter(&raw_ty.usages);
                let res_ty = res_ty.clone_unfilter(&raw_ty.usages);

                let res_term = RawScope::from_parts_1(res_ty, res_term);
                let res_term = RawTyped::from_parts(arg_ty, res_term);
                let res_term = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: res_term,
                };
                TmKind::Func { res_term }
            },
        }
    }

    pub fn zero() -> Tm<N> {
        Tm {
            raw_ctx: RawCtx::root(),
            raw_typed_term: RawTyped::from_parts(RawTy::never(0), RawTm::zero(0)),
        }
    }

    pub fn succs(&self, count: &NonZeroBigUint) -> Tm<N> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Nat = &*raw_ty.kind else {
            unreachable!();
        };

        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(raw_ty, RawTm::succs(count.clone(), raw_term)),
        }
    }

    pub fn equals(&self, other: &Tm<N>) -> Ty<N> {
        let eq_term_0 = self;
        let eq_term_1 = other;

        let (ctx, eq_term_0, eq_term_1) = Ctx::merge_into_ctx_2(eq_term_0, eq_term_1);
        let (eq_ty_0, eq_term_0) = eq_term_0.into_parts();
        let (eq_ty_1, eq_term_1) = eq_term_1.into_parts();
        let eq_ty = as_equal(eq_ty_0, eq_ty_1).unwrap();
        
        let raw_ty = RawTy::equal(eq_ty, eq_term_0, eq_term_1);
        Ty { raw_ctx: ctx.raw_ctx, raw_ty }
    }

    pub fn refl(&self) -> Tm<N> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (eq_ty, eq_term) = raw_typed_term.to_parts();

        let ty = RawTy::equal(eq_ty, eq_term.clone(), eq_term);
        let term = RawTm::refl(ctx_len);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn unit() -> Tm<N> {
        Tm {
            raw_ctx: RawCtx::root(),
            raw_typed_term: RawTyped::from_parts(RawTy::unit(0), RawTm::unit(0)),
        }
    }

    pub fn inj_lhs(&self, lhs_name: &N, rhs_ty: &Ty<N>) -> Tm<N> {
        let lhs_term = self;
        
        let (ctx, lhs_term, rhs_ty) = Ctx::merge_into_ctx_2(lhs_term, rhs_ty);
        let (lhs_ty, lhs_term) = lhs_term.into_parts();
        let ty = RawTy::sum(lhs_name.clone(), lhs_ty, rhs_ty);
        let term = RawTm::inj_lhs(lhs_term);
        let term = RawTyped::from_parts(ty, term);
        Tm { raw_ctx: ctx.raw_ctx, raw_typed_term: term }
    }

    pub fn inj_rhs(&self, lhs_name: &N, lhs_ty: &Ty<N>) -> Tm<N> {
        let rhs_term = self;
        
        let (ctx, lhs_ty, rhs_term) = Ctx::merge_into_ctx_2(lhs_ty, rhs_term);
        let (rhs_ty, rhs_term) = rhs_term.into_parts();
        let ty = RawTy::sum(lhs_name.clone(), lhs_ty, rhs_ty);
        let term = RawTm::inj_rhs(rhs_term);
        let term = RawTyped::from_parts(ty, term);
        Tm { raw_ctx: ctx.raw_ctx, raw_typed_term: term }
    }

    pub fn pair(
        &self,
        head_name: &N,
        tail_ty: impl FnOnce(Tm<N>) -> Ty<N>,
        tail_term: &Tm<N>,
    ) -> Tm<N> {
        let head_term = self;
        
        let (ctx, head_term, tail_term) = Ctx::merge_into_ctx_2(head_term, tail_term);
        let (head_ty, head_term) = head_term.into_parts();
        let tail_ty = raw_scope(&ctx.raw_ctx, Some(head_name.clone()), &head_ty, tail_ty);
        let tail_term = {
            let expected_tail_ty = tail_ty.clone().bind(&head_term);
            let (actual_tail_ty, tail_term) = tail_term.into_parts();
            assert_eq!(expected_tail_ty, actual_tail_ty);
            tail_term
        };

        let ty = RawTy::sigma(head_name.clone(), head_ty, tail_ty);
        let term = RawTm::pair(head_term, tail_term);
        let term = RawTyped::from_parts(ty, term);

        Tm {
            raw_ctx: ctx.raw_ctx,
            raw_typed_term: term,
        }
    }

    pub fn to_ty(&self) -> Ty<N> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Universe = &*raw_ty.kind else {
            unreachable!();
        };
        let raw_ty = match &*raw_term.kind {
            RawTmKind::Stuck { stuck } => {
                let stuck = stuck.clone_unfilter(&raw_term.usages);
                RawTy::stuck(stuck)
            },
            RawTmKind::Type { ty } => {
                ty.clone_unfilter(&raw_term.usages)
            },
            _ => unreachable!(),
        };
        Ty {
            raw_ctx: raw_ctx.clone(),
            raw_ty,
        }
    }

    pub fn to_scope(&self) -> Scope<N, Tm<N>> {
        let ty = self.ty();
        let RawTyKind::Pi { arg_name, arg_ty, res_ty: _ } = &*ty.raw_ty.kind else {
            unreachable!()
        };
        let arg_ty = arg_ty.clone_unfilter(&ty.raw_ty.usages);
        let arg_ty = Ty {
            raw_ctx: ty.raw_ctx,
            raw_ty: arg_ty,
        };
        arg_ty.named_scope(arg_name, |arg_term| self.app(&arg_term))
    }

    pub fn for_loop(
        &self,
        motive: impl FnOnce(Tm<N>) -> Ty<N>,
        zero_inhab: &Tm<N>,
        succ_inhab: impl FnOnce(Tm<N>, Tm<N>) -> Tm<N>,
    ) -> Tm<N> {
        let (Ctx { ctx_len, raw_ctx }, elim, zero_inhab) = Ctx::merge_into_ctx_2(self, zero_inhab);
        let (raw_ty, raw_term) = elim.to_parts();
        let RawTyKind::Nat = &*raw_ty.kind else {
            unreachable!();
        };

        let motive = raw_scope(&raw_ctx, None, &raw_ty, motive);

        let zero_inhab = {
            let (actual_zero_inhab_ty, zero_inhab) = zero_inhab.into_parts();
            let expected_zero_inhab_ty = motive.clone().bind(&RawTm::zero(ctx_len));
            assert_eq!(actual_zero_inhab_ty, expected_zero_inhab_ty);
            zero_inhab
        };

        let succ_inhab = raw_scope_2(&raw_ctx, None, &raw_ty, None, &motive.clone().into_inner(), succ_inhab);
        let succ_inhab = {
            let (actual_succ_inhab_ty, succ_inhab) = succ_inhab.into_parts();
            let expected_succ_inhab_ty = RawScope::new(RawScope::new(
                motive
                .clone_weaken(2)
                .bind(&RawTm::succs(NonZeroBigUint::one(), RawTm::var(ctx_len + 2, ctx_len)))
            ));
            assert_eq!(actual_succ_inhab_ty, expected_succ_inhab_ty);
            succ_inhab
        };

        let ty = motive.clone().bind(&raw_term);
        let term = RawTm::for_loop(raw_term, motive, zero_inhab, succ_inhab);
        let raw_typed_term = RawTyped::from_parts(ty, term);

        Tm { raw_ctx, raw_typed_term }
    }

    pub fn cong(
        &self,
        motive: impl FnOnce(Tm<N>, Tm<N>, Tm<N>) -> Ty<N>,
        inhab: impl FnOnce(Tm<N>) -> Tm<N>,
    ) -> Tm<N> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = &*raw_ty.kind else {
            unreachable!();
        };
        let eq_ty = eq_ty.clone_unfilter(&raw_ty.usages);
        let eq_term_0 = eq_term_0.clone_unfilter(&raw_ty.usages);
        let eq_term_1 = eq_term_1.clone_unfilter(&raw_ty.usages);

        let motive = raw_scope_3(
            raw_ctx,
            None,
            &eq_ty,
            None,
            &eq_ty.clone_weaken(1),
            None,
            &RawTy::equal(
                eq_ty.clone_weaken(2),
                RawTm::var(ctx_len + 2, ctx_len),
                RawTm::var(ctx_len + 2, ctx_len + 1),
            ),
            motive,
        );

        let inhab = raw_scope(raw_ctx, None, &eq_ty, inhab);

        let inhab = {
            let (actual_inhab_ty, inhab) = inhab.into_parts();
            let expected_inhab_ty = RawScope::new(
                motive
                .clone_weaken(1)
                .bind3(
                    &RawTm::var(ctx_len + 1, ctx_len),
                    &RawTm::var(ctx_len + 1, ctx_len),
                    &RawTm::refl(ctx_len + 1),
                ),
            );
            assert_eq!(actual_inhab_ty, expected_inhab_ty);
            inhab
        };

        let ty = motive.clone().bind3(&eq_term_0, &eq_term_1, &raw_term);
        let term = RawTm::cong(eq_ty, eq_term_0, eq_term_1, raw_term, motive, inhab);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn explode(
        &self, 
        motive: impl FnOnce(Tm<N>) -> Ty<N>,
    ) -> Tm<N> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Never = &*raw_ty.kind else {
            unreachable!();
        };

        let motive = raw_scope(raw_ctx, None, &raw_ty, motive);

        let ty = motive.clone().bind(&raw_term);
        let term = RawTm::explode(raw_term, motive);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn relay(
        &self,
        motive: impl FnOnce(Tm<N>) -> Ty<N>,
        inhab: &Tm<N>,
    ) -> Tm<N> {
        let (Ctx { ctx_len, raw_ctx }, elim, inhab) = Ctx::merge_into_ctx_2(self, inhab);

        let (raw_ty, raw_term) = elim.into_parts();
        let RawTyKind::Unit = &*raw_ty.kind else {
            unreachable!();
        };

        let motive = raw_scope(&raw_ctx, None, &raw_ty, motive);

        let inhab = {
            let (actual_inhab_ty, inhab) = inhab.into_parts();
            let expected_inhab_ty = motive.clone().bind(&RawTm::unit(ctx_len));
            assert_eq!(actual_inhab_ty, expected_inhab_ty);
            inhab
        };

        let ty = motive.clone().bind(&raw_term);
        let term = RawTm::relay(raw_term, motive, inhab);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx,
            raw_typed_term: term,
        }
    }

    pub fn case(
        &self,
        motive: impl FnOnce(Tm<N>) -> Ty<N>,
        lhs_inhab: impl FnOnce(Tm<N>) -> Tm<N>,
        rhs_inhab: impl FnOnce(Tm<N>) -> Tm<N>,
    ) -> Tm<N> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty } = &*raw_ty.kind else {
            unreachable!();
        };
        let lhs_ty = lhs_ty.clone_unfilter(&raw_ty.usages);
        let rhs_ty = rhs_ty.clone_unfilter(&raw_ty.usages);

        let motive = raw_scope(raw_ctx, None, &raw_ty, motive);

        let lhs_inhab = raw_scope(raw_ctx, Some(lhs_name.clone()), &lhs_ty, lhs_inhab);
        let lhs_inhab = {
            let (actual_lhs_inhab_ty, lhs_inhab) = lhs_inhab.into_parts();
            let expected_lhs_inhab_ty = RawScope::new(
                motive
                .clone_weaken(1)
                .bind(&RawTm::inj_lhs(RawTm::var(ctx_len + 1, ctx_len)))
            );
            assert_eq!(actual_lhs_inhab_ty, expected_lhs_inhab_ty);
            lhs_inhab
        };

        let rhs_inhab = raw_scope(raw_ctx, None, &rhs_ty, rhs_inhab);
        let rhs_inhab = {
            let (actual_rhs_inhab_ty, rhs_inhab) = rhs_inhab.into_parts();
            let expected_rhs_inhab_ty = RawScope::new(
                motive
                .clone_weaken(1)
                .bind(&RawTm::inj_rhs(RawTm::var(ctx_len + 1, ctx_len)))
            );
            assert_eq!(actual_rhs_inhab_ty, expected_rhs_inhab_ty);
            rhs_inhab
        };

        let ty = motive.clone().bind(&raw_term);
        let term = RawTm::case(lhs_name.clone(), lhs_ty, rhs_ty, raw_term, motive, lhs_inhab, rhs_inhab);
        let term = RawTyped::from_parts(ty, term);

        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn split(
        &self,
        motive: impl FnOnce(Tm<N>) -> Ty<N>,
        inhab: impl FnOnce(Tm<N>, Tm<N>) -> Tm<N>,
    ) -> Tm<N> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Sigma { head_name, head_ty, tail_ty } = &*raw_ty.kind else {
            unreachable!();
        };
        let head_ty = head_ty.clone_unfilter(&raw_ty.usages);
        let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);

        let motive = raw_scope(raw_ctx, None, &raw_ty, motive);

        let tail_ty_inner = tail_ty.clone().into_inner();
        let inhab = raw_scope_2(raw_ctx, Some(head_name.clone()), &head_ty, None, &tail_ty_inner, inhab);
        let inhab = {
            let (actual_inhab_ty, inhab) = inhab.into_parts();
            let expected_inhab_ty = RawScope::new(
                RawScope::new(
                    motive
                    .clone_weaken(2)
                    .bind(&RawTm::pair(RawTm::var(ctx_len + 2, ctx_len), RawTm::var(ctx_len + 2, ctx_len + 1)))
                ),
            );
            assert_eq!(actual_inhab_ty, expected_inhab_ty);
            inhab
        };

        let ty = motive.clone().bind(&raw_term);
        let term = RawTm::split(head_name.clone(), head_ty, tail_ty, raw_term, motive, inhab);
        let term = RawTyped::from_parts(ty, term);
        
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn app(
        &self,
        arg_term: &Tm<N>,
    ) -> Tm<N> {
        let (Ctx { raw_ctx, .. }, elim, arg_term) = Ctx::merge_into_ctx_2(self, arg_term);
        let (raw_ty, raw_term) = elim.into_parts();
        let RawTyKind::Pi { arg_name, arg_ty, res_ty } = &*raw_ty.kind else {
            unreachable!();
        };
        let arg_ty = arg_ty.clone_unfilter(&raw_ty.usages);
        let res_ty = res_ty.clone_unfilter(&raw_ty.usages);
        
        let arg_term = {
            let (actual_arg_ty, arg_term) = arg_term.into_parts();
            assert_eq!(actual_arg_ty, arg_ty);
            arg_term
        };

        let ty = res_ty.clone().bind(&arg_term);
        let term = RawTm::app(arg_name.clone(), arg_ty, res_ty, raw_term, arg_term);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx,
            raw_typed_term: term,
        }
    }
}

impl<N: Name> Stuck<N> {
    pub fn ctx(&self) -> Ctx<N> {
        Ctx {
            ctx_len: self.raw_typed_stuck.usages.len(),
            raw_ctx: self.raw_ctx.clone(),
        }
    }

    pub fn ty(&self) -> Ty<N> {
        let Stuck { raw_ctx, raw_typed_stuck } = self;
        let (raw_ty, _) = raw_typed_stuck.to_parts();
        Ty {
            raw_ctx: raw_ctx.clone(),
            raw_ty,
        }
    }

    pub fn to_term(&self) -> Tm<N> {
        let Stuck { raw_ctx, raw_typed_stuck } = self;
        let (raw_ty, raw_stuck) = raw_typed_stuck.to_parts();
        let raw_term = RawTm::stuck(raw_stuck);
        let raw_typed_term = RawTyped::from_parts(raw_ty, raw_term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term,
        }
    }

    pub fn to_ty(&self) -> Ty<N> {
        let Stuck { raw_ctx, raw_typed_stuck } = self;
        let (raw_ty, raw_stuck) = raw_typed_stuck.to_parts();
        let RawTyKind::Universe = &*raw_ty.kind else {
            unreachable!();
        };
        let raw_ty = RawTy::stuck(raw_stuck);
        Ty {
            raw_ctx: raw_ctx.clone(),
            raw_ty,
        }
    }

    pub fn kind(&self) -> StuckKind<N> {
        let ctx_len = self.raw_typed_stuck.usages.len();
        let Stuck { raw_ctx, raw_typed_stuck } = self;
        let (_raw_ty, raw_stuck) = raw_typed_stuck.to_parts();
        match &*raw_stuck.kind {
            RawStuckKind::Var => {
                let index = raw_stuck.usages.index_of_single_one().unwrap();
                StuckKind::Var { index }
            },

            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);
                let zero_inhab = zero_inhab.clone_unfilter(&raw_stuck.usages);
                let succ_inhab = succ_inhab.clone_unfilter(&raw_stuck.usages);

                let elim = RawTyped::from_parts(RawTy::nat(ctx_len), elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let zero_inhab_ty = motive.clone().bind(&RawTm::zero(ctx_len));
                let zero_inhab = RawTyped::from_parts(zero_inhab_ty, zero_inhab);
                let zero_inhab = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: zero_inhab,
                };

                let succ_inhab_ty = {
                    motive
                    .clone_weaken(2)
                    .bind(&RawTm::succs(NonZeroBigUint::one(), RawTm::var(ctx_len + 2, ctx_len)))
                };
                let succ_inhab = succ_inhab.into_inner();
                let succ_inhab = succ_inhab.into_inner();
                let succ_inhab = RawTyped::from_parts(succ_inhab_ty, succ_inhab);
                let succ_inhab = RawScope::new(succ_inhab);
                let succ_inhab = RawTyped::from_parts(
                    motive.clone_weaken(1).bind(&RawTm::var(ctx_len + 1, ctx_len)),
                    succ_inhab,
                );
                let succ_inhab = RawScope::new(succ_inhab);
                let succ_inhab = RawTyped::from_parts(RawTy::nat(ctx_len), succ_inhab);
                let succ_inhab = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: succ_inhab,
                };

                let motive = RawTyped::from_parts(RawTy::nat(ctx_len), motive);
                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: motive,
                };

                StuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab }
            },

            /*
            RawStuckKind::Max { max_term_0, max_term_1 } => {
                let max_term_0 = max_term_0.clone_unfilter(&raw_stuck.usages);
                let max_term_1 = max_term_1.clone_unfilter(&raw_stuck.usages);

                let max_term_0 = RawTyped::from_parts(RawTy::nat(ctx_len), max_term_0);
                let max_term_0 = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: max_term_0,
                };

                let max_term_1 = RawTyped::from_parts(RawTy::nat(ctx_len), max_term_1);
                let max_term_1 = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: max_term_1,
                };

                StuckKind::Max { max_term_0, max_term_1 }
            },
            */

            RawStuckKind::Cong { eq_ty, eq_term_0, eq_term_1, elim, motive, inhab } => {
                let eq_ty = eq_ty.clone_unfilter(&raw_stuck.usages);
                let eq_term_0 = eq_term_0.clone_unfilter(&raw_stuck.usages);
                let eq_term_1 = eq_term_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);
                let inhab = inhab.clone_unfilter(&raw_stuck.usages);

                let elim_ty = RawTy::equal(eq_ty.clone(), eq_term_0, eq_term_1);
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let inhab_ty = {
                    motive
                    .clone_weaken(1)
                    .bind3(
                        &RawTm::var(ctx_len + 1, ctx_len),
                        &RawTm::var(ctx_len + 1, ctx_len),
                        &RawTm::refl(ctx_len + 1),
                    )
                };
                let inhab_ty = RawScope::new(inhab_ty);
                let inhab = RawScope::from_parts_1(inhab_ty, inhab);
                let inhab = RawTyped::from_parts(
                    eq_ty.clone(),
                    inhab,
                );
                let inhab = Scope { raw_ctx: raw_ctx.clone(), raw_typed_scope: inhab };

                let motive = motive.into_inner();
                let motive = motive.into_inner();
                let motive = motive.into_inner();
                let motive = RawTyped::from_parts(
                    RawTy::equal(
                        eq_ty.clone_weaken(2),
                        RawTm::var(ctx_len + 2, ctx_len),
                        RawTm::var(ctx_len + 2, ctx_len + 1),
                    ),
                    RawScope::new(motive),
                );
                let motive = RawTyped::from_parts(
                    eq_ty.clone_weaken(1),
                    RawScope::new(motive),
                );
                let motive = RawTyped::from_parts(
                    eq_ty,
                    RawScope::new(motive),
                );
                let motive = Scope { raw_ctx: raw_ctx.clone(), raw_typed_scope: motive };

                StuckKind::Cong { elim, motive, inhab }
            },

            RawStuckKind::Explode { elim, motive } => {
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);

                let elim = RawTyped::from_parts(RawTy::never(ctx_len), elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let motive = RawTyped::from_parts(RawTy::never(ctx_len), motive);
                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: motive,
                };

                StuckKind::Explode { elim, motive }
            },

            RawStuckKind::Relay { elim, motive, inhab } => {
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);
                let inhab = inhab.clone_unfilter(&raw_stuck.usages);

                let elim = RawTyped::from_parts(RawTy::unit(ctx_len), elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let inhab_ty = motive.clone().bind(&RawTm::unit(ctx_len));
                let inhab = RawTyped::from_parts(inhab_ty, inhab);
                let inhab = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: inhab,
                };

                let motive = RawTyped::from_parts(RawTy::unit(ctx_len), motive);
                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: motive,
                };

                StuckKind::Relay { elim, motive, inhab }
            },

            RawStuckKind::Case { lhs_name, lhs_ty, rhs_ty, elim, motive, lhs_inhab, rhs_inhab } => {
                let lhs_ty = lhs_ty.clone_unfilter(&raw_stuck.usages);
                let rhs_ty = rhs_ty.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);
                let lhs_inhab = lhs_inhab.clone_unfilter(&raw_stuck.usages);
                let rhs_inhab = rhs_inhab.clone_unfilter(&raw_stuck.usages);

                let lhs_inhab_ty = {
                    motive
                    .clone_weaken(1)
                    .bind(&RawTm::inj_lhs(RawTm::var(ctx_len + 1, ctx_len)))
                };
                let lhs_inhab = lhs_inhab.into_inner();
                let lhs_inhab = RawTyped::from_parts(lhs_inhab_ty, lhs_inhab);
                let lhs_inhab = RawTyped::from_parts(
                    lhs_ty.clone(),
                    RawScope::new(lhs_inhab),
                );
                let lhs_inhab = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: lhs_inhab,
                };

                let rhs_inhab_ty = {
                    motive
                    .clone_weaken(1)
                    .bind(&RawTm::inj_rhs(RawTm::var(ctx_len + 1, ctx_len)))
                };
                let rhs_inhab = rhs_inhab.into_inner();
                let rhs_inhab = RawTyped::from_parts(rhs_inhab_ty, rhs_inhab);
                let rhs_inhab = RawTyped::from_parts(
                    rhs_ty.clone(),
                    RawScope::new(rhs_inhab),
                );
                let rhs_inhab = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: rhs_inhab,
                };

                let elim_ty = RawTy::sum(lhs_name.clone(), lhs_ty.clone(), rhs_ty.clone());
                let elim = RawTyped::from_parts(elim_ty.clone(), elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let motive = RawTyped::from_parts(elim_ty, motive);
                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: motive,
                };

                StuckKind::Case { elim, motive, lhs_inhab, rhs_inhab }
            },

            RawStuckKind::Split { head_name, head_ty, tail_ty, elim, motive, inhab } => {
                let head_ty = head_ty.clone_unfilter(&raw_stuck.usages);
                let tail_ty = tail_ty.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);
                let inhab = inhab.clone_unfilter(&raw_stuck.usages);

                let elim_ty = RawTy::sigma(head_name.clone(), head_ty.clone(), tail_ty.clone());
                let elim = RawTyped::from_parts(elim_ty.clone(), elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let inhab_ty = {
                    motive
                    .clone_weaken(2)
                    .bind(&RawTm::pair(RawTm::var(ctx_len + 2, ctx_len), RawTm::var(ctx_len + 2, ctx_len + 1)))
                };
                let inhab = inhab.into_inner();
                let inhab = inhab.into_inner();
                let inhab = RawTyped::from_parts(inhab_ty, inhab);
                let inhab = RawTyped::from_parts(
                    tail_ty.clone_weaken(1).bind(&RawTm::var(ctx_len + 1, ctx_len)),
                    RawScope::new(inhab),
                );
                let inhab = RawTyped::from_parts(
                    head_ty.clone(),
                    RawScope::new(inhab),
                );
                let inhab = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: inhab,
                };

                let motive = RawTyped::from_parts(elim_ty, motive);
                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_scope: motive,
                };

                StuckKind::Split { elim, motive, inhab }
            },

            RawStuckKind::App { arg_name, arg_ty, res_ty, elim, arg_term } => {
                let arg_ty = arg_ty.clone_unfilter(&raw_stuck.usages);
                let res_ty = res_ty.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let arg_term = arg_term.clone_unfilter(&raw_stuck.usages);

                let elim_ty = RawTy::pi(arg_name.clone(), arg_ty.clone(), res_ty);
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let arg_term = RawTyped::from_parts(arg_ty, arg_term);
                let arg_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: arg_term,
                };

                StuckKind::App { elim, arg_term }
            },
        }
    }
}

impl<N: Name> ContextualSealed<N> for Ty<N> {
    type Raw = RawTy<N>;

    fn raw_ctx(&self) -> &RawCtx<N> {
        &self.raw_ctx
    }

    fn raw(&self) -> &RawTy<N> {
        &self.raw_ty
    }

    fn into_raw(self) -> RawTy<N> {
        self.raw_ty
    }

    fn from_raw(raw_ctx: RawCtx<N>, raw: RawTy<N>) -> Ty<N> {
        Ty {
            raw_ctx,
            raw_ty: raw,
        }
    }
}

impl<N: Name> ContextualSealed<N> for Tm<N> {
    type Raw = RawTyped<N, RawTm<N>>;

    fn raw_ctx(&self) -> &RawCtx<N> {
        &self.raw_ctx
    }

    fn raw(&self) -> &RawTyped<N, RawTm<N>> {
        &self.raw_typed_term
    }

    fn into_raw(self) -> RawTyped<N, RawTm<N>> {
        self.raw_typed_term
    }

    fn from_raw(raw_ctx: RawCtx<N>, raw: RawTyped<N, RawTm<N>>) -> Tm<N> {
        Tm {
            raw_ctx,
            raw_typed_term: raw,
        }
    }
}

impl<N: Name> ContextualSealed<N> for Stuck<N> {
    type Raw = RawTyped<N, RawStuck<N>>;

    fn raw_ctx(&self) -> &RawCtx<N> {
        &self.raw_ctx
    }

    fn raw(&self) -> &RawTyped<N, RawStuck<N>> {
        &self.raw_typed_stuck
    }

    fn into_raw(self) -> RawTyped<N, RawStuck<N>> {
        self.raw_typed_stuck
    }

    fn from_raw(raw_ctx: RawCtx<N>, raw: RawTyped<N, RawStuck<N>>) -> Stuck<N> {
        Stuck {
            raw_ctx,
            raw_typed_stuck: raw,
        }
    }
}

impl<N: Name, T: ContextualSealed<N>> ContextualSealed<N> for Scope<N, T>
where
    T::Raw: Clone,
{
    type Raw = RawTyped<N, RawScope<N, T::Raw>>;

    fn raw_ctx(&self) -> &RawCtx<N> {
        &self.raw_ctx
    }

    fn raw(&self) -> &RawTyped<N, RawScope<N, T::Raw>> {
        &self.raw_typed_scope
    }

    fn into_raw(self) -> RawTyped<N, RawScope<N, T::Raw>> {
        self.raw_typed_scope
    }

    fn from_raw(raw_ctx: RawCtx<N>, raw: RawTyped<N, RawScope<N, T::Raw>>) -> Scope<N, T> {
        Scope {
            raw_ctx,
            raw_typed_scope: raw,
        }
    }
}

impl<N: Name, T: Contextual<N>> Scope<N, T> {
    #[allow(private_bounds)]
    pub fn unbind(&self) -> impl FnOnce(Tm<N>) -> T
    where
        T: SubstInvariant<N>,
    {
        |var_term| self.bind(&var_term)
    }

    #[allow(private_bounds)]
    pub fn bind(&self, term: &Tm<N>) -> T
    where
        T: SubstInvariant<N>,
    {
        let (ctx, raw_typed_scope, raw_typed_term) = Ctx::merge_into_ctx_2(self, term);
        let (expected_raw_ty, raw_scope) = raw_typed_scope.into_parts();
        let (actual_raw_ty, raw_term) = raw_typed_term.into_parts();
        assert_eq!(actual_raw_ty, expected_raw_ty);

        let inner = raw_scope.bind(&raw_term);
        T::from_raw(ctx.raw_ctx, inner)
    }

    pub fn map<U: Contextual<N>>(&self, func: impl FnOnce(Tm<N>, T) -> U) -> Scope<N, U> {
        let ctx_len = self.raw_typed_scope.usages.len();
        let (raw_ty, raw_scope) = self.raw_typed_scope.to_parts();
        let inner = raw_scope.into_inner();
        let raw_ctx = self.raw_ctx.cons(None, raw_ty.clone());
        let var_term = Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(raw_ty.clone_weaken(1), RawTm::var(ctx_len + 1, ctx_len)),
        };
        let inner = T::from_raw(raw_ctx.clone(), inner);
        let inner = func(var_term, inner);
        assert_eq!(inner.raw_ctx(), &raw_ctx);
        let inner = inner.into_raw();
        let raw_scope = RawScope::new(inner);
        let raw_typed_scope = RawTyped::from_parts(raw_ty, raw_scope);
        Scope {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_scope,
        }
    }

    pub fn try_map<Y>(
        &self,
        func: impl FnOnce(Tm<N>, T) -> Y,
    ) -> <Y::Residual as Residual<Scope<N, Y::Output>>>::TryType
    where
        Y: Try,
        Y::Output: Contextual<N>,
        Y::Residual: Residual<Scope<N, Y::Output>>,
    {
        let ctx_len = self.raw_typed_scope.usages.len();
        let (raw_ty, raw_scope) = self.raw_typed_scope.to_parts();
        let inner = raw_scope.into_inner();
        let raw_ctx = self.raw_ctx.cons(None, raw_ty.clone());
        let var_term = Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(raw_ty.clone_weaken(1), RawTm::var(ctx_len + 1, ctx_len)),
        };
        let inner = T::from_raw(raw_ctx.clone(), inner);
        let inner_res = func(var_term, inner);
        match inner_res.branch() {
            ControlFlow::Break(err) => {
                <<Y::Residual as Residual<Scope<N, Y::Output>>>::TryType as FromResidual>::from_residual(err)
            },
            ControlFlow::Continue(inner) => {
                let scope = {
                    assert_eq!(inner.raw_ctx(), &raw_ctx);
                    let inner = inner.into_raw();
                    let raw_scope = RawScope::new(inner);
                    let raw_typed_scope = RawTyped::from_parts(raw_ty, raw_scope);
                    Scope {
                        raw_ctx: self.raw_ctx.clone(),
                        raw_typed_scope,
                    }
                };
                <<Y::Residual as Residual<Scope<N, Y::Output>>>::TryType as Try>::from_output(scope)
            },
        }
    }

    pub fn into_inner(self) -> T {
        let Scope { raw_ctx, raw_typed_scope } = self;
        let (raw_ty, raw_scope) = raw_typed_scope.to_parts();
        let inner = raw_scope.into_inner();
        T::from_raw(raw_ctx.cons(None, raw_ty.clone()), inner)
    }

    pub fn var_ty(&self) -> Ty<N> {
        let Scope { raw_ctx, raw_typed_scope } = self;
        let (raw_ty, _raw_scope) = raw_typed_scope.to_parts();
        Ty::from_raw(raw_ctx.clone(), raw_ty)
    }

    pub fn try_strengthen(&self) -> Option<T>
    where
        T: SubstInvariant<N>,
    {
        if self.raw_typed_scope.inner.var_used {
            None
        } else {
            let Scope { raw_ctx, raw_typed_scope } = self;
            let (_raw_var_ty, raw_scope) = raw_typed_scope.to_parts();
            let raw_inner = raw_scope.inner.clone_unfilter(&raw_scope.usages);
            Some(T::from_raw(raw_ctx.clone(), raw_inner))
        }
    }
}

impl<N: Name> Scope<N, Ty<N>> {
    pub fn to_pi(&self, arg_name: &N) -> Ty<N> {
        let arg_ty = self.var_ty();
        arg_ty.pi(arg_name, self.unbind())
    }
}

impl<N: Name> Scope<N, Tm<N>> {
    pub fn to_func(&self, arg_name: &N) -> Tm<N> {
        let arg_ty = self.var_ty();
        arg_ty.func(arg_name, self.unbind())
    }
}

impl<N: Name> Scope<N, Scope<N, Ty<N>>> {
    pub fn unsplit(&self, head_name: &N) -> Scope<N, Ty<N>> {
        let head_ty = self.var_ty();
        let tail_ty = self.map(|_head_term, scope| scope.var_ty());
        let sigma_ty = head_ty.sigma(head_name, tail_ty.unbind());
        sigma_ty.scope(|pair_term| {
            pair_term
            .split(
                |pair_term| pair_term.ctx().universe(),
                |head_term, tail_term| self.bind(&head_term).bind(&tail_term).to_term(),
            )
            .to_ty()
        })
    }
}

impl<N: Name> Scope<N, Scope<N, Tm<N>>> {
    pub fn unsplit(&self, head_name: &N) -> Scope<N, Tm<N>> {
        let head_ty = self.var_ty();
        let tail_ty = self.map(|_head_term, scope| scope.var_ty());
        let motive = self.map(|_head_term, scope| scope.map(|_tail_term, inner| inner.ty()));
        let sigma_ty = head_ty.sigma(head_name, tail_ty.unbind());
        sigma_ty.scope(|pair_term| {
            pair_term
            .split(
                motive.unsplit(head_name).unbind(),
                |head_term, tail_term| self.bind(&head_term).bind(&tail_term),
            )
        })
    }
}

fn try_raw_scope<N: Name, Y>(
    raw_ctx: &RawCtx<N>,
    var_name_opt: Option<N>,
    var_ty: &RawTy<N>,
    func: impl FnOnce(Tm<N>) -> Y,
) -> <Y::Residual as Residual<RawScope<N, <Y::Output as ContextualSealed<N>>::Raw>>>::TryType
where
    Y: Try,
    Y::Output: ContextualSealed<N>,
    Y::Residual: Residual<RawScope<N, <Y::Output as ContextualSealed<N>>::Raw>>,
{
    let ctx_len = var_ty.usages().len();
    let raw_ctx = raw_ctx.cons(var_name_opt, var_ty.clone());
    let var_term = {
        let ty = var_ty.clone_weaken(1);
        let term = RawTm::var(ctx_len + 1, ctx_len);
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
                    Y::Residual as Residual<RawScope<N, <Y::Output as ContextualSealed<N>>::Raw>>
                >::TryType as FromResidual
            >::from_residual(err)
        },
        ControlFlow::Continue(inner) => {
            let raw_scope = {
                let inner_ctx_len = inner.raw().usages_len();
                let diff = (ctx_len + 1).strict_sub(inner_ctx_len);
                assert_eq!(raw_ctx.nth_parent(diff), inner.raw_ctx());

                let mut inner = inner.into_raw();
                inner.weaken(diff);
                RawScope::new(inner)
            };
            <
                <
                    Y::Residual as Residual<RawScope<N, <Y::Output as ContextualSealed<N>>::Raw>>
                >::TryType as Try
            >::from_output(raw_scope)
        },
    }
}

fn raw_scope<N: Name, T: ContextualSealed<N>>(
    raw_ctx: &RawCtx<N>,
    var_name_opt: Option<N>,
    var_ty: &RawTy<N>,
    func: impl FnOnce(Tm<N>) -> T,
) -> RawScope<N, T::Raw> {
    let ctx_len = var_ty.usages.len();
    let raw_ctx = raw_ctx.cons(var_name_opt, var_ty.clone());
    let var_term = {
        let ty = var_ty.clone_weaken(1);
        let term = RawTm::var(ctx_len + 1, ctx_len);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };

    let inner = func(var_term);

    let inner_ctx_len = inner.raw().usages_len();
    let diff = (ctx_len + 1).strict_sub(inner_ctx_len);
    assert_eq!(raw_ctx.nth_parent(diff), inner.raw_ctx());

    let mut inner = inner.into_raw();
    inner.weaken(diff);
    RawScope::new(inner)
}

fn raw_scope_2<N: Name, T: ContextualSealed<N>>(
    raw_ctx: &RawCtx<N>,
    var_name_opt_0: Option<N>,
    var_ty_0: &RawTy<N>,
    var_name_opt_1: Option<N>,
    var_ty_1: &RawTy<N>,
    func: impl FnOnce(Tm<N>, Tm<N>) -> T,
) -> RawScope<N, RawScope<N, T::Raw>> {
    let ctx_len = var_ty_0.usages.len();
    assert_eq!(ctx_len + 1, var_ty_1.usages.len());

    let raw_ctx = raw_ctx.cons(var_name_opt_0, var_ty_0.clone()).cons(var_name_opt_1, var_ty_1.clone());
    let var_term_0 = {
        let ty = var_ty_0.clone_weaken(2);
        let term = RawTm::var(ctx_len + 2, ctx_len);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };
    let var_term_1 = {
        let ty = var_ty_1.clone_weaken(1);
        let term = RawTm::var(ctx_len + 2, ctx_len + 1);
        let term = RawTyped::from_parts(ty, term);
        Tm { 
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };

    let inner = func(var_term_0, var_term_1);

    let inner_ctx_len = inner.raw().usages_len();
    let diff = (ctx_len + 2).strict_sub(inner_ctx_len);
    assert_eq!(raw_ctx.nth_parent(diff), inner.raw_ctx());

    let mut inner = inner.into_raw();
    inner.weaken(diff);
    RawScope::new(RawScope::new(inner))
}

fn raw_scope_3<N: Name, T: ContextualSealed<N>>(
    raw_ctx: &RawCtx<N>,
    var_name_opt_0: Option<N>,
    var_ty_0: &RawTy<N>,
    var_name_opt_1: Option<N>,
    var_ty_1: &RawTy<N>,
    var_name_opt_2: Option<N>,
    var_ty_2: &RawTy<N>,
    func: impl FnOnce(Tm<N>, Tm<N>, Tm<N>) -> T,
) -> RawScope<N, RawScope<N, RawScope<N, T::Raw>>> {
    let ctx_len = var_ty_0.usages.len();
    assert_eq!(ctx_len + 1, var_ty_1.usages.len());
    assert_eq!(ctx_len + 2, var_ty_2.usages.len());

    let raw_ctx = {
        raw_ctx
        .cons(var_name_opt_0, var_ty_0.clone())
        .cons(var_name_opt_1, var_ty_1.clone())
        .cons(var_name_opt_2, var_ty_2.clone())
    };
    let var_term_0 = {
        let ty = var_ty_0.clone_weaken(3);
        let term = RawTm::var(ctx_len + 3, ctx_len);
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };
    let var_term_1 = {
        let ty = var_ty_1.clone_weaken(2);
        let term = RawTm::var(ctx_len + 3, ctx_len + 1);
        let term = RawTyped::from_parts(ty, term);
        Tm { 
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };
    let var_term_2 = {
        let ty = var_ty_2.clone_weaken(1);
        let term = RawTm::var(ctx_len + 3, ctx_len + 2);
        let term = RawTyped::from_parts(ty, term);
        Tm { 
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    };

    let inner = func(var_term_0, var_term_1, var_term_2);

    let inner_ctx_len = inner.raw().usages_len();
    let diff = (ctx_len + 3).strict_sub(inner_ctx_len);
    assert_eq!(raw_ctx.nth_parent(diff), inner.raw_ctx());

    let mut inner = inner.into_raw();
    inner.weaken(diff);
    RawScope::new(RawScope::new(RawScope::new(inner)))
}

