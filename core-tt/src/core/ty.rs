use crate::priv_prelude::*;

#[derive_where(Clone, PartialEq)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Ty<S: Scheme> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) raw_ty: RawTy<S>,
}

#[derive_where(Clone, Debug)]
pub enum TyKind<S: Scheme> {
    Stuck {
        stuck: Stuck<S>,
    },
    User {
        user_ty: S::UserTy,
    },
    Universe,
    Nat,
    Equal {
        eq_term_0: Tm<S>,
        eq_term_1: Tm<S>,
    },
    Never,
    Unit,
    Sum {
        lhs_ty: Ty<S>,
        rhs_ty: Ty<S>,
    },
    Sigma {
        tail_ty: Scope<S, Ty<S>>,
    },
    Pi {
        res_ty: Scope<S, Ty<S>>,
    },
}

impl<S: Scheme> Contextual<S> for Ty<S> {
    type Raw = Intern<RawTyKind<S>>;

    fn into_raw(self) -> (Ctx<S>, RawTy<S>) {
        let Ty { raw_ctx, raw_ty } = self;
        let ctx = Ctx { raw_ctx };
        (ctx, raw_ty)
    }

    fn from_raw(ctx: Ctx<S>, raw: RawTy<S>) -> Ty<S> {
        Ty {
            raw_ctx: ctx.raw_ctx,
            raw_ty: raw,
        }
    }

    fn ctx(&self) -> Ctx<S> {
        let raw_ctx = self.raw_ctx.clone();
        Ctx { raw_ctx }
    }

    fn eliminates_var(&self, index: usize) -> bool {
        self.raw_ty.eliminates_var(index)
    }
}

impl<S: Scheme> Ty<S> {
    pub fn ctx(&self) -> Ctx<S> {
        Ctx {
            raw_ctx: self.raw_ctx.clone(),
        }
    }

    pub fn usages(&self) -> &Usages {
        &self.raw_ty.usages
    }

    pub fn transitive_usages(&self) -> Usages {
        let mut usages = self.raw_ty.usages.clone();
        self.raw_ctx.fill_transitive_usages(&mut usages);
        usages
    }

    pub fn with_ctx(&self, ctx: &Ctx<S>) -> Ty<S> {
        let diff = ctx.len().strict_sub(self.raw_ty.usages.len());
        assert_eq!(&self.raw_ctx, ctx.raw_ctx.nth_parent(diff));
        let raw_ctx = ctx.raw_ctx.clone();
        let raw_ty = self.raw_ty.clone_weaken(diff);
        Ty { raw_ctx, raw_ty }
    }

    pub fn cons(&self) -> Ctx<S> {
        self.ctx().cons(self)
    }

    pub fn with_cons<T>(&self, func: impl FnOnce(Tm<S>) -> T) -> T {
        self.ctx().with_cons(self, func)
    }

    pub fn contains_var(&self, index: usize) -> bool {
        self.raw_ty.usages[index]
    }

    pub fn to_scope(&self) -> Scope<S, Ty<S>> {
        let Ty { raw_ctx, raw_ty } = self;
        let RawTyKind::Pi { res_ty } = raw_ty.weak.get_clone() else {
            unreachable!()
        };
        let res_ty = res_ty.clone_unfilter(&raw_ty.usages);
        Scope {
            raw_ctx: raw_ctx.clone(),
            raw_scope: res_ty,
        }
    }
    
    pub fn kind(&self) -> TyKind<S> {
        let Ty { raw_ctx, raw_ty } = self;
        match raw_ty.weak.get_clone() {
            RawTyKind::Stuck { stuck } => {
                let raw_stuck = stuck.clone_unfilter(&raw_ty.usages);
                let raw_ty = RawTy::universe(raw_ty.usages.len());
                let stuck = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: RawTyped::from_parts(raw_ty, raw_stuck),
                };
                TyKind::Stuck { stuck }
            },
            RawTyKind::User { user_ty } => TyKind::User { user_ty },
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
            RawTyKind::Sum { lhs_ty, rhs_ty } => {
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
                TyKind::Sum { lhs_ty, rhs_ty }
            },
            RawTyKind::Sigma { tail_ty } => {
                let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);
                let tail_ty = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: tail_ty,
                };
                TyKind::Sigma { tail_ty }
            },
            RawTyKind::Pi { res_ty } => {
                let res_ty = res_ty.clone_unfilter(&raw_ty.usages);
                let res_ty = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: res_ty,
                };
                TyKind::Pi { res_ty }
            },
        }
    }

    pub fn sum(
        lhs_ty: &Ty<S>,
        rhs_ty: &Ty<S>,
    ) -> Ty<S> {
        let (ctx, lhs_ty, rhs_ty) = Ctx::merge_into_ctx_2(lhs_ty, rhs_ty);
        let raw_ctx = ctx.raw_ctx;
        let raw_ty = RawTy::sum(lhs_ty, rhs_ty);
        Ty { raw_ctx, raw_ty }
    }

    pub fn sigma(
        &self,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Ty<S> {
        let head_ty = self;
        let tail_ty = raw_scope(&head_ty.raw_ctx, &head_ty.raw_ty, tail_ty);

        let raw_ctx = head_ty.raw_ctx.clone();
        let raw_ty = RawTy::sigma(tail_ty);
        Ty { raw_ctx, raw_ty }
    }

    pub fn pi(
        &self,
        res_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Ty<S> {
        let arg_ty = self;
        let res_ty = raw_scope(&arg_ty.raw_ctx, &arg_ty.raw_ty, res_ty);

        let raw_ctx = arg_ty.raw_ctx.clone();
        let raw_ty = RawTy::pi(res_ty);
        Ty { raw_ctx, raw_ty }
    }

    pub fn func(
        &self,
        res_term: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let arg_ty = self;
        let res_term = raw_scope(&arg_ty.raw_ctx, &arg_ty.raw_ty, res_term);

        let (res_ty, res_term) = res_term.into_parts();

        let ty = RawTy::pi(res_ty);
        let term = RawTm::func(res_term);
        let term = RawTyped::from_parts(ty, term);

        Tm { raw_ctx: arg_ty.raw_ctx.clone(), raw_typed_term: term }
    }

    pub fn scope<T: Contextual<S>>(&self, func: impl FnOnce(Tm<S>) -> T) -> Scope<S, T> {
        let raw_scope = raw_scope(&self.raw_ctx, &self.raw_ty, func);
        Scope {
            raw_ctx: self.raw_ctx.clone(),
            raw_scope,
        }
    }

    #[allow(private_bounds)]
    pub fn try_scope<Y>(
        &self,
        func: impl FnOnce(Tm<S>) -> Y,
    ) -> <Y::Residual as Residual<Scope<S, Y::Output>>>::TryType
    where
        Y: Try,
        Y::Output: Contextual<S>,
        Y::Residual: Residual<Scope<S, Y::Output>>,
        Y::Residual: Residual<RawScope<S, <Y::Output as Contextual<S>>::Raw>>,
    {
        let raw_scope = try_raw_scope(&self.raw_ctx, &self.raw_ty, func)?;
        let scope = Scope {
            raw_ctx: self.raw_ctx.clone(),
            raw_scope,
        };
        <<Y::Residual as Residual<Scope<S, Y::Output>>>::TryType as Try>::from_output(scope)
    }

    pub fn to_term(&self) -> Tm<S> {
        let Ty { raw_ctx, raw_ty } = self;
        let ctx_len = raw_ty.usages.len();

        let term = RawTm::from_ty(raw_ty.clone());
        let term = RawTyped::from_parts(RawTy::universe(ctx_len), term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn strong_ctx_len(&self) -> usize {
        self.raw_ty.usages.strong_ctx_len()
    }

    pub fn unique_term_opt(&self) -> Option<Tm<S>> {
        let raw_term = self.raw_ty.unique_eta_term_opt(&mut Vec::new())?;
        let raw_typed_term = RawTyped::from_parts(self.raw_ty.clone(), raw_term);
        Some(Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term,
        })
    }

    /*
    pub fn unwrap_universe(&self) {
        match self.kind() {
            TyKind::Universe => (),
            _ => {
                panic!(
                    "unwrap_universe(): self is not universe.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }

    pub fn unwrap_nat(&self) {
        match self.kind() {
            TyKind::Nat => (),
            _ => {
                panic!(
                    "unwrap_nat(): self is not nat.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }

    pub fn unwrap_equal(&self) -> (Tm<S>, Tm<S>) {
        match self.kind() {
            TyKind::Equal { eq_term_0, eq_term_1 } => (eq_term_0, eq_term_1),
            _ => {
                panic!(
                    "unwrap_nat(): self is not an equality type.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }

    pub fn unwrap_never(&self) {
        match self.kind() {
            TyKind::Never => (),
            _ => {
                panic!(
                    "unwrap_nat(): self is not never.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }

    pub fn unwrap_unit(&self) {
        match self.kind() {
            TyKind::Unit => (),
            _ => {
                panic!(
                    "unwrap_unit(): self is not unit.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }

    pub fn unwrap_sum(&self) -> (Ty<S>, Ty<S>) {
        match self.kind() {
            TyKind::Sum { lhs_ty, rhs_ty } => (lhs_ty, rhs_ty),
            _ => {
                panic!(
                    "unwrap_unit(): self is not a sum type.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }

    pub fn unwrap_sigma(&self) -> Scope<S, Ty<S>> {
        match self.kind() {
            TyKind::Sigma { tail_ty } => tail_ty,
            _ => {
                panic!(
                    "unwrap_unit(): self is not a sigma type.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }

    pub fn unwrap_pi(&self) -> Scope<S, Ty<S>> {
        match self.kind() {
            TyKind::Pi { res_ty } => res_ty,
            _ => {
                panic!(
                    "unwrap_unit(): self is not a pi type.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }
    */
}

