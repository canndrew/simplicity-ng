use crate::priv_prelude::*;

/// The type for representing types.
#[derive_where(Clone)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Ty<S: Scheme> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) raw_ty: RawTy<S>,
}

impl<S: Scheme> PartialEq for Ty<S> {
    fn eq(&self, other: &Ty<S>) -> bool {
        let (_, (ty_0, ty_1)) = merge_ctxs((self, other));
        ty_0 == ty_1
    }
}

#[derive_where(Clone, Debug)]
pub enum TyKind<S: Scheme> {
    Stuck {
        stuck: Stuck<S>,
    },
    Name,
    Universe,
    Nat,
    Equal {
        eq_term_0: Tm<S>,
        eq_term_1: Tm<S>,
    },
    Never,
    Unit,
    Sum {
        lhs_name: Name<S>,
        lhs_ty: Ty<S>,
        rhs_ty: Ty<S>,
    },
    Sigma {
        head_name: Name<S>,
        tail_ty: Scope<S, Ty<S>>,
    },
    Pi {
        arg_name: Name<S>,
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

    fn contains_subterm(&self, subterm: &RawTm<S>) -> bool {
        self.raw_ty.contains_subterm(subterm)
    }
}

impl<S: Scheme> Ty<S> {
    /// Returns the context of `self`.
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

    /// Returns the context of `self` extended with a single variable of type `self`.
    pub fn cons(&self) -> Ctx<S> {
        self.ctx().cons(self)
    }

    /// Evaluates `func` under the context of `self` extended with a single variable of type
    /// `self`.
    ///
    /// The term passed to `func` is the variable of type `self`.
    pub fn with_cons<T>(&self, func: impl FnOnce(Tm<S>) -> T) -> T {
        let ctx_len = self.raw_ctx.len();
        let raw_typed_term = RawTyped::from_parts(
            self.raw_ty.clone_weaken(1),
            RawTm::var(ctx_len + 1, ctx_len, &self.raw_ty),
        );
        let var_term = Tm {
            raw_ctx: self.raw_ctx.cons(self.raw_ty.clone()),
            raw_typed_term,
        };
        func(var_term)
    }

    /// Checks whether `self` refers to the variable at index `index`.
    pub fn contains_var(&self, index: usize) -> bool {
        self.raw_ty.usages[index]
    }

    /// Returns a scoped type, assuming self is a [TyKind::Pi] type.
    ///
    /// # Panics
    ///
    /// If `self` is not of the form [TyKind::Pi].
    pub fn to_scope(&self) -> Scope<S, Ty<S>> {
        let Ty { raw_ctx, raw_ty } = self;
        let RawTyKind::Pi { arg_name: _, res_ty } = raw_ty.weak.get_clone() else {
            panic!("\
                to_scope(): self is not a pi type.\n\
                self: {:?}",
                self,
            );
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
            RawTyKind::Name => TyKind::Name,
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
                let lhs_name = lhs_name.clone_unfilter(&raw_ty.usages);
                let lhs_ty = lhs_ty.clone_unfilter(&raw_ty.usages);
                let rhs_ty = rhs_ty.clone_unfilter(&raw_ty.usages);
                let lhs_name = Name {
                    raw_ctx: raw_ctx.clone(),
                    raw_name: lhs_name,
                };
                let lhs_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: lhs_ty,
                };
                let rhs_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: rhs_ty,
                };
                TyKind::Sum { lhs_name, lhs_ty, rhs_ty }
            },
            RawTyKind::Sigma { head_name, tail_ty } => {
                let head_name = head_name.clone_unfilter(&raw_ty.usages);
                let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);
                let head_name = Name {
                    raw_ctx: raw_ctx.clone(),
                    raw_name: head_name,
                };
                let tail_ty = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: tail_ty,
                };
                TyKind::Sigma { head_name, tail_ty }
            },
            RawTyKind::Pi { arg_name, res_ty } => {
                let arg_name = arg_name.clone_unfilter(&raw_ty.usages);
                let res_ty = res_ty.clone_unfilter(&raw_ty.usages);
                let arg_name = Name {
                    raw_ctx: raw_ctx.clone(),
                    raw_name: arg_name,
                };
                let res_ty = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: res_ty,
                };
                TyKind::Pi { arg_name, res_ty }
            },
        }
    }

    /// Returns the [TyKind::Sum] type with `self` as the left type and the given name and right
    /// type.
    pub fn sum(
        &self,
        lhs_name: &Name<S>,
        rhs_ty: &Ty<S>,
    ) -> Ty<S> {
        let (ctx, (lhs_name, lhs_ty, rhs_ty)) = merge_ctxs((lhs_name, self, rhs_ty));
        let raw_ctx = ctx.raw_ctx;
        let raw_ty = RawTy::sum(lhs_name, lhs_ty, rhs_ty);
        Ty { raw_ctx, raw_ty }
    }

    /// Returns the [TyKind::Sigma] type with `self` as the head type and the given name and tail
    /// type.
    pub fn sigma(
        &self,
        head_name: &Name<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Ty<S> {
        let (ctx, (head_name, head_ty)) = merge_ctxs((head_name, self));
        let raw_ctx = ctx.raw_ctx;
        let tail_ty = raw_scope(&raw_ctx, &head_ty, tail_ty);

        let raw_ty = RawTy::sigma(head_name, tail_ty);
        Ty { raw_ctx, raw_ty }
    }

    /// Returns the [TyKind::Pi] type with `self` as the argument type and the given argument name
    /// and result type.
    pub fn pi(
        &self,
        arg_name: &Name<S>,
        res_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Ty<S> {
        let (ctx, (arg_name, arg_ty)) = merge_ctxs((arg_name, self));
        let raw_ctx = ctx.raw_ctx;
        let res_ty = raw_scope(&raw_ctx, &arg_ty, res_ty);

        let raw_ty = RawTy::pi(arg_name, res_ty);
        Ty { raw_ctx, raw_ty }
    }

    /// Returns a function (ie. a term of type [TyKind::Pi]) with `self` as the argument type.
    pub fn func(
        &self,
        arg_name: &Name<S>,
        res_term: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let (ctx, (arg_name, arg_ty)) = merge_ctxs((arg_name, self));
        let raw_ctx = ctx.raw_ctx;
        let res_term = raw_scope(&raw_ctx, &arg_ty, res_term);

        let (res_ty, res_term) = res_term.into_parts();

        let ty = RawTy::pi(arg_name.clone(), res_ty);
        let term = RawTm::func(arg_name, res_term);
        let term = RawTyped::from_parts(ty, term);

        Tm { raw_ctx, raw_typed_term: term }
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
    ) -> Y::AltOutput<Scope<S, Y::Output>>
    where
        Y: MyTry,
        Y::Output: Contextual<S>,
    {
        let raw_scope = match try_raw_scope(&self.raw_ctx, &self.raw_ty, func).branch() {
            ControlFlow::Continue(rs) => rs,
            ControlFlow::Break(err) => return Y::AltOutput::from_residual(err),
        };
        let scope = Scope {
            raw_ctx: self.raw_ctx.clone(),
            raw_scope,
        };
        Y::AltOutput::from_output(scope)
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
                    "unwrap_equal(): self is not an equality type.\n\
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
                    "unwrap_never(): self is not never.\n\
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

    pub fn unwrap_sum(&self) -> (Name<S>, Ty<S>, Ty<S>) {
        match self.kind() {
            TyKind::Sum { lhs_name, lhs_ty, rhs_ty } => (lhs_name, lhs_ty, rhs_ty),
            _ => {
                panic!(
                    "unwrap_sum(): self is not a sum type.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }

    pub fn unwrap_sigma(&self) -> (Name<S>, Scope<S, Ty<S>>) {
        match self.kind() {
            TyKind::Sigma { head_name, tail_ty } => (head_name, tail_ty),
            _ => {
                panic!(
                    "unwrap_sigma(): self is not a sigma type.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }

    pub fn unwrap_pi(&self) -> (Name<S>, Scope<S, Ty<S>>) {
        match self.kind() {
            TyKind::Pi { arg_name, res_ty } => (arg_name, res_ty),
            _ => {
                panic!(
                    "unwrap_pi(): self is not a pi type.\n\
                    self: {:?}",
                    self,
                );
            },
        }
    }
}

