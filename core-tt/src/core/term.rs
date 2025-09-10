use crate::priv_prelude::*;

#[derive_where(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Tm<S: Scheme> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) raw_typed_term: RawTyped<S, Intern<RawTmKind<S>>>,
}

#[derive_where(Clone)]
pub enum TmKind<S: Scheme> {
    Stuck {
        stuck: Stuck<S>,
    },
    User {
        user_term: S::UserTm,
    },
    Type {
        ty: Ty<S>,
    },
    Zero,
    Succs {
        count: NonZeroBigUint,
        pred_term: Tm<S>,
    },
    Refl {
        eq_term: Tm<S>,
    },
    Unit,
    InjLhs {
        lhs_term: Tm<S>,
        rhs_ty: Ty<S>,
    },
    InjRhs {
        rhs_term: Tm<S>,
        lhs_ty: Ty<S>,
    },
    Pair {
        tail_ty: Scope<S, Ty<S>>,
        head_term: Tm<S>,
        tail_term: Tm<S>,
    },
    Func {
        res_term: Scope<S, Tm<S>>,
    },
}

impl<S: Scheme> Contextual<S> for Tm<S> {
    type Raw = RawTypedKind<S, Intern<RawTmKind<S>>>;

    fn into_raw(self) -> (Ctx<S>, RawTyped<S, Intern<RawTmKind<S>>>) {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx = Ctx { raw_ctx };
        (ctx, raw_typed_term)
    }

    fn from_raw(ctx: Ctx<S>, raw: RawTyped<S, Intern<RawTmKind<S>>>) -> Tm<S> {
        Tm {
            raw_ctx: ctx.raw_ctx,
            raw_typed_term: raw,
        }
    }

    fn ctx(&self) -> Ctx<S> {
        let raw_ctx = self.raw_ctx.clone();
        Ctx { raw_ctx }
    }

    fn eliminates_var(&self, index: usize) -> bool {
        self.raw_typed_term.eliminates_var(index)
    }
}

impl<S: Scheme> Tm<S> {
    pub fn ctx(&self) -> Ctx<S> {
        Ctx {
            raw_ctx: self.raw_ctx.clone(),
        }
    }

    pub fn usages(&self) -> &Usages {
        &self.raw_typed_term.usages
    }

    pub fn transitive_usages(&self) -> Usages {
        let mut usages = self.raw_typed_term.weak.inner.usages.clone_unfilter(&self.raw_typed_term.usages);
        self.raw_ctx.fill_transitive_usages(&mut usages);
        usages
    }

    pub fn ty(&self) -> Ty<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, _) = raw_typed_term.to_parts();
        Ty {
            raw_ctx: raw_ctx.clone(),
            raw_ty,
        }
    }

    pub fn kind(&self) -> TmKind<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        match raw_term.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let raw_stuck = stuck.clone_unfilter(&raw_term.usages);
                let stuck = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: RawTyped::from_parts(raw_ty, raw_stuck),
                };
                TmKind::Stuck { stuck }
            },
            RawTmKind::User { user_term } => {
                TmKind::User { user_term }
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
            RawTmKind::Refl => {
                let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
                    unreachable!();
                };
                let eq_term = if cfg!(debug_assertions) {
                    as_equal(eq_term_0, eq_term_1).unwrap()
                } else {
                    eq_term_0
                };
                let eq_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(eq_ty, eq_term),
                };
                TmKind::Refl { eq_term }
            },
            RawTmKind::Unit => TmKind::Unit,
            RawTmKind::InjLhs { lhs_term } => {
                let RawTyKind::Sum { lhs_ty, rhs_ty } = raw_ty.weak.get_clone() else {
                    unreachable!();
                };

                let lhs_term = lhs_term.clone_unfilter(&raw_term.usages);
                let lhs_ty = lhs_ty.clone_unfilter(&raw_ty.usages);
                let lhs_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(lhs_ty, lhs_term),
                };
                let rhs_ty = rhs_ty.clone_unfilter(&raw_ty.usages);
                let rhs_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: rhs_ty,
                };
                TmKind::InjLhs { lhs_term, rhs_ty }
            },
            RawTmKind::InjRhs { rhs_term } => {
                let RawTyKind::Sum { lhs_ty, rhs_ty } = raw_ty.weak.get_clone() else {
                    unreachable!();
                };

                let rhs_term = rhs_term.clone_unfilter(&raw_term.usages);
                let rhs_ty = rhs_ty.clone_unfilter(&raw_ty.usages);
                let rhs_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(rhs_ty, rhs_term),
                };
                let lhs_ty = lhs_ty.clone_unfilter(&raw_ty.usages);
                let lhs_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: lhs_ty,
                };
                TmKind::InjRhs { rhs_term, lhs_ty }
            },
            RawTmKind::Pair { head_term, tail_term } => {
                let RawTyKind::Sigma { tail_ty } = raw_ty.weak.get_clone() else {
                    unreachable!();
                };

                let head_term = head_term.clone_unfilter(&raw_term.usages);
                let tail_term = tail_term.clone_unfilter(&raw_term.usages);
                let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);
                let head_ty = tail_ty.var_ty_unfiltered();

                let tail_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(tail_ty.clone().bind(&head_term), tail_term),
                };
                let head_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(head_ty, head_term),
                };
                let tail_ty = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: tail_ty,
                };
                TmKind::Pair { tail_ty, head_term, tail_term }
            },
            RawTmKind::Func { res_term } => {
                let RawTyKind::Pi { res_ty } = raw_ty.weak.get_clone() else {
                    unreachable!();
                };

                let res_term = res_term.clone_unfilter(&raw_term.usages);
                let res_ty = res_ty.clone_unfilter(&raw_ty.usages);

                let res_term = RawScope::from_parts_1(res_ty, res_term);
                let res_term = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: res_term,
                };
                TmKind::Func { res_term }
            },
        }
    }

    pub fn contains_var(&self, index: usize) -> bool {
        self.raw_typed_term.usages[index]
    }

    pub fn zero() -> Tm<S> {
        Tm {
            raw_ctx: RawCtx::root(),
            raw_typed_term: RawTyped::from_parts(RawTy::never(0), RawTm::zero(0)),
        }
    }

    pub fn succs(&self, count: impl Into<BigUint>) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Nat = raw_ty.weak.get_clone() else {
            panic!(
                "succs(): self is not a nat.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let Some(count) = NonZeroBigUint::new(count.into()) else {
            return self.clone();
        };

        let raw_typed_term = RawTyped::from_parts(raw_ty, RawTm::succs(count, raw_term));

        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term,
        }
    }

    pub fn max(&self, rhs: &Tm<S>) -> Tm<S> {
        let (Ctx { raw_ctx }, lhs_term, rhs_term) = Ctx::merge_into_ctx_2(self, rhs);

        let (lhs_ty, lhs_term) = lhs_term.into_parts();
        let (rhs_ty, rhs_term) = rhs_term.into_parts();
        
        let RawTyKind::Nat = lhs_ty.weak.get_clone() else {
            panic!(
                "max(): left argument is not a nat.
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Nat = rhs_ty.weak.get_clone() else {
            panic!(
                "max(): right argument is not a nat.
                rhs.ty(): {:?}",
                rhs.ty(),
            );
        };

        let raw_term = RawTm::max(lhs_term, rhs_term);
        let raw_ty = RawTy::nat(raw_term.usages.len());
        let raw_typed_term = RawTyped::from_parts(raw_ty, raw_term);

        Tm { raw_ctx, raw_typed_term }
    }

    pub fn add(&self, rhs: &Tm<S>) -> Tm<S> {
        let (Ctx { raw_ctx }, lhs_term, rhs_term) = Ctx::merge_into_ctx_2(self, rhs);

        let (lhs_ty, lhs_term) = lhs_term.into_parts();
        let (rhs_ty, rhs_term) = rhs_term.into_parts();
        
        let RawTyKind::Nat = lhs_ty.weak.get_clone() else {
            panic!(
                "add(): left argument is not a nat.
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Nat = rhs_ty.weak.get_clone() else {
            panic!(
                "add(): right argument is not a nat.
                rhs.ty(): {:?}",
                rhs.ty(),
            );
        };

        let raw_term = RawTm::add(lhs_term, rhs_term);
        let raw_ty = RawTy::nat(raw_term.usages.len());
        let raw_typed_term = RawTyped::from_parts(raw_ty, raw_term);

        Tm { raw_ctx, raw_typed_term }
    }

    pub fn mul(&self, rhs: &Tm<S>) -> Tm<S> {
        let (Ctx { raw_ctx }, lhs_term, rhs_term) = Ctx::merge_into_ctx_2(self, rhs);

        let (lhs_ty, lhs_term) = lhs_term.into_parts();
        let (rhs_ty, rhs_term) = rhs_term.into_parts();
        
        let RawTyKind::Nat = lhs_ty.weak.get_clone() else {
            panic!(
                "mul(): left argument is not a nat.
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Nat = rhs_ty.weak.get_clone() else {
            panic!(
                "mul(): left argument is not a nat.
                rhs.ty(): {:?}",
                rhs.ty(),
            );
        };

        let raw_term = RawTm::mul(lhs_term, rhs_term);
        let raw_ty = RawTy::nat(raw_term.usages.len());
        let raw_typed_term = RawTyped::from_parts(raw_ty, raw_term);

        Tm { raw_ctx, raw_typed_term }
    }

    pub fn equals(&self, other: &Tm<S>) -> Ty<S> {
        let eq_term_0 = self;
        let eq_term_1 = other;

        let (ctx, eq_term_0, eq_term_1) = Ctx::merge_into_ctx_2(eq_term_0, eq_term_1);
        let (eq_ty_0, eq_term_0) = eq_term_0.into_parts();
        let (eq_ty_1, eq_term_1) = eq_term_1.into_parts();
        let Some(eq_ty) = as_equal(eq_ty_0, eq_ty_1) else {
            panic!(
                "\
                x.equals(y): x and y have different types.\n\
                x.ty(): {:?}\n\
                y.ty(): {:?}\n\
                ",
                self.ty(),
                other.ty(),
            );
        };
        
        let raw_ty = RawTy::equal(eq_ty, eq_term_0, eq_term_1);
        Ty { raw_ctx: ctx.raw_ctx, raw_ty }
    }

    pub fn refl(&self) -> Tm<S> {
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

    pub fn unit() -> Tm<S> {
        Tm {
            raw_ctx: RawCtx::root(),
            raw_typed_term: RawTyped::from_parts(RawTy::unit(0), RawTm::unit(0)),
        }
    }

    pub fn inj_lhs(&self, rhs_ty: &Ty<S>) -> Tm<S> {
        let lhs_term = self;
        
        let (ctx, lhs_term, rhs_ty) = Ctx::merge_into_ctx_2(lhs_term, rhs_ty);
        let (lhs_ty, lhs_term) = lhs_term.into_parts();
        let ty = RawTy::sum(lhs_ty, rhs_ty);
        let term = RawTm::inj_lhs(lhs_term);
        let term = RawTyped::from_parts(ty, term);
        Tm { raw_ctx: ctx.raw_ctx, raw_typed_term: term }
    }

    pub fn inj_rhs(&self, lhs_ty: &Ty<S>) -> Tm<S> {
        let rhs_term = self;
        
        let (ctx, lhs_ty, rhs_term) = Ctx::merge_into_ctx_2(lhs_ty, rhs_term);
        let (rhs_ty, rhs_term) = rhs_term.into_parts();
        let ty = RawTy::sum(lhs_ty, rhs_ty);
        let term = RawTm::inj_rhs(rhs_term);
        let term = RawTyped::from_parts(ty, term);
        Tm { raw_ctx: ctx.raw_ctx, raw_typed_term: term }
    }

    pub fn pair(
        &self,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_term: &Tm<S>,
    ) -> Tm<S> {
        let head_term = self;
        
        let (ctx, head_term, tail_term) = Ctx::merge_into_ctx_2(head_term, tail_term);
        let (head_ty, head_term) = head_term.into_parts();
        let tail_ty = raw_scope(&ctx.raw_ctx, &head_ty, tail_ty);
        let tail_term = {
            let expected_tail_ty = tail_ty.clone().bind(&head_term);
            let (actual_tail_ty, tail_term) = tail_term.into_parts();
            if expected_tail_ty != actual_tail_ty {
                let expected_tail_ty = Ty {
                    raw_ctx: ctx.raw_ctx.clone(),
                    raw_ty: expected_tail_ty,
                };
                let actual_tail_ty = Ty {
                    raw_ctx: ctx.raw_ctx.clone(),
                    raw_ty: actual_tail_ty,
                };
                panic!(
                    "pair(): tail type mismatch.\n\
                    expected: {:?}\n\
                    got: {:?}",
                    expected_tail_ty,
                    actual_tail_ty,
                );
            }
            tail_term
        };

        let ty = RawTy::sigma(tail_ty);
        let term = RawTm::pair(head_term, tail_term);
        let term = RawTyped::from_parts(ty, term);

        Tm {
            raw_ctx: ctx.raw_ctx,
            raw_typed_term: term,
        }
    }

    pub fn to_ty(&self) -> Ty<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Universe = raw_ty.weak.get_clone() else {
            panic!("term is not a type: {:#?}", raw_ty.weak);
        };
        let raw_ty = RawTy::from_term(raw_term);
        Ty {
            raw_ctx: raw_ctx.clone(),
            raw_ty,
        }
    }

    pub fn to_scope(&self) -> Scope<S, Tm<S>> {
        let ty = self.ty();
        let RawTyKind::Pi { res_ty } = ty.raw_ty.weak.get_clone() else {
            panic!(
                "to_scope(): self is not a function.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let res_ty = res_ty.clone_unfilter(&ty.raw_ty.usages);
        let arg_ty = res_ty.var_ty_unfiltered();
        let arg_ty = Ty {
            raw_ctx: ty.raw_ctx,
            raw_ty: arg_ty,
        };
        arg_ty.scope(|arg_term| self.app(&arg_term))
    }

    pub fn for_loop(
        &self,
        motive: impl FnOnce(Tm<S>) -> Ty<S>,
        zero_inhab: &Tm<S>,
        succ_inhab: impl FnOnce(Tm<S>, Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let (Ctx { raw_ctx }, elim, zero_inhab) = Ctx::merge_into_ctx_2(self, zero_inhab);
        let ctx_len = raw_ctx.len();
        let (raw_ty, raw_term) = elim.to_parts();
        let RawTyKind::Nat = raw_ty.weak.get_clone() else {
            panic!(
                "for_loop(): self is not a nat.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let motive = raw_scope(&raw_ctx, &raw_ty, motive);

        let zero_inhab = {
            let (actual_zero_inhab_ty, zero_inhab) = zero_inhab.into_parts();
            let expected_zero_inhab_ty = motive.clone().bind(&RawTm::zero(ctx_len));
            assert_eq!(actual_zero_inhab_ty, expected_zero_inhab_ty);
            zero_inhab
        };

        let (motive_inner, _) = motive.clone().into_inner();
        let succ_inhab = raw_scope_2(&raw_ctx, &raw_ty, &motive_inner, succ_inhab);
        let succ_inhab = {
            let (actual_succ_inhab_ty, succ_inhab) = succ_inhab.into_parts();
            let expected_succ_inhab_ty = RawScope::new(
                raw_ty.clone(),
                RawScope::new(
                    motive_inner,
                    motive
                    .clone_weaken(2)
                    .bind(
                        &RawTm::succs(
                            NonZeroBigUint::one(),
                            RawTm::var(ctx_len + 2, ctx_len, &raw_ty),
                        ),
                    ),
                ),
            );
            assert_eq!(actual_succ_inhab_ty, expected_succ_inhab_ty);
            succ_inhab
        };

        let ty = motive.clone().bind(&raw_term);
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::for_loop(raw_term, motive, zero_inhab, succ_inhab),
        };
        let raw_typed_term = RawTyped::from_parts(ty, term);

        Tm { raw_ctx, raw_typed_term }
    }

    pub fn cong(
        &self,
        motive: impl FnOnce(Tm<S>, Tm<S>, Tm<S>) -> Ty<S>,
        inhab: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!(
                "cong(): self is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let eq_ty = eq_ty.clone_unfilter(&raw_ty.usages);
        let eq_term_0 = eq_term_0.clone_unfilter(&raw_ty.usages);
        let eq_term_1 = eq_term_1.clone_unfilter(&raw_ty.usages);

        let motive = raw_scope_3(
            raw_ctx,
            &eq_ty,
            &eq_ty.clone_weaken(1),
            &RawTy::equal(
                eq_ty.clone_weaken(2),
                RawTm::var(ctx_len + 2, ctx_len, &eq_ty),
                RawTm::var(ctx_len + 2, ctx_len + 1, &eq_ty.clone_weaken(1)),
            ),
            motive,
        );

        let inhab = raw_scope(raw_ctx, &eq_ty, inhab);

        let inhab = {
            let (actual_inhab_ty, inhab) = inhab.into_parts();
            let expected_inhab_ty = RawScope::new(
                eq_ty.clone(),
                motive
                .clone_weaken(1)
                .bind(&RawTm::var(ctx_len + 1, ctx_len, &eq_ty))
                .bind(&RawTm::var(ctx_len + 1, ctx_len, &eq_ty))
                .bind(&RawTm::refl(ctx_len + 1)),
            );
            if actual_inhab_ty != expected_inhab_ty {
                let expected_inhab_ty: Scope<S, Ty<S>> = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: expected_inhab_ty,
                };
                let actual_inhab_ty: Scope<S, Ty<S>> = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: actual_inhab_ty,
                };
                println!("expected inhab ty == {:?}", expected_inhab_ty);
                println!("actual inhab ty == {:?}", actual_inhab_ty);
                panic!("type mismatch");
            }
            inhab
        };

        let ty = {
            motive
            .clone()
            .bind(&eq_term_0)
            .bind(&eq_term_1)
            .bind(&raw_term)
        };
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::cong(eq_term_0, eq_term_1, raw_term, motive, inhab),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn unique_identity(
        &self,
        motive: impl FnOnce(Tm<S>, Tm<S>) -> Ty<S>,
        inhab: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!(
                "unique_identity(): self is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let eq_term = as_equal(eq_term_0, eq_term_1).unwrap();
        let eq_ty = eq_ty.clone_unfilter(&raw_ty.usages);
        let eq_term = eq_term.clone_unfilter(&raw_ty.usages);

        let motive = raw_scope_2(
            raw_ctx,
            &eq_ty,
            &RawTy::equal(
                eq_ty.clone_weaken(1),
                RawTm::var(ctx_len + 1, ctx_len, &eq_ty),
                RawTm::var(ctx_len + 1, ctx_len, &eq_ty),
            ),
            motive,
        );

        let inhab = raw_scope(raw_ctx, &eq_ty, inhab);

        let inhab = {
            let (actual_inhab_ty, inhab) = inhab.into_parts();
            let expected_inhab_ty = RawScope::new(
                eq_ty.clone(),
                motive
                .clone_weaken(1)
                .bind(&RawTm::var(ctx_len + 1, ctx_len, &eq_ty))
                .bind(&RawTm::refl(ctx_len + 1)),
            );
            assert_eq!(actual_inhab_ty, expected_inhab_ty);
            inhab
        };

        let ty = {
            motive
            .clone()
            .bind(&eq_term)
            .bind(&raw_term)
        };
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::unique_identity(eq_term, raw_term, motive, inhab),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn explode(
        &self, 
        motive: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Never = raw_ty.weak.get_clone() else {
            panic!(
                "explode(): self is not a never.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let motive = raw_scope(raw_ctx, &raw_ty, motive);

        let ty = motive.clone().bind(&raw_term);
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::explode(raw_term, motive),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn case(
        &self,
        motive: impl FnOnce(Tm<S>) -> Ty<S>,
        lhs_inhab: impl FnOnce(Tm<S>) -> Tm<S>,
        rhs_inhab: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Sum { lhs_ty, rhs_ty } = raw_ty.weak.get_clone() else {
            panic!(
                "case(): self is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let lhs_ty = lhs_ty.clone_unfilter(&raw_ty.usages);
        let rhs_ty = rhs_ty.clone_unfilter(&raw_ty.usages);

        let motive = raw_scope(raw_ctx, &raw_ty, motive);

        let lhs_inhab = raw_scope(raw_ctx, &lhs_ty, lhs_inhab);
        let lhs_inhab = {
            let (actual_lhs_inhab_ty, lhs_inhab) = lhs_inhab.into_parts();
            let expected_lhs_inhab_ty = RawScope::new(
                lhs_ty.clone(),
                motive
                .clone_weaken(1)
                .bind(&RawTm::inj_lhs(RawTm::var(ctx_len + 1, ctx_len, &lhs_ty))),
            );
            assert_eq!(actual_lhs_inhab_ty, expected_lhs_inhab_ty);
            lhs_inhab
        };

        let rhs_inhab = raw_scope(raw_ctx, &rhs_ty, rhs_inhab);
        let rhs_inhab = {
            let (actual_rhs_inhab_ty, rhs_inhab) = rhs_inhab.into_parts();
            let expected_rhs_inhab_ty = RawScope::new(
                rhs_ty.clone(),
                motive
                .clone_weaken(1)
                .bind(&RawTm::inj_rhs(RawTm::var(ctx_len + 1, ctx_len, &rhs_ty))),
            );
            assert_eq!(actual_rhs_inhab_ty, expected_rhs_inhab_ty);
            rhs_inhab
        };

        let ty = motive.clone().bind(&raw_term);
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::case(raw_term, motive, lhs_inhab, rhs_inhab),
        };
        let term = RawTyped::from_parts(ty, term);

        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn proj_head(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Sigma { tail_ty } = raw_ty.weak.get_clone() else {
            panic!(
                "proj_head(): self is not a sigma.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);
        let head_ty = tail_ty.var_ty_unfiltered();

        let ty = head_ty;
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::proj_head(tail_ty, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn proj_tail(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Sigma { tail_ty } = raw_ty.weak.get_clone() else {
            panic!(
                "proj_tail(): self is not a sigma.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);

        let ty = {
            let head_term = RawTm::proj_head(tail_ty.clone(), raw_term.clone());
            tail_ty.clone().bind(&head_term)
        };
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::proj_tail(tail_ty, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn app(
        &self,
        arg_term: &Tm<S>,
    ) -> Tm<S> {
        let (Ctx { raw_ctx }, elim, arg_term) = Ctx::merge_into_ctx_2(self, arg_term);
        let (raw_ty, raw_term) = elim.into_parts();
        let RawTyKind::Pi { res_ty } = raw_ty.weak.get_clone() else {
            panic!("app(): {:#?} is not a function", self);
        };
        let res_ty = res_ty.clone_unfilter(&raw_ty.usages);
        let arg_ty = res_ty.var_ty_unfiltered();
        
        let arg_term = {
            let (actual_arg_ty, arg_term) = arg_term.into_parts();
            if actual_arg_ty != arg_ty {
                let expected_arg_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: arg_ty.clone(),
                };
                let actual_arg_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: actual_arg_ty.clone(),
                };
                panic!(
                    "app(): arg_ty mismatch.\n\
                    expected: {:?}\n\
                    got: {:?}",
                    expected_arg_ty,
                    actual_arg_ty,
                );
            }
            arg_term
        };

        let ty = res_ty.clone().bind(&arg_term);
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::app(res_ty, raw_term, arg_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx,
            raw_typed_term: term,
        }
    }

    pub fn equal_eq_eq_ty_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!(
                "equal_eq_eq_ty_injective(): self is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            panic!(
                "equal_eq_eq_ty_injective(): self is not an equality between types.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Equal {
            eq_ty: eq_ty_0, eq_term_0: eq_term_0_0, eq_term_1: eq_term_1_0,
        } = ty_0.weak.get_clone() else {
            panic!(
                "equal_eq_eq_ty_injective(): type on left side of equality\
                is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Equal {
            eq_ty: eq_ty_1, eq_term_0: eq_term_0_1, eq_term_1: eq_term_1_1,
        } = ty_1.weak.get_clone() else {
            panic!(
                "equal_eq_eq_ty_injective(): type on right side of equality\
                is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let eq_ty_0 = {
            eq_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_ty_1 = {
            eq_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_0_0 = {
            eq_term_0_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_0_1 = {
            eq_term_0_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_1_0 = {
            eq_term_1_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_1_1 = {
            eq_term_1_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };

        let ty = RawTy::equal(
            RawTy::universe(ctx_len),
            RawTm::from_ty(eq_ty_0.clone()),
            RawTm::from_ty(eq_ty_1.clone()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::equal_eq_eq_ty_injective(
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        let ret = Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        };
        // TODO: remove
        ret.sanity_check();
        ret
    }

    pub fn equal_eq_eq_term_0_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!(
                "equal_eq_eq_term_0_injective(): self is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            panic!(
                "equal_eq_eq_term_0_injective(): self is not an equality between types.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Equal {
            eq_ty: eq_ty_0, eq_term_0: eq_term_0_0, eq_term_1: eq_term_1_0,
        } = ty_0.weak.get_clone() else {
            panic!(
                "equal_eq_eq_term_0_injective(): type on left side of equality\
                is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Equal {
            eq_ty: eq_ty_1, eq_term_0: eq_term_0_1, eq_term_1: eq_term_1_1,
        } = ty_1.weak.get_clone() else {
            panic!(
                "equal_eq_eq_term_0_injective(): type on right side of equality\
                is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let eq_ty_0 = {
            eq_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_ty_1 = {
            eq_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_0_0 = {
            eq_term_0_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_0_1 = {
            eq_term_0_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_1_0 = {
            eq_term_1_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_1_1 = {
            eq_term_1_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };

        let ty = RawTy::heterogeneous_equal(
            eq_ty_0.clone(),
            eq_ty_1.clone(),
            RawTm::equal_eq_eq_ty_injective(
                eq_ty_0.clone(), eq_ty_1.clone(),
                eq_term_0_0.clone(), eq_term_0_1.clone(),
                eq_term_1_0.clone(), eq_term_1_1.clone(),
                raw_term.clone(),
            ),
            eq_term_0_0.clone(),
            eq_term_0_1.clone(),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::equal_eq_eq_term_0_injective(
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        let ret = Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        };
        // TODO: remove
        ret.sanity_check();
        ret
    }

    pub fn equal_eq_eq_term_1_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!(
                "equal_eq_eq_term_1_injective(): self is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            panic!(
                "equal_eq_eq_term_1_injective(): self is not an equality between types.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Equal {
            eq_ty: eq_ty_0, eq_term_0: eq_term_0_0, eq_term_1: eq_term_1_0,
        } = ty_0.weak.get_clone() else {
            panic!(
                "equal_eq_eq_term_1_injective(): type on left side of equality\
                is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Equal {
            eq_ty: eq_ty_1, eq_term_0: eq_term_0_1, eq_term_1: eq_term_1_1,
        } = ty_1.weak.get_clone() else {
            panic!(
                "equal_eq_eq_term_1_injective(): type on right side of equality\
                is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let eq_ty_0 = {
            eq_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_ty_1 = {
            eq_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_0_0 = {
            eq_term_0_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_0_1 = {
            eq_term_0_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_1_0 = {
            eq_term_1_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let eq_term_1_1 = {
            eq_term_1_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };

        let ty = RawTy::heterogeneous_equal(
            eq_ty_0.clone(),
            eq_ty_1.clone(),
            RawTm::equal_eq_eq_ty_injective(
                eq_ty_0.clone(), eq_ty_1.clone(),
                eq_term_0_0.clone(), eq_term_0_1.clone(),
                eq_term_1_0.clone(), eq_term_1_1.clone(),
                raw_term.clone(),
            ),
            eq_term_1_0.clone(),
            eq_term_1_1.clone(),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::equal_eq_eq_term_1_injective(
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        let ret = Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        };
        // TODO: remove
        ret.sanity_check();
        ret
    }

    pub fn sum_eq_lhs_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!(
                "sum_eq_lhs_injective(): self is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            panic!(
                "sum_eq_lhs_injective(): self is not an equality between types.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sum { lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 } = ty_0.weak.get_clone() else {
            panic!(
                "sum_eq_lhs_injective(): type on left side of equality\
                is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sum { lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 } = ty_1.weak.get_clone() else {
            panic!(
                "sum_eq_lhs_injective(): type on right side of equality\
                is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let lhs_ty_0 = {
            lhs_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let lhs_ty_1 = {
            lhs_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let rhs_ty_0 = {
            rhs_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let rhs_ty_1 = {
            rhs_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };

        let ty = RawTy::equal(
            RawTy::universe(ctx_len),
            RawTm::from_ty(lhs_ty_0.clone()),
            RawTm::from_ty(lhs_ty_1.clone()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::sum_eq_lhs_injective(lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn sum_eq_rhs_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!(
                "sum_eq_rhs_injective(): self is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            panic!(
                "sum_eq_rhs_injective(): self is not an equality between types.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sum { lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 } = ty_0.weak.get_clone() else {
            panic!(
                "sum_eq_rhs_injective(): type on left side of equality\
                is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sum { lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 } = ty_1.weak.get_clone() else {
            panic!(
                "sum_eq_rhs_injective(): type on right side of equality\
                is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let lhs_ty_0 = {
            lhs_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let lhs_ty_1 = {
            lhs_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let rhs_ty_0 = {
            rhs_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let rhs_ty_1 = {
            rhs_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };

        let ty = RawTy::equal(
            RawTy::universe(ctx_len),
            RawTm::from_ty(rhs_ty_0.clone()),
            RawTm::from_ty(rhs_ty_1.clone()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::sum_eq_rhs_injective(lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn sigma_eq_head_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            unreachable!();
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sigma { tail_ty: tail_ty_0 } = ty_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sigma { tail_ty: tail_ty_1 } = ty_1.weak.get_clone() else {
            unreachable!();
        };

        let tail_ty_0 = tail_ty_0.unfilter(&ty_0.usages).unfilter(&eq_term_0.usages).unfilter(&raw_ty.usages);
        let tail_ty_1 = tail_ty_1.unfilter(&ty_1.usages).unfilter(&eq_term_1.usages).unfilter(&raw_ty.usages);

        let ty = RawTy::equal(
            RawTy::universe(ctx_len),
            RawTm::from_ty(tail_ty_0.var_ty_unfiltered()),
            RawTm::from_ty(tail_ty_1.var_ty_unfiltered()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::sigma_eq_head_injective(tail_ty_0, tail_ty_1, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn sigma_eq_tail_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            unreachable!();
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sigma { tail_ty: tail_ty_0 } = ty_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sigma { tail_ty: tail_ty_1 } = ty_1.weak.get_clone() else {
            unreachable!();
        };

        let tail_ty_0 = tail_ty_0.unfilter(&ty_0.usages).unfilter(&eq_term_0.usages).unfilter(&raw_ty.usages);
        let tail_ty_1 = tail_ty_1.unfilter(&ty_1.usages).unfilter(&eq_term_1.usages).unfilter(&raw_ty.usages);

        let ty = RawTy::scoped_tys_congruence_ty(
            tail_ty_0.clone(),
            tail_ty_1.clone(),
            RawTm::sigma_eq_head_injective(tail_ty_0.clone(), tail_ty_1.clone(), raw_term.clone()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::sigma_eq_tail_injective(tail_ty_0, tail_ty_1, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn pi_eq_arg_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!("\
                pi_eq_arg_injective(): self is not an equality.\n\
                self.ty(): {:#?}",
                self.ty(),
            );
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            let eq_ty = eq_ty.clone_unfilter(&raw_ty.usages);
            let eq_ty = Ty {
                raw_ctx: raw_ctx.clone(),
                raw_ty: eq_ty,
            };
            panic!("\
                pi_eq_arg_injective(): self is not an equality between types.\n\
                equality_type: {:#?}",
                eq_ty,
            );
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Pi { res_ty: res_ty_0 } = ty_0.weak.get_clone() else {
            let ty_0 = ty_0.clone_unfilter(&eq_term_0.usages);
            let ty_0 = ty_0.unfilter(&raw_ty.usages);
            let ty_0 = Ty {
                raw_ctx: raw_ctx.clone(),
                raw_ty: ty_0,
            };
            panic!(
                "pi_eq_arg_injective(): type on left side of equality is not a pi type.\n\
                left type: {:#?}",
                ty_0,
            );
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Pi { res_ty: res_ty_1 } = ty_1.weak.get_clone() else {
            let ty_1 = ty_1.clone_unfilter(&eq_term_1.usages);
            let ty_1 = ty_1.unfilter(&raw_ty.usages);
            let ty_1 = Ty {
                raw_ctx: raw_ctx.clone(),
                raw_ty: ty_1,
            };
            panic!(
                "pi_eq_arg_injective(): type on right side of equality is not a pi type.\n\
                right type: {:#?}",
                ty_1,
            );
        };

        let res_ty_0 = {
            res_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let res_ty_1 = {
            res_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };

        let ty = RawTy::equal(
            RawTy::universe(ctx_len),
            RawTm::from_ty(res_ty_0.var_ty_unfiltered()),
            RawTm::from_ty(res_ty_1.var_ty_unfiltered()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::pi_eq_arg_injective(res_ty_0, res_ty_1, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn pi_eq_res_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!("\
                pi_eq_res_injective(): self is not an equality.\n\
                self.ty(): {:#?}",
                self.ty(),
            );
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            let eq_ty = eq_ty.clone_unfilter(&raw_ty.usages);
            let eq_ty = Ty {
                raw_ctx: raw_ctx.clone(),
                raw_ty: eq_ty,
            };
            panic!("\
                pi_eq_res_injective(): self is not an equality between types.\n\
                equality_type: {:#?}",
                eq_ty,
            );
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Pi { res_ty: res_ty_0 } = ty_0.weak.get_clone() else {
            let ty_0 = ty_0.clone_unfilter(&eq_term_0.usages);
            let ty_0 = ty_0.unfilter(&raw_ty.usages);
            let ty_0 = Ty {
                raw_ctx: raw_ctx.clone(),
                raw_ty: ty_0,
            };
            panic!(
                "pi_eq_res_injective(): type on left side of equality is not a pi type.\n\
                left type: {:#?}",
                ty_0,
            );
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Pi { res_ty: res_ty_1 } = ty_1.weak.get_clone() else {
            let ty_1 = ty_1.clone_unfilter(&eq_term_1.usages);
            let ty_1 = ty_1.unfilter(&raw_ty.usages);
            let ty_1 = Ty {
                raw_ctx: raw_ctx.clone(),
                raw_ty: ty_1,
            };
            panic!(
                "pi_eq_res_injective(): type on right side of equality is not a pi type.\n\
                right type: {:#?}",
                ty_1,
            );
        };

        let res_ty_0 = {
            res_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let res_ty_1 = {
            res_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };

        let ty = RawTy::scoped_tys_congruence_ty(
            res_ty_0.clone(),
            res_ty_1.clone(),
            RawTm::pi_eq_arg_injective(res_ty_0.clone(), res_ty_1.clone(), raw_term.clone()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::pi_eq_res_injective(res_ty_0, res_ty_1, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);

        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    pub fn scoped_tys_congruence_ty(
        &self,
        scoped_ty_0: impl FnOnce(Tm<S>) -> Ty<S>,
        scoped_ty_1: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Ty<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!("scoped_tys_congruence_ty(): self is not an equality");
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            panic!("scoped_tys_congruence_ty(): self is not an equality between types");
        };
        let eq_term_0 = eq_term_0.clone_unfilter(&raw_ty.usages);
        let eq_term_1 = eq_term_1.clone_unfilter(&raw_ty.usages);
        let var_ty_0 = RawTy::from_term(eq_term_0);
        let var_ty_1 = RawTy::from_term(eq_term_1);

        let scoped_ty_0 = raw_scope(raw_ctx, &var_ty_0, scoped_ty_0);
        let scoped_ty_1 = raw_scope(raw_ctx, &var_ty_1, scoped_ty_1);
        
        let raw_ty = RawTy::scoped_tys_congruence_ty(scoped_ty_0, scoped_ty_1, raw_term);
        let raw_ctx = raw_ctx.clone();
        Ty { raw_ctx, raw_ty }
    }

    pub fn as_var(&self) -> Option<usize> {
        let raw_term = self.raw_typed_term.inner_unfiltered();
        match raw_term.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                stuck
                .clone_unfilter(&raw_term.usages)
                .as_var()
            },
            _ => None,
        }
    }
}

