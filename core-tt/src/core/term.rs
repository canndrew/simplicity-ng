use crate::priv_prelude::*;

/// Represents an arbitrary of term under a context and with a type.
#[derive_where(Clone)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Tm<S: Scheme> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) raw_typed_term: RawTyped<S, Intern<RawTmKind<S>>>,
}

impl<S: Scheme> PartialEq for Tm<S> {
    fn eq(&self, other: &Tm<S>) -> bool {
        let (_, (term_0, term_1)) = merge_ctxs((self, other));
        term_0 == term_1
    }
}

#[derive_where(Clone, Debug)]
pub enum TmKind<S: Scheme> {
    Stuck {
        stuck: Stuck<S>,
    },
    Tag {
        tag: S::Tag,
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
        lhs_name: Name<S>,
        lhs_term: Tm<S>,
        rhs_ty: Ty<S>,
    },
    InjRhs {
        lhs_name: Name<S>,
        rhs_term: Tm<S>,
        lhs_ty: Ty<S>,
    },
    Pair {
        head_name: Name<S>,
        tail_ty: Scope<S, Ty<S>>,
        head_term: Tm<S>,
        tail_term: Tm<S>,
    },
    Func {
        arg_name: Name<S>,
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

    fn contains_subterm(&self, subterm: &RawTm<S>) -> bool {
        self.raw_typed_term.contains_subterm(subterm)
    }
}

impl<S: Scheme> Tm<S> {
    /// Get the context of `self`.
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

    /// Get the type of `self`.
    pub fn ty(&self) -> Ty<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, _) = raw_typed_term.to_parts();
        Ty {
            raw_ctx: raw_ctx.clone(),
            raw_ty,
        }
    }

    /// Get the `TmKind` representation of `self` for pattern-matching on.
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
            RawTmKind::Tag { tag } => {
                TmKind::Tag { tag }
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
                let RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty } = raw_ty.weak.get_clone() else {
                    unreachable!();
                };

                let lhs_name = lhs_name.clone_unfilter(&raw_ty.usages);
                let lhs_term = lhs_term.clone_unfilter(&raw_term.usages);
                let lhs_ty = lhs_ty.clone_unfilter(&raw_ty.usages);
                let lhs_name = Name {
                    raw_ctx: raw_ctx.clone(),
                    raw_name: lhs_name,
                };
                let lhs_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(lhs_ty, lhs_term),
                };
                let rhs_ty = rhs_ty.clone_unfilter(&raw_ty.usages);
                let rhs_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: rhs_ty,
                };
                TmKind::InjLhs { lhs_name, lhs_term, rhs_ty }
            },
            RawTmKind::InjRhs { rhs_term } => {
                let RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty } = raw_ty.weak.get_clone() else {
                    unreachable!();
                };

                let lhs_name = lhs_name.clone_unfilter(&raw_ty.usages);
                let rhs_term = rhs_term.clone_unfilter(&raw_term.usages);
                let rhs_ty = rhs_ty.clone_unfilter(&raw_ty.usages);
                let lhs_name = Name {
                    raw_ctx: raw_ctx.clone(),
                    raw_name: lhs_name,
                };
                let rhs_term = Tm {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_term: RawTyped::from_parts(rhs_ty, rhs_term),
                };
                let lhs_ty = lhs_ty.clone_unfilter(&raw_ty.usages);
                let lhs_ty = Ty {
                    raw_ctx: raw_ctx.clone(),
                    raw_ty: lhs_ty,
                };
                TmKind::InjRhs { lhs_name, rhs_term, lhs_ty }
            },
            RawTmKind::Pair { head_name, head_term, tail_term } => {
                let RawTyKind::Sigma {
                    head_name: ty_head_name, tail_ty,
                } = raw_ty.weak.get_clone() else {
                    unreachable!();
                };
                debug_assert_eq!(
                    head_name.clone_unfilter(&raw_term.usages),
                    ty_head_name.clone_unfilter(&raw_ty.usages),
                );

                let head_name = head_name.clone_unfilter(&raw_term.usages);
                let head_term = head_term.clone_unfilter(&raw_term.usages);
                let tail_term = tail_term.clone_unfilter(&raw_term.usages);
                let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);
                let head_ty = tail_ty.var_ty_unfiltered();

                let head_name = Name {
                    raw_ctx: raw_ctx.clone(),
                    raw_name: head_name,
                };
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
                TmKind::Pair { head_name, tail_ty, head_term, tail_term }
            },
            RawTmKind::Func { arg_name, res_term } => {
                let RawTyKind::Pi {
                    arg_name: ty_arg_name, res_ty,
                } = raw_ty.weak.get_clone() else {
                    unreachable!();
                };
                debug_assert_eq!(
                    arg_name.clone_unfilter(&raw_term.usages),
                    ty_arg_name.unfilter(&raw_ty.usages),
                );

                let arg_name = arg_name.clone_unfilter(&raw_term.usages);
                let res_term = res_term.clone_unfilter(&raw_term.usages);
                let res_ty = res_ty.clone_unfilter(&raw_ty.usages);

                let arg_name = Name {
                    raw_ctx: raw_ctx.clone(),
                    raw_name: arg_name,
                };
                let res_term = RawScope::from_parts_1(res_ty, res_term);
                let res_term = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: res_term,
                };
                TmKind::Func { arg_name, res_term }
            },
        }
    }

    /// Checks whether `self` refers to the variable at `index`.
    pub fn contains_var(&self, index: usize) -> bool {
        self.raw_typed_term.usages[index]
    }

    /// Adds `count` to the natural number represented by self.
    ///
    /// # Panics
    ///
    /// If the type of self is not [TyKind::Nat].
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

    /// Returns the maximum of `self` and `rhs`, assuming both terms have type [TyKind::Nat].
    ///
    /// # Panics
    ///
    /// If the type of either `self` or `rhs` is not [TyKind::Nat].
    pub fn max(&self, rhs: &Tm<S>) -> Tm<S> {
        let (Ctx { raw_ctx }, (lhs_term, rhs_term)) = merge_ctxs((self, rhs));

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

    /// Returns the sum of `self` and `rhs`, assuming both terms have type [TyKind::Nat].
    ///
    /// # Panics
    ///
    /// If the type of either `self` or `rhs` is not [TyKind::Nat].
    pub fn add(&self, rhs: &Tm<S>) -> Tm<S> {
        let (Ctx { raw_ctx }, (lhs_term, rhs_term)) = merge_ctxs((self, rhs));

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

    /// Returns the product of `self` and `rhs`, assuming both terms have type [TyKind::Nat].
    ///
    /// # Panics
    ///
    /// If the type of either `self` or `rhs` is not [TyKind::Nat].
    pub fn mul(&self, rhs: &Tm<S>) -> Tm<S> {
        let (Ctx { raw_ctx }, (lhs_term, rhs_term)) = merge_ctxs((self, rhs));

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

    /// Returns the type representing the proposition that `self` equals `other`.
    ///
    /// Both `self` and `other` must have the same type.
    ///
    /// # Panics
    ///
    /// If the type of `self` and `other` do not match.
    pub fn equals(&self, other: &Tm<S>) -> Ty<S> {
        let eq_term_0 = self;
        let eq_term_1 = other;

        let (ctx, (eq_term_0, eq_term_1)) = merge_ctxs((eq_term_0, eq_term_1));
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

    /// Returns reflexivity proof of self. ie. the unique value of type `self.equals(self)`.
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

    /// Left-injects `self` into the type `self.ty().sum(lhs_name, rhs_ty)`.
    pub fn inj_lhs(&self, lhs_name: &Name<S>, rhs_ty: &Ty<S>) -> Tm<S> {
        let lhs_term = self;
        
        let (ctx, (lhs_name, lhs_term, rhs_ty)) = merge_ctxs((lhs_name, lhs_term, rhs_ty));
        let (lhs_ty, lhs_term) = lhs_term.into_parts();
        let ty = RawTy::sum(lhs_name, lhs_ty, rhs_ty);
        let term = RawTm::inj_lhs(lhs_term);
        let term = RawTyped::from_parts(ty, term);
        Tm { raw_ctx: ctx.raw_ctx, raw_typed_term: term }
    }

    /// Right-injects `self` into the type `lhs_ty.sum(lhs_name, &self.ty())`.
    pub fn inj_rhs(&self, lhs_name: &Name<S>, lhs_ty: &Ty<S>) -> Tm<S> {
        let rhs_term = self;
        
        let (ctx, (lhs_name, lhs_ty, rhs_term)) = merge_ctxs((lhs_name, lhs_ty, rhs_term));
        let (rhs_ty, rhs_term) = rhs_term.into_parts();
        let ty = RawTy::sum(lhs_name, lhs_ty, rhs_ty);
        let term = RawTm::inj_rhs(rhs_term);
        let term = RawTyped::from_parts(ty, term);
        Tm { raw_ctx: ctx.raw_ctx, raw_typed_term: term }
    }

    /// Pairs `self` with `tail_term` to create a term of type
    /// `self.ty().sigma(head_name, tail_ty)`.
    ///
    /// # Panics
    ///
    /// If `tail_term.ty()` does not match `tail_ty(self)`.
    pub fn pair(
        &self,
        head_name: &Name<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_term: &Tm<S>,
    ) -> Tm<S> {
        let head_term = self;
        
        let (ctx, (head_name, head_term, tail_term)) = merge_ctxs((
            head_name, head_term, tail_term,
        ));
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

        let ty = RawTy::sigma(head_name.clone(), tail_ty);
        let term = RawTm::pair(head_name, head_term, tail_term);
        let term = RawTyped::from_parts(ty, term);

        Tm {
            raw_ctx: ctx.raw_ctx,
            raw_typed_term: term,
        }
    }

    /// Converts `self` to a [Name], assuming `self` has type [TyKind::Name].
    ///
    /// # Panics
    ///
    /// If `self.ty()` is not [TyKind::Name].
    pub fn to_name(&self) -> Name<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Name = raw_ty.weak.get_clone() else {
            panic!("term is not a name: {:#?}", raw_ty.weak);
        };
        let raw_name = RawName::from_term(raw_term);
        Name {
            raw_ctx: raw_ctx.clone(),
            raw_name,
        }
    }

    /// Converts `self` to a [Ty], assuming `self` has type [TyKind::Universe].
    ///
    /// # Panics
    ///
    /// If `self.ty()` is not [TyKind::Universe].
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

    /// Converts a function into a scoped [Tm].
    ///
    /// This is the inverse of [Scope::to_func].
    ///
    /// # Panics
    ///
    /// If the type of `self` is not a [TyKind::Pi] type.
    pub fn to_scope(&self) -> Scope<S, Tm<S>> {
        let ty = self.ty();
        let RawTyKind::Pi { arg_name: _, res_ty } = ty.raw_ty.weak.get_clone() else {
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

    /// Assuming `self` has type [TyKind::Nat], loop `self` times to compute a term of type
    /// `motive(self)`.
    ///
    /// When `self` is zero, returns `zero_inhab`.
    /// When `self` is `val.succs(1)` returns `succ_inhab(val, val.for_loop(motive, zero_inhab,
    /// succ_inhab))`.
    ///
    /// The terms passed to `succ_inhab` are a natural number `n` and a term of type `motive(n)`.
    ///
    /// # Panics
    ///
    /// If any of the following conditions fail to hold:
    ///
    /// * `self` must have type [TyKind::Nat].
    /// * `zero_inhab` must have type `motive(self.ctx().zero())`.
    /// * `succ_inhab(n, state)` must have type `motive(n.succs(1))` where `n` has type
    /// [TyKind::Nat] and `state` has type `motive(n)`.
    pub fn for_loop(
        &self,
        motive: impl FnOnce(Tm<S>) -> Ty<S>,
        zero_inhab: &Tm<S>,
        succ_inhab: impl FnOnce(Tm<S>, Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let (Ctx { raw_ctx }, (elim, zero_inhab)) = merge_ctxs((self, zero_inhab));
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

    /// Pattern-match on an equality term. ie. the J-axiom of dependent type theory.
    ///
    /// Assuming `self` has type `x.equals(y)` (for some `x` and `y`) returns a `Tm` of type
    /// `motive(x, y, self)`.
    ///
    /// When `self` is `x.refl()` returns `inhab(x)`.
    ///
    /// # Panics
    ///
    /// If either of the following conditions fail to hold:
    ///
    /// * `self` must have type `x.equals(y)` for some `x` and `y`.
    /// * `inhab(z)` must have type `motive(z, z, z.refl())` for any `z` of the same type as `x`
    /// and `y`.
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
                panic!(
                    "cong(): inhab type doesn't match motive.\n\
                    expected inhab ty == {:?}\n\
                    actual inhab ty == {:?}",
                    expected_inhab_ty,
                    actual_inhab_ty,
                );
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

    /// Pattern-match on a reflexive equality term. ie. the K-axiom of dependent type theory.
    ///
    /// Assuming `self` has type `x.equals(x)` (for some `x`) returns a `Tm` of type
    /// `motive(x, x, self)`.
    ///
    /// When `self` is `x.refl()` returns `inhab(x)`.
    ///
    /// # Panics
    ///
    /// If either of the following conditions fail to hold:
    ///
    /// * `self` must have type `x.equals(x)` for some `x`.
    /// * `inhab(z)` must have type `motive(z, z, z.refl())` for any `z` of the same type as `x`.
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

    /// Ex falso quodlibet. Pattern match on a term of type [TyKind::Never]. 
    ///
    /// Returns a term of type `motive(self)`.
    ///
    /// # Panics
    ///
    /// If `self.ty()` is not [TyKind::Never].
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

    /// Case match on a sum term.
    ///
    /// `self` must have type `lhs_ty.sum(lhs_name, rhs_ty)` for some types `lhs_ty` and `rhs_ty`,
    /// and some name `lhs_name`. Returns a term of type `motive(self)`.
    ///
    /// Returns `lhs_inhab(lhs)` when self is `lhs.inj_lhs(lhs_name, rhs_ty)` for some `lhs`.
    /// Returns `rhs_inhab(rhs)` when self is `rhs.inj_rhs(lhs_name, lhs_ty)` for some `rhs`.
    ///
    /// # Panics
    ///
    /// If any of the following conditions fail to hold:
    ///
    /// * `self` must have type `lhs_ty.sum(lhs_name, rhs_ty)` for some type `lhs_ty` and `rhs_ty`
    /// and some name `lhs_name`.
    /// * `lhs_inhab(lhs)` must have type `motive(lhs.inj_lhs(lhs_name, rhs_ty))` for all `lhs` of
    /// type `lhs_ty`.
    /// * `rhs_inhab(rhs)` must have type `motive(rhs.inj_rhs(lhs_name, lhs_ty))` for all `rhs` of
    /// type `rhs_ty`.
    pub fn case(
        &self,
        motive: impl FnOnce(Tm<S>) -> Ty<S>,
        lhs_inhab: impl FnOnce(Tm<S>) -> Tm<S>,
        rhs_inhab: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty } = raw_ty.weak.get_clone() else {
            panic!(
                "case(): self is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let lhs_name = lhs_name.clone_unfilter(&raw_ty.usages);
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
            if actual_lhs_inhab_ty != expected_lhs_inhab_ty {
                let actual_lhs_inhab_ty: Scope<S, Ty<S>> = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: actual_lhs_inhab_ty,
                };
                let expected_lhs_inhab_ty: Scope<S, Ty<S>> = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: expected_lhs_inhab_ty,
                };
                panic!(
                    "case(): type of lhs branch does not match motive\n\
                    type of lhs branch: {:?}\n\
                    type of substituted motive: {:?}",
                    actual_lhs_inhab_ty,
                    expected_lhs_inhab_ty,
                );
            }
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
            if actual_rhs_inhab_ty != expected_rhs_inhab_ty {
                let actual_rhs_inhab_ty: Scope<S, Ty<S>> = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: actual_rhs_inhab_ty,
                };
                let expected_rhs_inhab_ty: Scope<S, Ty<S>> = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: expected_rhs_inhab_ty,
                };
                panic!(
                    "case(): type of rhs branch does not match motive\n\
                    type of rhs branch: {:?}\n\
                    type of substituted motive: {:?}",
                    actual_rhs_inhab_ty,
                    expected_rhs_inhab_ty,
                );
            }
            rhs_inhab
        };

        let ty = motive.clone().bind(&raw_term);
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::case(lhs_name, raw_term, motive, lhs_inhab, rhs_inhab),
        };
        let term = RawTyped::from_parts(ty, term);

        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Project out the head element of a pair. ie. the first element of a 2-tuple.
    ///
    /// Returns a term of type `head_ty` assuming the type of `self` is `head_ty.sigma(head_name,
    /// tail_ty)` for some type `head_ty`, some scoped type `tail_ty` and some name `head_name`.
    ///
    /// # Panics
    ///
    /// If the type of `self` is not a [TyKind::Sigma] type.
    pub fn proj_head(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Sigma { head_name, tail_ty } = raw_ty.weak.get_clone() else {
            panic!(
                "proj_head(): self is not a sigma.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let head_name = head_name.clone_unfilter(&raw_ty.usages);
        let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);
        let head_ty = tail_ty.var_ty_unfiltered();

        let ty = head_ty;
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::proj_head(head_name, tail_ty, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Project out the tail element of a pair. ie. the second element of a 2-tuple.
    ///
    /// Returns a term of type `tail_ty(self.proj_head())` assuming the type of `self` is
    /// `head_ty.sigma(head_name, tail_ty)` for some type `head_ty`, some scoped type `tail_ty` and
    /// some name `head_name`.
    ///
    /// # Panics
    ///
    /// If the type of `self` is not a [TyKind::Sigma] type.
    pub fn proj_tail(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Sigma { head_name, tail_ty } = raw_ty.weak.get_clone() else {
            panic!(
                "proj_tail(): self is not a sigma.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let head_name = head_name.clone_unfilter(&raw_ty.usages);
        let tail_ty = tail_ty.clone_unfilter(&raw_ty.usages);

        let ty = {
            let head_term = RawTm::proj_head(
                head_name.clone(), tail_ty.clone(), raw_term.clone(),
            );
            tail_ty.clone().bind(&head_term)
        };
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::proj_tail(head_name, tail_ty, raw_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Apply a function term.
    ///
    /// The type of `self` must be `arg_ty.pi(arg_name, res_ty)` for some type `arg_ty`, some
    /// scoped type `res_ty` and some name `arg_name`.
    ///
    /// Returns a term of type `res_ty(arg_term)`.
    ///
    /// # Panics
    ///
    /// If either of the following conditions fail to hold:
    ///
    /// * The type of `self` must be a [TyKind::Pi] type.
    /// * The type of `arg_term` must match the argument type of `self`.
    pub fn app(
        &self,
        arg_term: &Tm<S>,
    ) -> Tm<S> {
        let (Ctx { raw_ctx }, (elim, arg_term)) = merge_ctxs((self, arg_term));
        let (raw_ty, raw_term) = elim.into_parts();
        let RawTyKind::Pi { arg_name, res_ty } = raw_ty.weak.get_clone() else {
            panic!("app(): {:#?} is not a function", self);
        };
        let arg_name = arg_name.clone_unfilter(&raw_ty.usages);
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
            None => RawTm::app(arg_name, res_ty, raw_term, arg_term),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx,
            raw_typed_term: term,
        }
    }

    /// Convert an equality of unequal tags into a term of type [TyKind::Never].
    ///
    /// The type of self must be `self.ctx().tag(x).equals(&self.ctx().tag(y))` where `x` and `y`
    /// are rust values of type [Scheme::Tag] and `x != y`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.
    pub fn tags_apart(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();

        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!(
                "tags_apart(): self is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Name = eq_ty.weak.get_clone() else {
            panic!(
                "tags_apart(): self is not an equality between names.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Tag { tag: tag_0 } = eq_term_0.weak.get_clone() else {
            panic!(
                "tags_apart(): name on left side of equality is not a constant\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Tag { tag: tag_1 } = eq_term_1.weak.get_clone() else {
            panic!(
                "tags_apart(): name on left side of equality is not a constant\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let ty = RawTy::never(ctx_len);
        let term = RawTyped::from_parts(
            ty,
            RawTm::tags_apart(tag_0, tag_1, raw_term),
        );
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Type constructor injectivity for the endpoint type of equality types.
    ///
    /// Given the following:
    /// * Two types: `eq_ty_0` and `eq_ty_1`.
    /// * Two terms of type `eq_ty_0`: `eq_term_0_0` and `eq_term_1_0`.
    /// * Two terms of type `eq_ty_1`: `eq_term_0_1` and `eq_term_1_1`.
    ///
    /// Then if `self` has type:
    ///
    /// `eq_term_0_0.equals(eq_term_1_0).to_term().equals(&eq_term_0_1.equals(eq_term_1_1).to_term())`
    ///
    /// ie. `self` is a proof that the type of proofs
    ///
    /// `eq_term_0_0.equals(eq_term_1_0)`
    ///
    /// Is equal to the type of proofs
    ///
    /// `eq_term_0_1.equals(eq_term_1_1)`
    ///
    /// Then this method returns a term of type `eq_ty_0.to_term().equals(&eq_ty_1.to_term())`
    ///
    /// ie. A proof that `eq_ty_0 == eq_ty_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

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
            panic!(
                "equal_eq_eq_ty_injective(): type on left side of equality\
                is not known to be an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
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
            panic!(
                "equal_eq_eq_ty_injective(): type on right side of equality\
                is not known to be an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
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
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Type constructor injectivity for the left (first) endpoint of equality types.
    ///
    /// Given the following:
    /// * A type: `eq_ty`
    /// * Four terms of type `eq_ty`: `eq_term_0_0`, `eq_term_1_0`, `eq_term_0_1` and
    /// `eq_term_1_1`.
    ///
    /// Then if `self` has type:
    ///
    /// `eq_term_0_0.equals(eq_term_1_0).to_term().equals(&eq_term_0_1.equals(eq_term_1_1).to_term())`
    ///
    /// ie. `self` is a proof that the type of proofs
    ///
    /// `eq_term_0_0.equals(eq_term_1_0)`
    ///
    /// Is equal to the type of proofs
    ///
    /// `eq_term_0_1.equals(eq_term_1_1)`
    ///
    /// Then this method returns a term of type `eq_term_0_0.equals(eq_term_0_1)`.
    ///
    /// ie. A proof that the left-endpoints of the two equality proof types are equal.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

    pub fn equal_eq_eq_term_0_injective(
        &self,
    ) -> Tm<S> {
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
        };
        let eq_ty_1 = {
            eq_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
        };
        let Some(eq_ty) = as_equal(eq_ty_0, eq_ty_1) else {
            panic!(
                "equal_eq_eq_term_0_injective(): types of equal terms are not equal.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let eq_ty = eq_ty.unfilter(&raw_ty.usages);

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
            eq_ty.clone(),
            eq_term_0_0.clone(),
            eq_term_0_1.clone(),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::equal_eq_eq_term_0_injective(
                eq_ty,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }


    /// Type constructor injectivity for the right (second) endpoint of equality types.
    ///
    /// Given the following:
    /// * A type: `eq_ty`
    /// * Four terms of type `eq_ty`: `eq_term_0_0`, `eq_term_1_0`, `eq_term_0_1` and
    /// `eq_term_1_1`.
    ///
    /// Then if `self` has type:
    ///
    /// `eq_term_0_0.equals(eq_term_1_0).to_term().equals(&eq_term_0_1.equals(eq_term_1_1).to_term())`
    ///
    /// ie. `self` is a proof that the type of proofs
    ///
    /// `eq_term_0_0.equals(eq_term_1_0)`
    ///
    /// Is equal to the type of proofs
    ///
    /// `eq_term_0_1.equals(eq_term_1_1)`
    ///
    /// Then this method returns a term of type `eq_term_1_0.equals(eq_term_1_1)`.
    ///
    /// ie. A proof that the right-endpoints of the two equality proof types are equal.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

    pub fn equal_eq_eq_term_1_injective(
        &self,
    ) -> Tm<S> {
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
        };
        let eq_ty_1 = {
            eq_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
        };
        let Some(eq_ty) = as_equal(eq_ty_0, eq_ty_1) else {
            panic!(
                "equal_eq_eq_term_1_injective(): types of equal terms are not equal.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let eq_ty = eq_ty.unfilter(&raw_ty.usages);

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
            eq_ty.clone(),
            eq_term_1_0.clone(),
            eq_term_1_1.clone(),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::equal_eq_eq_term_1_injective(
                eq_ty,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Type constructor injectivity for the `lhs_name` of sum types.
    ///
    /// Given the following:
    /// * 4 types: `lhs_ty_0`, `rhs_ty_0`, `lhs_ty_1`, `rhs_ty_1`.
    /// * 2 names: `lhs_name_0`, `lhs_name_1`.
    ///
    /// Then if `self` has the type:
    ///
    /// `lhs_ty_0.sum(lhs_name_0, rhs_ty_0).to_term().equals(&lhs_ty_1.sum(lhs_name_1, rhs_ty_1))`
    ///
    /// ie. `self` is a proof that the type
    ///
    /// `TyKind::Sum { lhs_name: lhs_name_0, lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 }`
    ///
    /// equals the type
    ///
    /// `TyKind::Sum { lhs_name: lhs_name_1, lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 }`
    ///
    /// then this method returns a value of type
    ///
    /// `lhs_name_0.to_term().equals(&lhs_name_1.to_term())`
    ///
    /// ie. a proof that `lhs_name_0 == lhs_name_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

    pub fn sum_eq_name_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!(
                "sum_eq_name_injective(): self is not an equality.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTyKind::Universe = eq_ty.weak.get_clone() else {
            panic!(
                "sum_eq_name_injective(): self is not an equality between types.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sum { lhs_name: lhs_name_0, lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 } = ty_0.weak.get_clone() else {
            panic!(
                "sum_eq_name_injective(): type on left side of equality\
                is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sum { lhs_name: lhs_name_1, lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 } = ty_1.weak.get_clone() else {
            panic!(
                "sum_eq_name_injective(): type on right side of equality\
                is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let lhs_name_0 = {
            lhs_name_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let lhs_name_1 = {
            lhs_name_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
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
            RawTy::name(ctx_len),
            RawTm::from_name(lhs_name_0.clone()),
            RawTm::from_name(lhs_name_1.clone()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::sum_eq_name_injective(
                lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Type constructor injectivity for the `lhs_ty` of sum types.
    ///
    /// Given the following:
    /// * 4 types: `lhs_ty_0`, `rhs_ty_0`, `lhs_ty_1`, `rhs_ty_1`.
    /// * 2 names: `lhs_name_0`, `lhs_name_1`.
    ///
    /// Then if `self` has the type:
    ///
    /// `lhs_ty_0.sum(lhs_name_0, rhs_ty_0).to_term().equals(&lhs_ty_1.sum(lhs_name_1, rhs_ty_1))`
    ///
    /// ie. `self` is a proof that the type
    ///
    /// `TyKind::Sum { lhs_name: lhs_name_0, lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 }`
    ///
    /// equals the type
    ///
    /// `TyKind::Sum { lhs_name: lhs_name_1, lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 }`
    ///
    /// then this method returns a value of type
    ///
    /// `lhs_ty_0.to_term().equals(&lhs_ty_1.to_term())`
    ///
    /// ie. a proof that `lhs_ty_0 == lhs_ty_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

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
        let RawTyKind::Sum { lhs_name: lhs_name_0, lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 } = ty_0.weak.get_clone() else {
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
        let RawTyKind::Sum { lhs_name: lhs_name_1, lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 } = ty_1.weak.get_clone() else {
            panic!(
                "sum_eq_lhs_injective(): type on right side of equality\
                is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let lhs_name_0 = {
            lhs_name_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let lhs_name_1 = {
            lhs_name_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
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
            None => RawTm::sum_eq_lhs_injective(
                lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Type constructor injectivity for the `rhs_ty` of sum types.
    ///
    /// Given the following:
    /// * 4 types: `lhs_ty_0`, `rhs_ty_0`, `lhs_ty_1`, `rhs_ty_1`.
    /// * 2 names: `lhs_name_0`, `lhs_name_1`.
    ///
    /// Then if `self` has the type:
    ///
    /// `lhs_ty_0.sum(lhs_name_0, rhs_ty_0).to_term().equals(&lhs_ty_1.sum(lhs_name_1, rhs_ty_1))`
    ///
    /// ie. `self` is a proof that the type
    ///
    /// `TyKind::Sum { lhs_name: lhs_name_0, lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 }`
    ///
    /// equals the type
    ///
    /// `TyKind::Sum { lhs_name: lhs_name_1, lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 }`
    ///
    /// then this method returns a value of type
    ///
    /// `rhs_ty_0.to_term().equals(&rhs_ty_1.to_term())`
    ///
    /// ie. a proof that `rhs_ty_0 == rhs_ty_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

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
        let RawTyKind::Sum {
            lhs_name: lhs_name_0, lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0,
        } = ty_0.weak.get_clone() else {
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
        let RawTyKind::Sum {
            lhs_name: lhs_name_1, lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1,
        } = ty_1.weak.get_clone() else {
            panic!(
                "sum_eq_rhs_injective(): type on right side of equality\
                is not a sum.\n\
                self.ty(): {:?}",
                self.ty(),
            );
        };

        let lhs_name_0 = {
            lhs_name_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let lhs_name_1 = {
            lhs_name_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
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
            None => RawTm::sum_eq_rhs_injective(
                lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Type constructor injectivity for the `head_name` of sigma types.
    ///
    /// Given the following:
    /// * Two names: `head_name_0` and `head_name_1`.
    /// * Two types: `head_ty_0` and `head_ty_1`.
    /// * A type scoped under a value of type `head_ty_0`: `tail_ty_0`.
    /// * A type scoped under a value of type `head_ty_1`: `tail_ty_1`.
    ///
    /// Then if self has type:
    ///
    /// `head_ty_0.sigma(head_name_0, tail_ty_0).to_term().equals(&head_ty_1.sigma(head_name_1,
    /// tail_ty_1).to_term())`
    ///
    /// ie. `self` is a proof that the type:
    ///
    /// `TyKind::Sigma { head_name: head_name_0, tail_ty: tail_ty_0 }`
    ///
    /// Equals the type:
    ///
    /// `TyKind::Sigma { head_name: head_name_1, tail_ty: tail_ty_1 }`
    ///
    /// Then this method returns a term of type:
    ///
    /// `head_name_0.to_term().equals(&head_name_1.to_term())`.
    ///
    /// ie. A proof that `head_name_0 == head_name_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

    pub fn sigma_eq_name_injective(&self) -> Tm<S> {
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
        let RawTyKind::Sigma {
            head_name: head_name_0, tail_ty: tail_ty_0,
        } = ty_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sigma {
            head_name: head_name_1, tail_ty: tail_ty_1,
        } = ty_1.weak.get_clone() else {
            unreachable!();
        };

        let head_name_0 = {
            head_name_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let head_name_1 = {
            head_name_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let tail_ty_0 = {
            tail_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let tail_ty_1 = {
            tail_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };

        let ty = RawTy::equal(
            RawTy::name(ctx_len),
            RawTm::from_name(head_name_0.clone()),
            RawTm::from_name(head_name_1.clone()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::sigma_eq_name_injective(
                head_name_0, head_name_1, tail_ty_0, tail_ty_1, raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Type constructor injectivity for the `head_ty` of sigma types.
    ///
    /// Given the following:
    /// * Two names: `head_name_0` and `head_name_1`.
    /// * Two types: `head_ty_0` and `head_ty_1`.
    /// * A type scoped under a value of type `head_ty_0`: `tail_ty_0`.
    /// * A type scoped under a value of type `head_ty_1`: `tail_ty_1`.
    ///
    /// Then if self has type:
    ///
    /// `head_ty_0.sigma(head_name_0, tail_ty_0).to_term().equals(&head_ty_1.sigma(head_name_1,
    /// tail_ty_1).to_term())`
    ///
    /// ie. `self` is a proof that the type:
    ///
    /// `TyKind::Sigma { head_name: head_name_0, tail_ty: tail_ty_0 }`
    ///
    /// Equals the type:
    ///
    /// `TyKind::Sigma { head_name: head_name_1, tail_ty: tail_ty_1 }`
    ///
    /// Then this method returns a term of type:
    ///
    /// `head_ty_0.to_term().equals(&head_ty_1.to_term())`.
    ///
    /// ie. A proof that `head_ty_0 == head_ty_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

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
        let RawTyKind::Sigma {
            head_name: head_name_0, tail_ty: tail_ty_0,
        } = ty_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sigma {
            head_name: head_name_1, tail_ty: tail_ty_1,
        } = ty_1.weak.get_clone() else {
            unreachable!();
        };

        let head_name_0 = {
            head_name_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let head_name_1 = {
            head_name_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let tail_ty_0 = {
            tail_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let tail_ty_1 = {
            tail_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };

        let ty = RawTy::equal(
            RawTy::universe(ctx_len),
            RawTm::from_ty(tail_ty_0.var_ty_unfiltered()),
            RawTm::from_ty(tail_ty_1.var_ty_unfiltered()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::sigma_eq_head_injective(
                head_name_0, head_name_1, tail_ty_0, tail_ty_1, raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Type constructor injectivity for the `tail_ty` of sigma types.
    ///
    /// Given the following:
    /// * A name: `head_name`.
    /// * A type: `head_ty`.
    /// * Two types scoped under `head_ty`: `tail_ty_0` and `tail_ty_1`.
    ///
    /// Then if self has type:
    ///
    /// `head_ty.sigma(head_name, tail_ty_0).to_term().equals(&head_ty.sigma(head_name,
    /// tail_ty_1).to_term())`
    ///
    /// ie. `self` is a proof that the type:
    ///
    /// `TyKind::Sigma { head_name, tail_ty: tail_ty_0 }`
    ///
    /// Equals the type:
    ///
    /// `TyKind::Sigma { head_name, tail_ty: tail_ty_1 }`
    ///
    /// Then this method returns a term of type:
    ///
    /// `head_ty.func(head_name, tail_ty_0).equals(&head_ty.func(head_name, tail_ty_1))`.
    ///
    /// ie. A proof that `tail_ty_0 == tail_ty_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

    pub fn sigma_eq_tail_injective(
        &self,
    ) -> Tm<S> {
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
        let RawTyKind::Sigma {
            head_name: head_name_0, tail_ty: tail_ty_0,
        } = ty_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Sigma {
            head_name: head_name_1, tail_ty: tail_ty_1,
        } = ty_1.weak.get_clone() else {
            unreachable!();
        };

        let head_name_0 = {
            head_name_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
        };
        let head_name_1 = {
            head_name_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
        };
        let Some(head_name) = as_equal(head_name_0, head_name_1) else {
            unreachable!();
        };
        let head_name = head_name.unfilter(&raw_ty.usages);

        let tail_ty_0 = {
            tail_ty_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let tail_ty_1 = {
            tail_ty_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
        };
        let (inner_tail_ty_0, head_ty_0) = tail_ty_0.clone().into_inner();
        let (inner_tail_ty_1, head_ty_1) = tail_ty_1.clone().into_inner();
        let Some(head_ty) = as_equal(head_ty_0, head_ty_1) else {
            panic!();
        };

        let ty = RawTy::equal(
            RawTy::pi(
                head_name.clone(),
                RawScope::new(head_ty.clone(), RawTy::universe(raw_ctx.len() + 1)),
            ),
            RawTm::func(
                head_name.clone(),
                RawScope::new(head_ty.clone(), RawTm::from_ty(inner_tail_ty_0)),
            ),
            RawTm::func(
                head_name.clone(),
                RawScope::new(head_ty, RawTm::from_ty(inner_tail_ty_1)),
            ),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::sigma_eq_tail_injective(
                head_name,
                tail_ty_0,
                tail_ty_1,
                raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }


    /// Type constructor injectivity for the `arg_name` of pi types.
    ///
    /// Given the following:
    /// * Two names: `arg_name_0` and `arg_name_1`.
    /// * Two types: `arg_ty_0` and `arg_ty_1`.
    /// * A type scoped under a value of type `arg_ty_0`: `res_ty_0`.
    /// * A type scoped under a value of type `arg_ty_1`: `res_ty_1`.
    ///
    /// Then if self has type:
    ///
    /// `arg_ty_0.pi(arg_name_0, res_ty_0).to_term().equals(&arg_ty_1.pi(arg_name_1,
    /// res_ty_1).to_term())`
    ///
    /// ie. `self` is a proof that the type:
    ///
    /// `TyKind::Pi { arg_name: arg_name_0, res_ty: res_ty_0 }`
    ///
    /// Equals the type:
    ///
    /// `TyKind::Pi { arg_name: arg_name_1, res_ty: res_ty_1 }`
    ///
    /// Then this method returns a term of type:
    ///
    /// `arg_name_0.to_term().equals(&arg_name_1.to_term())`.
    ///
    /// ie. A proof that `arg_name_0 == arg_name_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

    pub fn pi_eq_name_injective(&self) -> Tm<S> {
        let Tm { raw_ctx, raw_typed_term } = self;
        let ctx_len = raw_typed_term.usages.len();
        let (raw_ty, raw_term) = raw_typed_term.to_parts();
        let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty.weak.get_clone() else {
            panic!("\
                pi_eq_name_injective(): self is not an equality.\n\
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
                pi_eq_name_injective(): self is not an equality between types.\n\
                equality_type: {:#?}",
                eq_ty,
            );
        };
        let RawTmKind::Type { ty: ty_0 } = eq_term_0.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Pi {
            arg_name: arg_name_0, res_ty: res_ty_0,
        } = ty_0.weak.get_clone() else {
            let ty_0 = ty_0.clone_unfilter(&eq_term_0.usages);
            let ty_0 = ty_0.unfilter(&raw_ty.usages);
            let ty_0 = Ty {
                raw_ctx: raw_ctx.clone(),
                raw_ty: ty_0,
            };
            panic!(
                "pi_eq_name_injective(): type on left side of equality is not a pi type.\n\
                left type: {:#?}",
                ty_0,
            );
        };
        let RawTmKind::Type { ty: ty_1 } = eq_term_1.weak.get_clone() else {
            unreachable!();
        };
        let RawTyKind::Pi {
            arg_name: arg_name_1, res_ty: res_ty_1,
        } = ty_1.weak.get_clone() else {
            let ty_1 = ty_1.clone_unfilter(&eq_term_1.usages);
            let ty_1 = ty_1.unfilter(&raw_ty.usages);
            let ty_1 = Ty {
                raw_ctx: raw_ctx.clone(),
                raw_ty: ty_1,
            };
            panic!(
                "pi_eq_name_injective(): type on right side of equality is not a pi type.\n\
                right type: {:#?}",
                ty_1,
            );
        };

        let arg_name_0 = {
            arg_name_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let arg_name_1 = {
            arg_name_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
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
            RawTy::name(ctx_len),
            RawTm::from_name(arg_name_0.clone()),
            RawTm::from_name(arg_name_1.clone()),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::pi_eq_name_injective(
                arg_name_0, arg_name_1, res_ty_0, res_ty_1, raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Type constructor injectivity for the `arg_ty` of pi types.
    ///
    /// Given the following:
    /// * Two names: `arg_name_0` and `arg_name_1`.
    /// * Two types: `arg_ty_0` and `arg_ty_1`.
    /// * A type scoped under a value of type `arg_ty_0`: `res_ty_0`.
    /// * A type scoped under a value of type `arg_ty_1`: `res_ty_1`.
    ///
    /// Then if self has type:
    ///
    /// `arg_ty_0.pi(arg_name_0, res_ty_0).to_term().equals(&arg_ty_1.pi(arg_name_1,
    /// res_ty_1).to_term())`
    ///
    /// ie. `self` is a proof that the type:
    ///
    /// `TyKind::Pi { arg_name: arg_name_0, res_ty: res_ty_0 }`
    ///
    /// Equals the type:
    ///
    /// `TyKind::Pi { arg_name: arg_name_1, res_ty: res_ty_1 }`
    ///
    /// Then this method returns a term of type:
    ///
    /// `arg_ty_0.to_term().equals(&arg_ty_1.to_term())`.
    ///
    /// ie. A proof that `arg_ty_0 == arg_ty_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

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
        let RawTyKind::Pi {
            arg_name: arg_name_0, res_ty: res_ty_0,
        } = ty_0.weak.get_clone() else {
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
        let RawTyKind::Pi {
            arg_name: arg_name_1, res_ty: res_ty_1,
        } = ty_1.weak.get_clone() else {
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

        let arg_name_0 = {
            arg_name_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
            .unfilter(&raw_ty.usages)
        };
        let arg_name_1 = {
            arg_name_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
            .unfilter(&raw_ty.usages)
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
            None => RawTm::pi_eq_arg_injective(
                arg_name_0, arg_name_1, res_ty_0, res_ty_1, raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }


    /// Type constructor injectivity for the `res_ty` of pi types.
    ///
    /// Given the following:
    /// * A name: `arg_name`.
    /// * A type: `arg_ty`.
    /// * Two types scoped under `arg_ty`: `res_ty_0` and `res_ty_1`.
    ///
    /// Then if self has type:
    ///
    /// `arg_ty.pi(arg_name, res_ty_0).to_term().equals(&arg_ty.pi(arg_name,
    /// res_ty_1).to_term())`
    ///
    /// ie. `self` is a proof that the type:
    ///
    /// `TyKind::Pi { arg_name, res_ty: res_ty_0 }`
    ///
    /// Equals the type:
    ///
    /// `TyKind::Pi { arg_name, res_ty: res_ty_1 }`
    ///
    /// Then this method returns a term of type:
    ///
    /// `arg_ty.func(arg_name, res_ty_0).equals(&arg_ty.func(arg_name, res_ty_1))`.
    ///
    /// ie. A proof that `res_ty_0 == res_ty_1`.
    ///
    /// # Panics
    ///
    /// If the type of `self` does not match the above description.

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
        let RawTyKind::Pi {
            arg_name: arg_name_0, res_ty: res_ty_0,
        } = ty_0.weak.get_clone() else {
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
        let RawTyKind::Pi {
            arg_name: arg_name_1, res_ty: res_ty_1,
        } = ty_1.weak.get_clone() else {
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

        let arg_name_0 = {
            arg_name_0
            .unfilter(&ty_0.usages)
            .unfilter(&eq_term_0.usages)
        };
        let arg_name_1 = {
            arg_name_1
            .unfilter(&ty_1.usages)
            .unfilter(&eq_term_1.usages)
        };
        let Some(arg_name) = as_equal(arg_name_0, arg_name_1) else {
            panic!();
        };
        let arg_name = arg_name.unfilter(&raw_ty.usages);

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
        let (inner_res_ty_0, arg_ty_0) = res_ty_0.clone().into_inner();
        let (inner_res_ty_1, arg_ty_1) = res_ty_1.clone().into_inner();
        let Some(arg_ty) = as_equal(arg_ty_0, arg_ty_1) else {
            panic!();
        };

        let ty = RawTy::equal(
            RawTy::pi(
                arg_name.clone(),
                RawScope::new(arg_ty.clone(), RawTy::universe(raw_ctx.len() + 1)),
            ),
            RawTm::func(
                arg_name.clone(),
                RawScope::new(arg_ty.clone(), RawTm::from_ty(inner_res_ty_0)),
            ),
            RawTm::func(
                arg_name.clone(),
                RawScope::new(arg_ty, RawTm::from_ty(inner_res_ty_1)),
            ),
        );
        let term = match ty.unique_eta_term_opt(&mut Vec::new()) {
            Some(eta_term) => eta_term,
            None => RawTm::pi_eq_res_injective(
                arg_name,
                res_ty_0,
                res_ty_1,
                raw_term,
            ),
        };
        let term = RawTyped::from_parts(ty, term);

        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: term,
        }
    }

    /// Returns `Some(index)` if `self` is a term representing the variable at `index`. Otherwise
    /// returns `None`.
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

