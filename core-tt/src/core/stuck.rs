use crate::priv_prelude::*;

#[derive_where(Clone, PartialEq)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Stuck<S: Scheme> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) raw_typed_stuck: RawTyped<S, Intern<RawStuckKind<S>>>,
}

#[derive_where(Clone)]
pub enum StuckKind<S: Scheme> {
    Var {
        index: usize,
    },
    ForLoop {
        elim: Stuck<S>,
        motive: Scope<S, Ty<S>>,
        zero_inhab: Tm<S>,
        succ_inhab: Scope<S, Scope<S, Tm<S>>>,
    },
    Max {
        elims: Vec<Tm<S>>,
    },
    Add {
        elims: Vec<Tm<S>>,
    },
    Mul {
        elims: Vec<Tm<S>>,
    },
    PowConstant {
        elim: Stuck<S>,
        exponent: NonZeroBigUint,
    },
    Cong {
        elim: Stuck<S>,
        motive: Scope<S, Scope<S, Scope<S, Ty<S>>>>,
        inhab: Scope<S, Tm<S>>,
    },
    UniqueIdentity {
        elim: Stuck<S>,
        motive: Scope<S, Scope<S, Ty<S>>>,
        inhab: Scope<S, Tm<S>>,
    },
    Explode {
        elim: Stuck<S>,
        motive: Scope<S, Ty<S>>,
    },
    Case {
        elim: Stuck<S>,
        motive: Scope<S, Ty<S>>,
        lhs_inhab: Scope<S, Tm<S>>,
        rhs_inhab: Scope<S, Tm<S>>,
    },
    ProjHead {
        elim: Stuck<S>,
    },
    ProjTail {
        elim: Stuck<S>,
    },

    App {
        elim: Stuck<S>,
        arg_term: Tm<S>,
    },

    EqualEqEqTyInjective {
        elim: Stuck<S>,
    },
    EqualEqEqTerm0Injective {
        elim: Stuck<S>,
    },
    EqualEqEqTerm1Injective {
        elim: Stuck<S>,
    },
    SumEqLhsInjective {
        elim: Stuck<S>,
    },
    SumEqRhsInjective {
        elim: Stuck<S>,
    },
    SigmaEqHeadInjective {
        elim: Stuck<S>,
    },
    SigmaEqTailInjective {
        elim: Stuck<S>,
    },
    PiEqArgInjective {
        elim: Stuck<S>,
    },
    PiEqResInjective {
        elim: Stuck<S>,
    },
}

impl<S: Scheme> Stuck<S> {
    pub fn ctx(&self) -> Ctx<S> {
        Ctx {
            raw_ctx: self.raw_ctx.clone(),
        }
    }

    pub fn usages(&self) -> &Usages {
        &self.raw_typed_stuck.usages
    }

    pub fn transitive_usages(&self) -> Usages {
        let mut usages = self.raw_typed_stuck.weak.inner.usages.clone_unfilter(&self.raw_typed_stuck.usages);
        self.raw_ctx.fill_transitive_usages(&mut usages);
        usages
    }

    pub fn ty(&self) -> Ty<S> {
        let Stuck { raw_ctx, raw_typed_stuck } = self;
        let (raw_ty, _) = raw_typed_stuck.to_parts();
        Ty {
            raw_ctx: raw_ctx.clone(),
            raw_ty,
        }
    }

    pub fn to_term(&self) -> Tm<S> {
        let Stuck { raw_ctx, raw_typed_stuck } = self;
        let (raw_ty, raw_stuck) = raw_typed_stuck.to_parts();
        let raw_term = RawTm::stuck(raw_stuck);
        let raw_typed_term = RawTyped::from_parts(raw_ty, raw_term);
        Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term,
        }
    }

    pub fn to_ty(&self) -> Ty<S> {
        let Stuck { raw_ctx, raw_typed_stuck } = self;
        let (raw_ty, raw_stuck) = raw_typed_stuck.to_parts();
        let RawTyKind::Universe = raw_ty.weak.get_clone() else {
            unreachable!();
        };
        let raw_ty = RawTy::stuck(raw_stuck);
        Ty {
            raw_ctx: raw_ctx.clone(),
            raw_ty,
        }
    }

    pub fn kind(&self) -> StuckKind<S> {
        let ctx_len = self.raw_typed_stuck.usages.len();
        let Stuck { raw_ctx, raw_typed_stuck } = self;
        let (_raw_ty, raw_stuck) = raw_typed_stuck.to_parts();
        match raw_stuck.weak.get_clone() {
            RawStuckKind::Var => {
                let index = raw_stuck.usages.index_of_single_one().unwrap();
                StuckKind::Var { index }
            },

            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);
                let zero_inhab = zero_inhab.clone_unfilter(&raw_stuck.usages);
                let succ_inhab = succ_inhab.clone_unfilter(&raw_stuck.usages);

                let nat_ty = RawTy::nat(ctx_len);
                let elim = RawTyped::from_parts(nat_ty.clone(), elim);
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
                    .bind(
                        &RawTm::succs(NonZeroBigUint::one(), RawTm::var(ctx_len + 2, ctx_len, &nat_ty)),
                    )
                };
                let (succ_inhab, raw_nat_ty) = succ_inhab.into_inner();
                let (succ_inhab, motive_inner) = succ_inhab.into_inner();
                let succ_inhab = RawTyped::from_parts(succ_inhab_ty, succ_inhab);
                let succ_inhab = RawScope::new(motive_inner.clone(), succ_inhab);
                let succ_inhab = RawScope::new(raw_nat_ty, succ_inhab);
                let succ_inhab = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: succ_inhab,
                };

                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: motive,
                };

                StuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab }
            },

            RawStuckKind::Nat { nat } => {
                let nat = nat.clone_unfilter(&raw_stuck.usages);
                if nat.max_all.terms.len() > 1 {
                    let elims = {
                        nat
                        .max_all
                        .terms
                        .into_iter()
                        .map(|add_all| {
                            let mut usages = Usages::zeros(nat.usages.count_ones());
                            for term in add_all.iter_terms() {
                                usages.or_assign(&term.usages);
                            }
                            usages.unfilter(&nat.usages);
                            let max_all = MaxAll { terms: ordset! { add_all } };
                            let nat = RawNat { usages, max_all };
                            let raw_term = nat.into_raw_term();
                            let raw_typed_term = RawTyped::from_parts(RawTy::nat(ctx_len), raw_term);
                            Tm {
                                raw_ctx: raw_ctx.clone(),
                                raw_typed_term,
                            }
                        })
                        .collect()
                    };
                    StuckKind::Max { elims }
                } else {
                    let add_all = nat.max_all.terms.into_iter().next().unwrap();
                    if add_all.terms.len() > 1 {
                        let elims = {
                            add_all
                            .terms
                            .into_iter()
                            .map(|(mul_all, multiplicity)| {
                                let mut usages = Usages::zeros(nat.usages.count_ones());
                                for term in mul_all.iter_terms() {
                                    usages.or_assign(&term.usages);
                                }
                                usages.unfilter(&nat.usages);
                                let add_all = AddAll { terms: ordmap! { mul_all => multiplicity } };
                                let max_all = MaxAll { terms: ordset! { add_all } };
                                let nat = RawNat { usages, max_all };
                                let raw_term = nat.into_raw_term();
                                let raw_typed_term = RawTyped::from_parts(RawTy::nat(ctx_len), raw_term);
                                Tm {
                                    raw_ctx: raw_ctx.clone(),
                                    raw_typed_term,
                                }
                            })
                            .collect()
                        };
                        StuckKind::Add { elims }
                    } else {
                        let (mul_all, multiplicity) = add_all.terms.into_iter().next().unwrap();
                        if !multiplicity.is_one() || mul_all.terms.len() > 1 {
                            let elims = {
                                (!multiplicity.is_one())
                                .then(|| {
                                    let ctx = Ctx { raw_ctx: raw_ctx.clone() };
                                    ctx.nat_constant(multiplicity)
                                })
                                .into_iter()
                                .chain(
                                    mul_all
                                    .terms
                                    .into_iter()
                                    .map(|(stuck, exponent)| {
                                        let usages = stuck.usages.clone_unfilter(&nat.usages);
                                        let mul_all = MulAll { terms: ordmap! { stuck => exponent } };
                                        let add_all = AddAll { terms: ordmap! { mul_all => NonZeroBigUint::one() } };
                                        let max_all = MaxAll { terms: ordset! { add_all } };
                                        let nat = RawNat { usages, max_all };
                                        let raw_term = nat.into_raw_term();
                                        let raw_typed_term = RawTyped::from_parts(RawTy::nat(ctx_len), raw_term);
                                        Tm {
                                            raw_ctx: raw_ctx.clone(),
                                            raw_typed_term,
                                        }
                                    })
                                )
                                .collect()
                            };
                            StuckKind::Mul { elims }
                        } else {
                            let (stuck, exponent) = mul_all.terms.into_iter().next().unwrap();
                            debug_assert!(!exponent.is_one());
                            let stuck = stuck.unfilter(&nat.usages);
                            let raw_typed_stuck = RawTyped::from_parts(RawTy::nat(ctx_len), stuck);
                            let elim = Stuck {
                                raw_ctx: raw_ctx.clone(),
                                raw_typed_stuck,
                            };
                            StuckKind::PowConstant {
                                elim,
                                exponent,
                            }
                        }
                    }
                }
            },

            RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
                let eq_term_0 = eq_term_0.clone_unfilter(&raw_stuck.usages);
                let eq_term_1 = eq_term_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);
                let inhab = inhab.clone_unfilter(&raw_stuck.usages);
                let eq_ty = inhab.var_ty_unfiltered();

                let elim_ty = RawTy::equal(eq_ty.clone(), eq_term_0, eq_term_1);
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let inhab_ty = {
                    motive
                    .clone_weaken(1)
                    .bind(&RawTm::var(ctx_len + 1, ctx_len, &eq_ty))
                    .bind(&RawTm::var(ctx_len + 1, ctx_len, &eq_ty))
                    .bind(&RawTm::refl(ctx_len + 1))
                };
                let inhab_ty = RawScope::new(eq_ty.clone(), inhab_ty);
                let inhab = RawScope::from_parts_1(inhab_ty, inhab);
                let inhab = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: inhab,
                };

                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: motive,
                };

                StuckKind::Cong { elim, motive, inhab }
            },

            RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
                let eq_term = eq_term.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);
                let inhab = inhab.clone_unfilter(&raw_stuck.usages);
                let eq_ty = inhab.var_ty_unfiltered();

                let elim_ty = RawTy::equal(eq_ty.clone(), eq_term.clone(), eq_term);
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let inhab_ty = {
                    motive
                    .clone_weaken(1)
                    .bind(&RawTm::var(ctx_len + 1, ctx_len, &eq_ty))
                    .bind(&RawTm::refl(ctx_len + 1))
                };
                let inhab_ty = RawScope::new(eq_ty.clone(), inhab_ty);
                let inhab = RawScope::from_parts_1(inhab_ty, inhab);
                let inhab = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: inhab,
                };

                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: motive,
                };

                StuckKind::UniqueIdentity { elim, motive, inhab }
            },

            RawStuckKind::Explode { elim, motive } => {
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);

                let elim = RawTyped::from_parts(RawTy::never(ctx_len), elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: motive,
                };

                StuckKind::Explode { elim, motive }
            },

            RawStuckKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let motive = motive.clone_unfilter(&raw_stuck.usages);
                let lhs_inhab = lhs_inhab.clone_unfilter(&raw_stuck.usages);
                let rhs_inhab = rhs_inhab.clone_unfilter(&raw_stuck.usages);
                let lhs_ty = lhs_inhab.var_ty_unfiltered();
                let rhs_ty = rhs_inhab.var_ty_unfiltered();

                let lhs_inhab_ty = {
                    motive
                    .clone_weaken(1)
                    .bind(&RawTm::inj_lhs(RawTm::var(ctx_len + 1, ctx_len, &lhs_ty)))
                };
                let (lhs_inhab, _) = lhs_inhab.into_inner();
                let lhs_inhab = RawTyped::from_parts(lhs_inhab_ty, lhs_inhab);
                let lhs_inhab = RawScope::new(lhs_ty.clone(), lhs_inhab);
                let lhs_inhab = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: lhs_inhab,
                };

                let rhs_inhab_ty = {
                    motive
                    .clone_weaken(1)
                    .bind(&RawTm::inj_rhs(RawTm::var(ctx_len + 1, ctx_len, &rhs_ty)))
                };
                let (rhs_inhab, _) = rhs_inhab.into_inner();
                let rhs_inhab = RawTyped::from_parts(rhs_inhab_ty, rhs_inhab);
                let rhs_inhab = RawScope::new(rhs_ty.clone(), rhs_inhab);
                let rhs_inhab = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: rhs_inhab,
                };

                let elim_ty = RawTy::sum(lhs_ty.clone(), rhs_ty.clone());
                let elim = RawTyped::from_parts(elim_ty.clone(), elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                let motive = Scope {
                    raw_ctx: raw_ctx.clone(),
                    raw_scope: motive,
                };

                StuckKind::Case { elim, motive, lhs_inhab, rhs_inhab }
            },

            RawStuckKind::ProjHead { tail_ty, elim } => {
                let tail_ty = tail_ty.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);

                let elim_ty = RawTy::sigma(tail_ty.clone());
                let elim = RawTyped::from_parts(elim_ty.clone(), elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                StuckKind::ProjHead { elim }
            },

            RawStuckKind::ProjTail { tail_ty, elim } => {
                let tail_ty = tail_ty.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);

                let elim_ty = RawTy::sigma(tail_ty.clone());
                let elim = RawTyped::from_parts(elim_ty.clone(), elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };

                StuckKind::ProjTail { elim }
            },

            RawStuckKind::App { res_ty, elim, arg_term } => {
                let res_ty = res_ty.clone_unfilter(&raw_stuck.usages);
                let arg_ty = res_ty.var_ty_unfiltered();
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let arg_term = arg_term.clone_unfilter(&raw_stuck.usages);

                let elim_ty = RawTy::pi(res_ty);
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

            RawStuckKind::EqualEqEqTyInjective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                let eq_ty_0 = eq_ty_0.clone_unfilter(&raw_stuck.usages);
                let eq_ty_1 = eq_ty_1.clone_unfilter(&raw_stuck.usages);
                let eq_term_0_0 = eq_term_0_0.clone_unfilter(&raw_stuck.usages);
                let eq_term_0_1 = eq_term_0_1.clone_unfilter(&raw_stuck.usages);
                let eq_term_1_0 = eq_term_1_0.clone_unfilter(&raw_stuck.usages);
                let eq_term_1_1 = eq_term_1_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let elim_ty = RawTy::equal(
                    RawTy::universe(ctx_len),
                    RawTm::from_ty(RawTy::equal(eq_ty_0, eq_term_0_0, eq_term_1_0)),
                    RawTm::from_ty(RawTy::equal(eq_ty_1, eq_term_0_1, eq_term_1_1)),
                );
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };
                StuckKind::EqualEqEqTyInjective { elim }
            },

            RawStuckKind::EqualEqEqTerm0Injective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                let eq_ty_0 = eq_ty_0.clone_unfilter(&raw_stuck.usages);
                let eq_ty_1 = eq_ty_1.clone_unfilter(&raw_stuck.usages);
                let eq_term_0_0 = eq_term_0_0.clone_unfilter(&raw_stuck.usages);
                let eq_term_0_1 = eq_term_0_1.clone_unfilter(&raw_stuck.usages);
                let eq_term_1_0 = eq_term_1_0.clone_unfilter(&raw_stuck.usages);
                let eq_term_1_1 = eq_term_1_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let elim_ty = RawTy::equal(
                    RawTy::universe(ctx_len),
                    RawTm::from_ty(RawTy::equal(eq_ty_0, eq_term_0_0, eq_term_1_0)),
                    RawTm::from_ty(RawTy::equal(eq_ty_1, eq_term_0_1, eq_term_1_1)),
                );
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };
                StuckKind::EqualEqEqTerm0Injective { elim }
            },

            RawStuckKind::EqualEqEqTerm1Injective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                let eq_ty_0 = eq_ty_0.clone_unfilter(&raw_stuck.usages);
                let eq_ty_1 = eq_ty_1.clone_unfilter(&raw_stuck.usages);
                let eq_term_0_0 = eq_term_0_0.clone_unfilter(&raw_stuck.usages);
                let eq_term_0_1 = eq_term_0_1.clone_unfilter(&raw_stuck.usages);
                let eq_term_1_0 = eq_term_1_0.clone_unfilter(&raw_stuck.usages);
                let eq_term_1_1 = eq_term_1_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let elim_ty = RawTy::equal(
                    RawTy::universe(ctx_len),
                    RawTm::from_ty(RawTy::equal(eq_ty_0, eq_term_0_0, eq_term_1_0)),
                    RawTm::from_ty(RawTy::equal(eq_ty_1, eq_term_0_1, eq_term_1_1)),
                );
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };
                StuckKind::EqualEqEqTerm1Injective { elim }
            },

            RawStuckKind::SumEqLhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
                let lhs_ty_0 = lhs_ty_0.clone_unfilter(&raw_stuck.usages);
                let lhs_ty_1 = lhs_ty_1.clone_unfilter(&raw_stuck.usages);
                let rhs_ty_0 = rhs_ty_0.clone_unfilter(&raw_stuck.usages);
                let rhs_ty_1 = rhs_ty_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let elim_ty = RawTy::equal(
                    RawTy::universe(ctx_len),
                    RawTm::from_ty(RawTy::sum(lhs_ty_0, rhs_ty_0)),
                    RawTm::from_ty(RawTy::sum(lhs_ty_1, rhs_ty_1)),
                );
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };
                StuckKind::SumEqLhsInjective { elim }
            },

            RawStuckKind::SumEqRhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
                let lhs_ty_0 = lhs_ty_0.clone_unfilter(&raw_stuck.usages);
                let lhs_ty_1 = lhs_ty_1.clone_unfilter(&raw_stuck.usages);
                let rhs_ty_0 = rhs_ty_0.clone_unfilter(&raw_stuck.usages);
                let rhs_ty_1 = rhs_ty_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let elim_ty = RawTy::equal(
                    RawTy::universe(ctx_len),
                    RawTm::from_ty(RawTy::sum(lhs_ty_0, rhs_ty_0)),
                    RawTm::from_ty(RawTy::sum(lhs_ty_1, rhs_ty_1)),
                );
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };
                StuckKind::SumEqRhsInjective { elim }
            },

            RawStuckKind::SigmaEqHeadInjective { tail_ty_0, tail_ty_1, elim } => {
                let tail_ty_0 = tail_ty_0.clone_unfilter(&raw_stuck.usages);
                let tail_ty_1 = tail_ty_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let elim_ty = RawTy::equal(
                    RawTy::universe(ctx_len),
                    RawTm::from_ty(RawTy::sigma(tail_ty_0)),
                    RawTm::from_ty(RawTy::sigma(tail_ty_1)),
                );
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };
                StuckKind::SigmaEqHeadInjective { elim }
            },

            RawStuckKind::SigmaEqTailInjective { tail_ty_0, tail_ty_1, elim } => {
                let tail_ty_0 = tail_ty_0.clone_unfilter(&raw_stuck.usages);
                let tail_ty_1 = tail_ty_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let elim_ty = RawTy::equal(
                    RawTy::universe(ctx_len),
                    RawTm::from_ty(RawTy::sigma(tail_ty_0)),
                    RawTm::from_ty(RawTy::sigma(tail_ty_1)),
                );
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };
                StuckKind::SigmaEqTailInjective { elim }
            },

            RawStuckKind::PiEqArgInjective { res_ty_0, res_ty_1, elim } => {
                let res_ty_0 = res_ty_0.clone_unfilter(&raw_stuck.usages);
                let res_ty_1 = res_ty_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let elim_ty = RawTy::equal(
                    RawTy::universe(ctx_len),
                    RawTm::from_ty(RawTy::pi(res_ty_0)),
                    RawTm::from_ty(RawTy::pi(res_ty_1)),
                );
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };
                StuckKind::PiEqArgInjective { elim }
            },

            RawStuckKind::PiEqResInjective { res_ty_0, res_ty_1, elim } => {
                let res_ty_0 = res_ty_0.clone_unfilter(&raw_stuck.usages);
                let res_ty_1 = res_ty_1.clone_unfilter(&raw_stuck.usages);
                let elim = elim.clone_unfilter(&raw_stuck.usages);
                let elim_ty = RawTy::equal(
                    RawTy::universe(ctx_len),
                    RawTm::from_ty(RawTy::pi(res_ty_0)),
                    RawTm::from_ty(RawTy::pi(res_ty_1)),
                );
                let elim = RawTyped::from_parts(elim_ty, elim);
                let elim = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck: elim,
                };
                StuckKind::PiEqResInjective { elim }
            },
        }
    }

    pub fn contains_var(&self, index: usize) -> bool {
        self.raw_typed_stuck.usages[index]
    }

    /*
    pub fn strengthen_maximally(&self) -> (Stuck<S>, Usages) {
        let usages = self.raw_typed_stuck.usages.with_usages_from_ctx(&self.raw_ctx);
        let raw_ctx = self.raw_ctx.filter(usages.len(), &usages);
        let raw_typed_stuck = self.raw_typed_stuck.clone_filter(&usages);
        let stuck = Stuck { raw_ctx, raw_typed_stuck };
        (stuck, usages)
    }
    */

    /*
    pub fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> Stuck<V> {
        let mut map_user_ty = map_user_ty;
        let mut map_user_term = map_user_term;

        let Stuck { raw_ctx, raw_typed_stuck } = self;
        let raw_ctx = raw_ctx.map_scheme(&mut map_user_ty, &mut map_user_term);
        let raw_typed_stuck = raw_typed_stuck.map_scheme(&mut map_user_ty, &mut map_user_term);
        Stuck { raw_ctx, raw_typed_stuck }
    }
    */

    pub fn as_var(&self) -> Option<usize> {
        self.raw_typed_stuck.inner_unfiltered().as_var()
    }
}

