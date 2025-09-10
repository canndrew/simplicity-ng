use crate::priv_prelude::*;

pub type RawStuck<S> = Weaken<Intern<RawStuckKind<S>>>;

#[derive_where(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RawStuckKind<S: Scheme> {
    Var,
    ForLoop {
        elim: RawStuck<S>,
        motive: RawScope<S, Intern<RawTyKind<S>>>,
        zero_inhab: RawTm<S>,
        succ_inhab: RawScope<S, RawScopeKind<S, Intern<RawTmKind<S>>>>,
    },
    Nat {
        nat: RawNat<S>,
    },
    Cong {
        eq_term_0: RawTm<S>,
        eq_term_1: RawTm<S>,
        elim: RawStuck<S>,
        motive: RawScope<S, RawScopeKind<S, RawScopeKind<S, Intern<RawTyKind<S>>>>>,
        inhab: RawScope<S, Intern<RawTmKind<S>>>,
    },
    UniqueIdentity {
        eq_term: RawTm<S>,
        elim: RawStuck<S>,
        motive: RawScope<S, RawScopeKind<S, Intern<RawTyKind<S>>>>,
        inhab: RawScope<S, Intern<RawTmKind<S>>>,
    },
    Explode {
        elim: RawStuck<S>,
        motive: RawScope<S, Intern<RawTyKind<S>>>,
    },
    Case {
        elim: RawStuck<S>,
        motive: RawScope<S, Intern<RawTyKind<S>>>,
        lhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
        rhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
    },
    ProjHead {
        tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    ProjTail {
        tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    App {
        res_ty: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
        arg_term: RawTm<S>,
    },

    EqualEqEqTyInjective {
        eq_ty_0: RawTy<S>,
        eq_ty_1: RawTy<S>,
        eq_term_0_0: RawTm<S>,
        eq_term_0_1: RawTm<S>,
        eq_term_1_0: RawTm<S>,
        eq_term_1_1: RawTm<S>,
        elim: RawStuck<S>,
    },
    EqualEqEqTerm0Injective {
        eq_ty_0: RawTy<S>,
        eq_ty_1: RawTy<S>,
        eq_term_0_0: RawTm<S>,
        eq_term_0_1: RawTm<S>,
        eq_term_1_0: RawTm<S>,
        eq_term_1_1: RawTm<S>,
        elim: RawStuck<S>,
    },
    EqualEqEqTerm1Injective {
        eq_ty_0: RawTy<S>,
        eq_ty_1: RawTy<S>,
        eq_term_0_0: RawTm<S>,
        eq_term_0_1: RawTm<S>,
        eq_term_1_0: RawTm<S>,
        eq_term_1_1: RawTm<S>,
        elim: RawStuck<S>,
    },

    SumEqLhsInjective {
        lhs_ty_0: RawTy<S>,
        lhs_ty_1: RawTy<S>,
        rhs_ty_0: RawTy<S>,
        rhs_ty_1: RawTy<S>,
        elim: RawStuck<S>,
    },
    SumEqRhsInjective {
        lhs_ty_0: RawTy<S>,
        lhs_ty_1: RawTy<S>,
        rhs_ty_0: RawTy<S>,
        rhs_ty_1: RawTy<S>,
        elim: RawStuck<S>,
    },

    SigmaEqHeadInjective {
        tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    SigmaEqTailInjective {
        tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },

    PiEqArgInjective {
        res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    PiEqResInjective {
        res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
}

impl<S: Scheme> RawStuck<S> {
    pub(crate) fn as_var(&self) -> Option<usize> {
        match self.weak.get_clone() {
            RawStuckKind::Var => {
                Some(self.usages.index_of_single_one().unwrap())
            },
            _ => None,
        }
    }

    pub(crate) fn var(ctx_len: usize, index: usize) -> RawStuck<S> {
        Weaken {
            usages: Usages::single_one(ctx_len, index),
            weak: RawStuckKind::var(),
        }
    }

    pub(crate) fn for_loop(
        mut elim: RawStuck<S>,
        mut motive: RawScope<S, Intern<RawTyKind<S>>>,
        mut zero_inhab: RawTm<S>,
        mut succ_inhab: RawScope<S, RawScopeKind<S, Intern<RawTmKind<S>>>>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut elim.usages,
            &mut motive.usages,
            &mut zero_inhab.usages,
            &mut succ_inhab.usages,
        ]);

        let weak = Intern::new(RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab });
        Weaken { usages, weak }
    }

    pub(crate) fn nat(mut nat: RawNat<S>) -> RawStuck<S> {
        let usages = Usages::merge_mut([&mut nat.usages]);

        let weak = Intern::new(RawStuckKind::Nat { nat });
        Weaken { usages, weak }
    }

    /*
    pub(crate) fn max(
        max_term_0: RawStuck<S>,
        max_term_1: RawTm<S>,
    ) -> RawStuck<S> {
        if let RawStuckKind::Max { max_term_0: max_term_00, max_term_1: max_term_01 } = &*max_term_0.weak {
            let max_term_00 = max_term_00.clone_unfilter(&max_term_0.usages);
            let max_term_01 = max_term_01.clone_unfilter(&max_term_0.usages);
            return RawStuck::max(max_term_00, RawTm::max(max_term_01, max_term_1));
        }

    }
    */

    pub(crate) fn cong(
        mut eq_term_0: RawTm<S>,
        mut eq_term_1: RawTm<S>,
        mut elim: RawStuck<S>,
        mut motive: RawScope<S, RawScopeKind<S, RawScopeKind<S, Intern<RawTyKind<S>>>>>,
        mut inhab: RawScope<S, Intern<RawTmKind<S>>>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut eq_term_0.usages,
            &mut eq_term_1.usages,
            &mut elim.usages,
            &mut motive.usages,
            &mut inhab.usages,
        ]);

        let weak = Intern::new(RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab });
        Weaken { usages, weak }
    }

    pub(crate) fn unique_identity(
        mut eq_term: RawTm<S>,
        mut elim: RawStuck<S>,
        mut motive: RawScope<S, RawScopeKind<S, Intern<RawTyKind<S>>>>,
        mut inhab: RawScope<S, Intern<RawTmKind<S>>>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut eq_term.usages,
            &mut elim.usages,
            &mut motive.usages,
            &mut inhab.usages,
        ]);

        let weak = Intern::new(RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab });
        Weaken { usages, weak }
    }

    pub(crate) fn explode(
        mut elim: RawStuck<S>,
        mut motive: RawScope<S, Intern<RawTyKind<S>>>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut elim.usages,
            &mut motive.usages,
        ]);

        let weak = Intern::new(RawStuckKind::Explode { elim, motive });
        Weaken { usages, weak }
    }

    pub(crate) fn case(
        mut elim: RawStuck<S>,
        mut motive: RawScope<S, Intern<RawTyKind<S>>>,
        mut lhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
        mut rhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut elim.usages,
            &mut motive.usages,
            &mut lhs_inhab.usages,
            &mut rhs_inhab.usages,
        ]);

        let weak = Intern::new(RawStuckKind::Case { elim, motive, lhs_inhab, rhs_inhab });
        Weaken { usages, weak }
    }

    pub(crate) fn proj_head(
        mut tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut tail_ty.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::ProjHead { tail_ty, elim });
        Weaken { usages, weak }
    }

    pub(crate) fn proj_tail(
        mut tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut tail_ty.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::ProjTail { tail_ty, elim });
        Weaken { usages, weak }
    }

    pub(crate) fn app(
        mut res_ty: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
        mut arg_term: RawTm<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut res_ty.usages,
            &mut elim.usages,
            &mut arg_term.usages,
        ]);

        let weak = Intern::new(RawStuckKind::App { res_ty ,elim, arg_term });
        Weaken { usages, weak }
    }

    pub(crate) fn unique_eta_term_opt(
        &self,
        ty_var_etas: &mut Vec<(usize, usize)>,
    ) -> Option<RawTm<S>> {
        match self.weak.get_clone() {
            RawStuckKind::Var => {
                 // ugh, have to adjust ty_vars every time we go through a filter
                None
            },
            
            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                debug_assert!(matches!(motive.weak.inner.weak.get_clone(), RawTyKind::Universe));
                let ctx_len = zero_inhab.usages.len();
                let zero_inhab_term = zero_inhab.unique_eta_term_opt(ty_var_etas)?;
                let succ_inhab_term = {
                    let mut succ_inhab_inner = {
                        succ_inhab
                        .inner_unfiltered_with_var()
                        .inner_unfiltered_with_var()
                    };
                    succ_inhab_inner.weaken(1);

                    ty_var_etas.push((ctx_len + 1, ctx_len + 2));
                    let succ_inhab_term = succ_inhab_inner.unique_eta_term_opt(ty_var_etas)?;
                    ty_var_etas.pop();

                    let succ_inhab_term = RawScope::new(
                        RawTy::stuck(RawStuck::var(ctx_len + 2, ctx_len + 1)),
                        succ_inhab_term,
                    );
                    let succ_inhab_term = RawScope::new(
                        RawTy::universe(ctx_len + 1),
                        succ_inhab_term,
                    );
                    let succ_inhab_term = {
                        succ_inhab_term
                        .bind(
                            &RawTm::stuck(
                                RawStuck::for_loop(
                                    RawStuck::var(ctx_len + 1, ctx_len),
                                    RawScope::new(
                                        RawTy::nat(ctx_len + 1),
                                        RawTy::universe(ctx_len + 2),
                                    ),
                                    zero_inhab.clone_weaken(1),
                                    succ_inhab.clone_weaken(1),
                                ),
                            )
                        )
                    };
                    let succ_inhab_term = RawScope::new(
                        RawTy::nat(ctx_len),
                        succ_inhab_term,
                    );
                    succ_inhab_term
                };
                let term = RawTm::stuck(
                    RawStuck::for_loop(
                        elim.clone(),
                        RawScope::new(
                            RawTy::nat(ctx_len),
                            RawTy::stuck(
                                RawStuck::for_loop(
                                    RawStuck::var(ctx_len + 1, ctx_len),
                                    motive.clone_weaken(1),
                                    zero_inhab.clone_weaken(1),
                                    succ_inhab.clone_weaken(1),
                                ),
                            ),
                        ),
                        zero_inhab_term,
                        succ_inhab_term,
                    ),
                );
                Some(term.unfilter(&self.usages))
            },

            RawStuckKind::Nat { nat: _ } => unreachable!(),

            RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
                debug_assert!(matches!(
                    motive.weak.inner.weak.inner.weak.inner.weak.get_clone(),
                    RawTyKind::Universe,
                ));
                let inhab_term = inhab.unique_eta_term_opt(ty_var_etas)?;
                let inner_ctx_len = elim.usages.len();
                let eq_ty = inhab.var_ty_unfiltered();
                let eq_ty_weak_1 = eq_ty.clone_weaken(1);
                let term = RawTm::stuck(
                    RawStuck::cong(
                        eq_term_0.clone(),
                        eq_term_1.clone(),
                        elim.clone(),
                        RawScope::new(
                            eq_ty.clone(),
                            RawScope::new(
                                eq_ty_weak_1.clone(),
                                RawScope::new(
                                    RawTy::equal(
                                        eq_ty.clone_weaken(2),
                                        RawTm::var(inner_ctx_len + 2, inner_ctx_len, &eq_ty),
                                        RawTm::var(inner_ctx_len + 2, inner_ctx_len + 1, &eq_ty_weak_1),
                                    ),
                                    RawTy::stuck(
                                        RawStuck::cong(
                                            RawTm::var(inner_ctx_len + 3, inner_ctx_len, &eq_ty),
                                            RawTm::var(inner_ctx_len + 3, inner_ctx_len + 1, &eq_ty_weak_1),
                                            RawStuck::var(inner_ctx_len + 3, inner_ctx_len + 2),
                                            motive.clone_weaken(3),
                                            inhab.clone_weaken(3),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                        inhab_term,
                    ),
                );
                Some(term.unfilter(&self.usages))
            },

            RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
                debug_assert!(matches!(motive.weak.inner.weak.inner.weak.get_clone(), RawTyKind::Universe));
                let inhab_term = inhab.unique_eta_term_opt(ty_var_etas)?;
                let inner_ctx_len = elim.usages.len();
                let eq_ty = inhab.var_ty_unfiltered();
                let term = RawTm::stuck(
                    RawStuck::unique_identity(
                        eq_term.clone(),
                        elim.clone(),
                        RawScope::new(
                            eq_ty.clone(),
                            RawScope::new(
                                RawTy::equal(
                                    eq_ty.clone_weaken(1),
                                    RawTm::var(inner_ctx_len + 1, inner_ctx_len, &eq_ty),
                                    RawTm::var(inner_ctx_len + 1, inner_ctx_len, &eq_ty),
                                ),
                                RawTy::stuck(
                                    RawStuck::unique_identity(
                                        RawTm::var(inner_ctx_len + 2, inner_ctx_len, &eq_ty),
                                        RawStuck::var(inner_ctx_len + 2, inner_ctx_len + 1),
                                        motive.clone_weaken(2),
                                        inhab.clone_weaken(2),
                                    ),
                                ),
                            ),
                        ),
                        inhab_term,
                    ),
                );
                Some(term.unfilter(&self.usages))
            },

            RawStuckKind::Explode { elim, motive } => {
                debug_assert!(matches!(motive.weak.inner.weak.get_clone(), RawTyKind::Universe));
                let inner_ctx_len = elim.usages.len();
                let never_ty = motive.var_ty_unfiltered();
                let term = RawTm::stuck(
                    RawStuck::explode(
                        elim.clone(),
                        RawScope::new(
                            never_ty,
                            RawTy::stuck(
                                RawStuck::explode(
                                    RawStuck::var(inner_ctx_len + 1, inner_ctx_len),
                                    motive.clone_weaken(1),
                                ),
                            ),
                        ),
                    ),
                );
                Some(term.unfilter(&self.usages))
            },

            RawStuckKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                debug_assert!(matches!(motive.weak.inner.weak.get_clone(), RawTyKind::Universe));
                let inner_ctx_len = elim.usages.len();
                let lhs_inhab_term = lhs_inhab.unique_eta_term_opt(ty_var_etas)?;
                let rhs_inhab_term = rhs_inhab.unique_eta_term_opt(ty_var_etas)?;
                let lhs_ty = lhs_inhab.var_ty_unfiltered();
                let rhs_ty = rhs_inhab.var_ty_unfiltered();

                let term = RawTm::stuck(
                    RawStuck::case(
                        elim.clone(),
                        RawScope::new(
                            RawTy::sum(lhs_ty, rhs_ty),
                            RawTy::stuck(
                                RawStuck::case(
                                    RawStuck::var(inner_ctx_len + 1, inner_ctx_len),
                                    motive.clone_weaken(1),
                                    lhs_inhab.clone_weaken(1),
                                    rhs_inhab.clone_weaken(1),
                                ),
                            ),
                        ),
                        lhs_inhab_term,
                        rhs_inhab_term,
                    ),
                );
                Some(term.unfilter(&self.usages))
            },

            RawStuckKind::ProjHead { .. } => None,
            RawStuckKind::ProjTail { .. } => None,
            RawStuckKind::App { .. } => None,

            RawStuckKind::EqualEqEqTyInjective { .. } => None,
            RawStuckKind::EqualEqEqTerm0Injective { .. } => None,
            RawStuckKind::EqualEqEqTerm1Injective { .. } => None,
            RawStuckKind::SumEqLhsInjective { .. } => None,
            RawStuckKind::SumEqRhsInjective { .. } => None,
            RawStuckKind::SigmaEqHeadInjective { .. } => None,
            RawStuckKind::SigmaEqTailInjective { .. } => None,
            RawStuckKind::PiEqArgInjective { .. } => None,
            RawStuckKind::PiEqResInjective { .. } => None,
        }
    }

    pub(crate) fn equal_eq_eq_ty_injective(
        mut eq_ty_0: RawTy<S>,
        mut eq_ty_1: RawTy<S>,
        mut eq_term_0_0: RawTm<S>,
        mut eq_term_0_1: RawTm<S>,
        mut eq_term_1_0: RawTm<S>,
        mut eq_term_1_1: RawTm<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut eq_ty_0.usages,
            &mut eq_ty_1.usages,
            &mut eq_term_0_0.usages,
            &mut eq_term_0_1.usages,
            &mut eq_term_1_0.usages,
            &mut eq_term_1_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::EqualEqEqTyInjective {
            eq_ty_0, eq_ty_1,
            eq_term_0_0, eq_term_0_1,
            eq_term_1_0, eq_term_1_1,
            elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn equal_eq_eq_term_0_injective(
        mut eq_ty_0: RawTy<S>,
        mut eq_ty_1: RawTy<S>,
        mut eq_term_0_0: RawTm<S>,
        mut eq_term_0_1: RawTm<S>,
        mut eq_term_1_0: RawTm<S>,
        mut eq_term_1_1: RawTm<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut eq_ty_0.usages,
            &mut eq_ty_1.usages,
            &mut eq_term_0_0.usages,
            &mut eq_term_0_1.usages,
            &mut eq_term_1_0.usages,
            &mut eq_term_1_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::EqualEqEqTerm0Injective {
            eq_ty_0, eq_ty_1,
            eq_term_0_0, eq_term_0_1,
            eq_term_1_0, eq_term_1_1,
            elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn equal_eq_eq_term_1_injective(
        mut eq_ty_0: RawTy<S>,
        mut eq_ty_1: RawTy<S>,
        mut eq_term_0_0: RawTm<S>,
        mut eq_term_0_1: RawTm<S>,
        mut eq_term_1_0: RawTm<S>,
        mut eq_term_1_1: RawTm<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut eq_ty_0.usages,
            &mut eq_ty_1.usages,
            &mut eq_term_0_0.usages,
            &mut eq_term_0_1.usages,
            &mut eq_term_1_0.usages,
            &mut eq_term_1_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::EqualEqEqTerm1Injective {
            eq_ty_0, eq_ty_1,
            eq_term_0_0, eq_term_0_1,
            eq_term_1_0, eq_term_1_1,
            elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sum_eq_lhs_injective(
        mut lhs_ty_0: RawTy<S>,
        mut lhs_ty_1: RawTy<S>,
        mut rhs_ty_0: RawTy<S>,
        mut rhs_ty_1: RawTy<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut lhs_ty_0.usages,
            &mut lhs_ty_1.usages,
            &mut rhs_ty_0.usages,
            &mut rhs_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SumEqLhsInjective {
            lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sum_eq_rhs_injective(
        mut lhs_ty_0: RawTy<S>,
        mut lhs_ty_1: RawTy<S>,
        mut rhs_ty_0: RawTy<S>,
        mut rhs_ty_1: RawTy<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut lhs_ty_0.usages,
            &mut lhs_ty_1.usages,
            &mut rhs_ty_0.usages,
            &mut rhs_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SumEqRhsInjective {
            lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sigma_eq_head_injective(
        mut tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut tail_ty_0.usages,
            &mut tail_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SigmaEqHeadInjective {
            tail_ty_0, tail_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sigma_eq_tail_injective(
        mut tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut tail_ty_0.usages,
            &mut tail_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SigmaEqTailInjective {
            tail_ty_0, tail_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn pi_eq_arg_injective(
        mut res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut res_ty_0.usages,
            &mut res_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::PiEqArgInjective {
            res_ty_0, res_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn pi_eq_res_injective(
        mut res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut res_ty_0.usages,
            &mut res_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::PiEqResInjective {
            res_ty_0, res_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn is_unique_eta_term_for_type(&self, ty: &RawTy<S>) -> bool {
        debug_assert_eq!(self.usages.len(), ty.usages.len());
        match self.weak.get_clone() {
            RawStuckKind::Var => false,
            RawStuckKind::Nat { .. } => false,

            RawStuckKind::ForLoop { .. } => false,  // TODO

            RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
                let RawTyKind::Stuck { stuck: ty_stuck } = ty.weak.get_clone() else {
                    return false;
                };
                let RawStuckKind::Cong {
                    eq_term_0: ty_eq_term_0,
                    eq_term_1: ty_eq_term_1,
                    elim: ty_elim,
                    motive: ty_motive,
                    inhab: ty_inhab,
                } = ty_stuck.weak.get_clone() else {
                    return false;
                };

                if cfg!(debug_assertions) {
                    assert!(matches!(
                        ty_motive.weak.inner.weak.inner.weak.inner.weak.get_clone(),
                        RawTyKind::Universe,
                    ));
                }

                (
                    motive.var_ty_unfiltered().unfilter(&self.usages)
                    ==
                    ty_motive.var_ty_unfiltered().unfilter(&ty.usages)
                )
                && eq_term_0.clone_unfilter(&self.usages) == ty_eq_term_0.unfilter(&ty.usages)
                && eq_term_1.clone_unfilter(&self.usages) == ty_eq_term_1.unfilter(&ty.usages)
                && elim.clone_unfilter(&self.usages) == ty_elim.unfilter(&ty.usages)
                && {
                    motive
                    .bind(&eq_term_0)
                    .bind(&eq_term_1)
                    .bind(&RawTm::stuck(elim))
                    .unfilter(&self.usages)
                    ==
                    *ty
                }
                && {
                    let inhab_term = {
                        inhab
                        .unfilter(&self.usages)
                        .inner_unfiltered_with_var()
                    };
                    let inhab_ty = {
                        ty_inhab
                        .unfilter(&ty.usages)
                        .inner_unfiltered_with_var()
                    };
                    let inhab_ty = RawTy::from_term(inhab_ty);
                    inhab_term.is_unique_eta_term_for_type(&inhab_ty)
                }
            },

            RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
                let RawTyKind::Stuck { stuck: ty_stuck } = ty.weak.get_clone() else {
                    return false;
                };
                let RawStuckKind::UniqueIdentity {
                    eq_term: ty_eq_term,
                    elim: ty_elim,
                    motive: ty_motive,
                    inhab: ty_inhab,
                } = ty_stuck.weak.get_clone() else {
                    return false;
                };

                if cfg!(debug_assertions) {
                    assert!(matches!(
                        ty_motive.weak.inner.weak.inner.weak.get_clone(),
                        RawTyKind::Universe,
                    ));
                }

                (
                    motive.var_ty_unfiltered().unfilter(&self.usages)
                    ==
                    ty_motive.var_ty_unfiltered().unfilter(&ty.usages)
                )
                && eq_term.clone_unfilter(&self.usages) == ty_eq_term.unfilter(&ty.usages)
                && elim.clone_unfilter(&self.usages) == ty_elim.unfilter(&ty.usages)
                && {
                    motive
                    .bind(&eq_term)
                    .bind(&RawTm::stuck(elim))
                    .unfilter(&self.usages)
                    ==
                    *ty
                }
                && {
                    let inhab_term = {
                        inhab
                        .unfilter(&self.usages)
                        .inner_unfiltered_with_var()
                    };
                    let inhab_ty = {
                        ty_inhab
                        .unfilter(&ty.usages)
                        .inner_unfiltered_with_var()
                    };
                    let inhab_ty = RawTy::from_term(inhab_ty);
                    inhab_term.is_unique_eta_term_for_type(&inhab_ty)
                }
            },

            RawStuckKind::Explode { elim, motive } => {
                let RawTyKind::Stuck { stuck: ty_stuck } = ty.weak.get_clone() else {
                    return false;
                };
                let RawStuckKind::Explode {
                    elim: ty_elim,
                    motive: ty_motive,
                } = ty_stuck.weak.get_clone() else {
                    return false;
                };

                if cfg!(debug_assertions) {
                    assert!(matches!(
                        ty_motive.weak.inner.weak.get_clone(),
                        RawTyKind::Universe,
                    ));
                }

                elim.clone_unfilter(&self.usages) == ty_elim.unfilter(&ty.usages)
                && motive.bind(&RawTm::stuck(elim)) == *ty
            },

            RawStuckKind::Case {
                elim,
                motive,
                lhs_inhab,
                rhs_inhab,
            } => {
                let RawTyKind::Stuck { stuck: ty_stuck } = ty.weak.get_clone() else {
                    return false;
                };
                let RawStuckKind::Case {
                    elim: ty_elim,
                    motive: ty_motive,
                    lhs_inhab: ty_lhs_inhab,
                    rhs_inhab: ty_rhs_inhab,
                } = ty_stuck.weak.get_clone() else {
                    return false;
                };

                if cfg!(debug_assertions) {
                    assert!(matches!(
                        ty_motive.weak.inner.weak.get_clone(),
                        RawTyKind::Universe,
                    ));
                }

                (
                    lhs_inhab.var_ty_unfiltered().unfilter(&self.usages)
                    ==
                    ty_lhs_inhab.var_ty_unfiltered().unfilter(&ty.usages)
                )
                && (
                    rhs_inhab.var_ty_unfiltered().unfilter(&self.usages)
                    ==
                    ty_rhs_inhab.var_ty_unfiltered().unfilter(&ty.usages)
                )
                && elim.clone_unfilter(&self.usages) == ty_elim.unfilter(&ty.usages)
                && (
                    motive.bind(&RawTm::stuck(elim))
                    ==
                    *ty
                )
                && {
                    let lhs_inhab_term = {
                        lhs_inhab
                        .unfilter(&self.usages)
                        .inner_unfiltered_with_var()
                    };
                    let lhs_inhab_ty = {
                        ty_lhs_inhab
                        .unfilter(&ty.usages)
                        .inner_unfiltered_with_var()
                    };
                    let lhs_inhab_ty = RawTy::from_term(lhs_inhab_ty);
                    lhs_inhab_term.is_unique_eta_term_for_type(&lhs_inhab_ty)
                }
                && {
                    let rhs_inhab_term = {
                        rhs_inhab
                        .unfilter(&self.usages)
                        .inner_unfiltered_with_var()
                    };
                    let rhs_inhab_ty = {
                        ty_rhs_inhab
                        .unfilter(&ty.usages)
                        .inner_unfiltered_with_var()
                    };
                    let rhs_inhab_ty = RawTy::from_term(rhs_inhab_ty);
                    rhs_inhab_term.is_unique_eta_term_for_type(&rhs_inhab_ty)
                }
            },

            RawStuckKind::ProjHead { .. } |
            RawStuckKind::ProjTail { .. } |
            RawStuckKind::App { .. } |
            RawStuckKind::EqualEqEqTyInjective { .. } |
            RawStuckKind::EqualEqEqTerm0Injective { .. } |
            RawStuckKind::EqualEqEqTerm1Injective { .. } |
            RawStuckKind::SumEqLhsInjective { .. } |
            RawStuckKind::SumEqRhsInjective { .. } |
            RawStuckKind::SigmaEqHeadInjective { .. } |
            RawStuckKind::SigmaEqTailInjective { .. } |
            RawStuckKind::PiEqArgInjective { .. } |
            RawStuckKind::PiEqResInjective { .. } => false,
        }
    }
}

impl<S: Scheme> RawStuckKind<S> {
    pub(crate) fn var() -> Intern<RawStuckKind<S>> {
        Intern::new(RawStuckKind::Var)
    }

    /*
    fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> RawStuckKind<V> {
        match self {
            RawStuckKind::Var => RawStuckKind::Var,
            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                let motive = motive.map_scheme(map_user_ty, map_user_term);
                let zero_inhab = zero_inhab.map_scheme(map_user_ty, map_user_term);
                let succ_inhab = succ_inhab.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab }
            },

            RawStuckKind::Nat { nat } => {
                let nat = nat.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::Nat { nat }
            },
            RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
                let eq_term_0 = eq_term_0.map_scheme(map_user_ty, map_user_term);
                let eq_term_1 = eq_term_1.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                let motive = motive.map_scheme(map_user_ty, map_user_term);
                let inhab = inhab.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab }
            },
            RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
                let eq_term = eq_term.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                let motive = motive.map_scheme(map_user_ty, map_user_term);
                let inhab = inhab.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab }
            },
            RawStuckKind::Explode { elim, motive } => {
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                let motive = motive.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::Explode { elim, motive }
            },
            RawStuckKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                let motive = motive.map_scheme(map_user_ty, map_user_term);
                let lhs_inhab = lhs_inhab.map_scheme(map_user_ty, map_user_term);
                let rhs_inhab = rhs_inhab.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::Case { elim, motive, lhs_inhab, rhs_inhab }
            },
            RawStuckKind::ProjHead { tail_ty, elim } => {
                let tail_ty = tail_ty.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::ProjHead { tail_ty, elim }
            },
            RawStuckKind::ProjTail { tail_ty, elim } => {
                let tail_ty = tail_ty.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::ProjTail { tail_ty, elim }
            },
            RawStuckKind::App { res_ty, elim, arg_term } => {
                let res_ty = res_ty.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                let arg_term = arg_term.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::App { res_ty, elim, arg_term }
            },

            RawStuckKind::SumEqLhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
                let lhs_ty_0 = lhs_ty_0.map_scheme(map_user_ty, map_user_term);
                let lhs_ty_1 = lhs_ty_1.map_scheme(map_user_ty, map_user_term);
                let rhs_ty_0 = rhs_ty_0.map_scheme(map_user_ty, map_user_term);
                let rhs_ty_1 = rhs_ty_1.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::SumEqLhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim }
            },
            RawStuckKind::SumEqRhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
                let lhs_ty_0 = lhs_ty_0.map_scheme(map_user_ty, map_user_term);
                let lhs_ty_1 = lhs_ty_1.map_scheme(map_user_ty, map_user_term);
                let rhs_ty_0 = rhs_ty_0.map_scheme(map_user_ty, map_user_term);
                let rhs_ty_1 = rhs_ty_1.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::SumEqRhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim }
            },

            RawStuckKind::SigmaEqHeadInjective { tail_ty_0, tail_ty_1, elim } => {
                let tail_ty_0 = tail_ty_0.map_scheme(map_user_ty, map_user_term);
                let tail_ty_1 = tail_ty_1.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::SigmaEqHeadInjective { tail_ty_0, tail_ty_1, elim }
            },
            RawStuckKind::SigmaEqTailInjective { tail_ty_0, tail_ty_1, elim } => {
                let tail_ty_0 = tail_ty_0.map_scheme(map_user_ty, map_user_term);
                let tail_ty_1 = tail_ty_1.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::SigmaEqTailInjective { tail_ty_0, tail_ty_1, elim }
            },

            RawStuckKind::PiEqArgInjective { res_ty_0, res_ty_1, elim } => {
                let res_ty_0 = res_ty_0.map_scheme(map_user_ty, map_user_term);
                let res_ty_1 = res_ty_1.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::PiEqArgInjective { res_ty_0, res_ty_1, elim }
            },
            RawStuckKind::PiEqResInjective { res_ty_0, res_ty_1, elim } => {
                let res_ty_0 = res_ty_0.map_scheme(map_user_ty, map_user_term);
                let res_ty_1 = res_ty_1.map_scheme(map_user_ty, map_user_term);
                let elim = elim.map_scheme(map_user_ty, map_user_term);
                RawStuckKind::PiEqResInjective { res_ty_0, res_ty_1, elim }
            },

        }
    }
    */
}

/*
impl<S: Scheme> Substitute<S> for RawStuck<S> {
    type RawSubstOutput = RawTm<S>;

    fn to_subst_output(&self) -> RawTm<S> {
        RawTm::stuck(self.clone())
    }

    fn subst(&self, filter: &Usages, var_term: &RawTm<S>) -> RawTm<S> {
        match self.usages.subst(filter, var_term) {
            ControlFlow::Break(usages) => {
                let stuck = Weaken {
                    usages,
                    kind: self.kind.clone(),
                };
                RawTm::stuck(stuck)
            },
            ControlFlow::Continue((unfilter, sub_filter, var_term)) => {
                let mut ret = self.kind.subst(&sub_filter, var_term);
                ret.usages.unfilter(&unfilter);
                ret
            },
        }
    }
}
*/

impl<S: Scheme> Substitute<S> for Intern<RawStuckKind<S>> {
    type RawSubstOutput = Intern<RawTmKind<S>>;

    fn to_subst_output(&self, num_usages: usize) -> Intern<RawTmKind<S>> {
        let usages = Usages::ones(num_usages);
        let stuck = Weaken { usages, weak: self.clone() };
        Intern::new(RawTmKind::Stuck {
            stuck: stuck,
        })
    }

    fn subst(&self, filter: &Usages, var_term: RawTm<S>) -> RawTm<S> {
        match self.get_clone() {
            RawStuckKind::Var => {
                let mut var_term = var_term;
                var_term.weaken(filter.len().strict_sub(1).strict_sub(var_term.usages.len()));
                var_term
            },

            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let zero_inhab = zero_inhab.subst(filter, &var_term);
                let succ_inhab = succ_inhab.subst(filter, &var_term);
                RawTm::for_loop(elim, motive, zero_inhab, succ_inhab)
            },

            RawStuckKind::Nat { nat } => {
                nat.subst(filter, &var_term)
            },

            RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
                let eq_term_0 = eq_term_0.subst(filter, &var_term);
                let eq_term_1 = eq_term_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let inhab = inhab.subst(filter, &var_term);
                RawTm::cong(eq_term_0, eq_term_1, elim, motive, inhab)
            },

            RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
                let eq_term = eq_term.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let inhab = inhab.subst(filter, &var_term);
                RawTm::unique_identity(eq_term, elim, motive, inhab)
            },

            RawStuckKind::Explode { elim, motive } => {
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                RawTm::explode(elim, motive)
            },

            RawStuckKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let lhs_inhab = lhs_inhab.subst(filter, &var_term);
                let rhs_inhab = rhs_inhab.subst(filter, &var_term);
                RawTm::case(elim, motive, lhs_inhab, rhs_inhab)
            },

            RawStuckKind::ProjHead { tail_ty, elim } => {
                let tail_ty = tail_ty.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::proj_head(tail_ty, elim)
            },

            RawStuckKind::ProjTail { tail_ty, elim } => {
                let tail_ty = tail_ty.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::proj_tail(tail_ty, elim)
            },

            RawStuckKind::App { res_ty, elim, arg_term } => {
                let res_ty = res_ty.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                let arg_term = arg_term.subst(filter, &var_term);
                RawTm::app(res_ty, elim, arg_term)
            },

            RawStuckKind::EqualEqEqTyInjective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                let eq_ty_0 = eq_ty_0.subst(filter, &var_term);
                let eq_ty_1 = eq_ty_1.subst(filter, &var_term);
                let eq_term_0_0 = eq_term_0_0.subst(filter, &var_term);
                let eq_term_0_1 = eq_term_0_1.subst(filter, &var_term);
                let eq_term_1_0 = eq_term_1_0.subst(filter, &var_term);
                let eq_term_1_1 = eq_term_1_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::equal_eq_eq_ty_injective(
                    eq_ty_0,
                    eq_ty_1,
                    eq_term_0_0,
                    eq_term_0_1,
                    eq_term_1_0,
                    eq_term_1_1,
                    elim,
                )
            },
            RawStuckKind::EqualEqEqTerm0Injective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                let eq_ty_0 = eq_ty_0.subst(filter, &var_term);
                let eq_ty_1 = eq_ty_1.subst(filter, &var_term);
                let eq_term_0_0 = eq_term_0_0.subst(filter, &var_term);
                let eq_term_0_1 = eq_term_0_1.subst(filter, &var_term);
                let eq_term_1_0 = eq_term_1_0.subst(filter, &var_term);
                let eq_term_1_1 = eq_term_1_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::equal_eq_eq_term_0_injective(
                    eq_ty_0,
                    eq_ty_1,
                    eq_term_0_0,
                    eq_term_0_1,
                    eq_term_1_0,
                    eq_term_1_1,
                    elim,
                )
            },
            RawStuckKind::EqualEqEqTerm1Injective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                let eq_ty_0 = eq_ty_0.subst(filter, &var_term);
                let eq_ty_1 = eq_ty_1.subst(filter, &var_term);
                let eq_term_0_0 = eq_term_0_0.subst(filter, &var_term);
                let eq_term_0_1 = eq_term_0_1.subst(filter, &var_term);
                let eq_term_1_0 = eq_term_1_0.subst(filter, &var_term);
                let eq_term_1_1 = eq_term_1_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::equal_eq_eq_term_1_injective(
                    eq_ty_0,
                    eq_ty_1,
                    eq_term_0_0,
                    eq_term_0_1,
                    eq_term_1_0,
                    eq_term_1_1,
                    elim,
                )
            },

            RawStuckKind::SumEqLhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
                let lhs_ty_0 = lhs_ty_0.subst(filter, &var_term);
                let lhs_ty_1 = lhs_ty_1.subst(filter, &var_term);
                let rhs_ty_0 = rhs_ty_0.subst(filter, &var_term);
                let rhs_ty_1 = rhs_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sum_eq_lhs_injective(lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim)
            },

            RawStuckKind::SumEqRhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
                let lhs_ty_0 = lhs_ty_0.subst(filter, &var_term);
                let lhs_ty_1 = lhs_ty_1.subst(filter, &var_term);
                let rhs_ty_0 = rhs_ty_0.subst(filter, &var_term);
                let rhs_ty_1 = rhs_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sum_eq_rhs_injective(lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim)
            },

            RawStuckKind::SigmaEqHeadInjective { tail_ty_0, tail_ty_1, elim } => {
                let tail_ty_0 = tail_ty_0.subst(filter, &var_term);
                let tail_ty_1 = tail_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sigma_eq_head_injective(tail_ty_0, tail_ty_1, elim)
            },

            RawStuckKind::SigmaEqTailInjective { tail_ty_0, tail_ty_1, elim } => {
                let tail_ty_0 = tail_ty_0.subst(filter, &var_term);
                let tail_ty_1 = tail_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sigma_eq_tail_injective(tail_ty_0, tail_ty_1, elim)
            },

            RawStuckKind::PiEqArgInjective { res_ty_0, res_ty_1, elim } => {
                let res_ty_0 = res_ty_0.subst(filter, &var_term);
                let res_ty_1 = res_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::pi_eq_arg_injective(res_ty_0, res_ty_1, elim)
            },

            RawStuckKind::PiEqResInjective { res_ty_0, res_ty_1, elim } => {
                let res_ty_0 = res_ty_0.subst(filter, &var_term);
                let res_ty_1 = res_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::pi_eq_res_injective(res_ty_0, res_ty_1, elim)
            },
        }
    }

    fn eliminates_var(&self, index: usize) -> bool {
        match self.get_clone() {
            RawStuckKind::Var => false,
            RawStuckKind::ForLoop { elim, motive: _, zero_inhab, succ_inhab } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index) ||
                zero_inhab.eliminates_var(index) ||
                succ_inhab.eliminates_var(index)
            },
            RawStuckKind::Nat { nat } => nat.eliminates_var(index),
            RawStuckKind::Cong { eq_term_0: _, eq_term_1: _, elim, motive: _, inhab } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index) ||
                inhab.eliminates_var(index)
            },
            RawStuckKind::UniqueIdentity { eq_term: _, elim, motive: _, inhab } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index) ||
                inhab.eliminates_var(index)
            },
            RawStuckKind::Explode { elim, motive: _ } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index)
            },
            RawStuckKind::Case { elim, motive: _, lhs_inhab, rhs_inhab } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index) ||
                lhs_inhab.eliminates_var(index) ||
                rhs_inhab.eliminates_var(index)
            },
            RawStuckKind::ProjHead { tail_ty: _, elim } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index)
            },
            RawStuckKind::ProjTail { tail_ty: _, elim } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index)
            },
            RawStuckKind::App { res_ty: _, elim, arg_term } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index) ||
                arg_term.eliminates_var(index)
            },

            RawStuckKind::EqualEqEqTyInjective { elim, .. } => {
                elim.eliminates_var(index)
            },
            RawStuckKind::EqualEqEqTerm0Injective { elim, .. } => {
                elim.eliminates_var(index)
            },
            RawStuckKind::EqualEqEqTerm1Injective { elim, .. } => {
                elim.eliminates_var(index)
            },
            RawStuckKind::SumEqLhsInjective { elim, .. } => {
                elim.eliminates_var(index)
            },
            RawStuckKind::SumEqRhsInjective { elim, .. } => {
                elim.eliminates_var(index)
            },
            RawStuckKind::SigmaEqHeadInjective { elim, .. } => {
                elim.eliminates_var(index)
            },
            RawStuckKind::SigmaEqTailInjective { elim, .. } => {
                elim.eliminates_var(index)
            },
            RawStuckKind::PiEqArgInjective { elim, .. } => {
                elim.eliminates_var(index)
            },
            RawStuckKind::PiEqResInjective { elim, .. } => {
                elim.eliminates_var(index)
            },
        }
    }
}

