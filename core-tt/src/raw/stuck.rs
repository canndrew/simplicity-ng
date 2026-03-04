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
        lhs_name: RawName<S>,
        elim: RawStuck<S>,
        motive: RawScope<S, Intern<RawTyKind<S>>>,
        lhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
        rhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
    },
    ProjHead {
        head_name: RawName<S>,
        tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    ProjTail {
        head_name: RawName<S>,
        tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    App {
        arg_name: RawName<S>,
        res_ty: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
        arg_term: RawTm<S>,
    },


    TagsApart {
        tag_0: S::Tag,
        tag_1: S::Tag,
        elim: RawStuck<S>,
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
        eq_ty: RawTy<S>,
        eq_term_0_0: RawTm<S>,
        eq_term_0_1: RawTm<S>,
        eq_term_1_0: RawTm<S>,
        eq_term_1_1: RawTm<S>,
        elim: RawStuck<S>,
    },
    EqualEqEqTerm1Injective {
        eq_ty: RawTy<S>,
        eq_term_0_0: RawTm<S>,
        eq_term_0_1: RawTm<S>,
        eq_term_1_0: RawTm<S>,
        eq_term_1_1: RawTm<S>,
        elim: RawStuck<S>,
    },

    SumEqNameInjective {
        lhs_name_0: RawName<S>,
        lhs_name_1: RawName<S>,
        lhs_ty_0: RawTy<S>,
        lhs_ty_1: RawTy<S>,
        rhs_ty_0: RawTy<S>,
        rhs_ty_1: RawTy<S>,
        elim: RawStuck<S>,
    },
    SumEqLhsInjective {
        lhs_name_0: RawName<S>,
        lhs_name_1: RawName<S>,
        lhs_ty_0: RawTy<S>,
        lhs_ty_1: RawTy<S>,
        rhs_ty_0: RawTy<S>,
        rhs_ty_1: RawTy<S>,
        elim: RawStuck<S>,
    },
    SumEqRhsInjective {
        lhs_name_0: RawName<S>,
        lhs_name_1: RawName<S>,
        lhs_ty_0: RawTy<S>,
        lhs_ty_1: RawTy<S>,
        rhs_ty_0: RawTy<S>,
        rhs_ty_1: RawTy<S>,
        elim: RawStuck<S>,
    },

    SigmaEqNameInjective {
        head_name_0: RawName<S>,
        head_name_1: RawName<S>,
        tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    SigmaEqHeadInjective {
        head_name_0: RawName<S>,
        head_name_1: RawName<S>,
        tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    SigmaEqTailInjective {
        head_name: RawName<S>,
        tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },

    PiEqNameInjective {
        arg_name_0: RawName<S>,
        arg_name_1: RawName<S>,
        res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    PiEqArgInjective {
        arg_name_0: RawName<S>,
        arg_name_1: RawName<S>,
        res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawStuck<S>,
    },
    PiEqResInjective {
        arg_name: RawName<S>,
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
        if let RawTyKind::Never = motive.weak.inner.weak.get_clone() {
            return elim;
        }

        let usages = Usages::merge_mut([
            &mut elim.usages,
            &mut motive.usages,
        ]);

        let weak = Intern::new(RawStuckKind::Explode { elim, motive });
        Weaken { usages, weak }
    }

    pub(crate) fn case(
        mut lhs_name: RawName<S>,
        mut elim: RawStuck<S>,
        mut motive: RawScope<S, Intern<RawTyKind<S>>>,
        mut lhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
        mut rhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
    ) -> RawStuck<S> {
        if let Some(var_index) = lhs_inhab.weak.inner.usages.len().checked_sub(1)
        && lhs_inhab.weak.inner.usages.is_single(var_index)
        && let Some(var_index) = rhs_inhab.weak.inner.usages.len().checked_sub(1)
        && rhs_inhab.weak.inner.usages.is_single(var_index)
        && let RawTmKind::InjLhs { lhs_term } = lhs_inhab.weak.inner.weak.get_clone()
        && let RawTmKind::Stuck { stuck } = lhs_term.weak.get_clone()
        && let RawStuckKind::Var = stuck.weak.get_clone()
        && let RawTmKind::InjRhs { rhs_term } = rhs_inhab.weak.inner.weak.get_clone()
        && let RawTmKind::Stuck { stuck } = rhs_term.weak.get_clone()
        && let RawStuckKind::Var = stuck.weak.get_clone()
        && let RawTyKind::Sum {
            lhs_name: motive_lhs_name, lhs_ty, rhs_ty,
        } = motive.weak.inner.weak.get_clone()
        && motive_lhs_name == lhs_name
        && {
            let mut motive_lhs_ty = lhs_ty.unfilter(&motive.weak.inner.usages);
            let var_used = motive_lhs_ty.usages.pop();
            !var_used && {
                motive_lhs_ty.unfilter(&motive.usages) == lhs_inhab.var_ty_unfiltered()
            }
        }
        && {
            let mut motive_rhs_ty = rhs_ty.unfilter(&motive.weak.inner.usages);
            let var_used = motive_rhs_ty.usages.pop();
            !var_used && {
                motive_rhs_ty.unfilter(&motive.usages) == rhs_inhab.var_ty_unfiltered()
            }
        }
        {
            return elim;
        }

        let usages = Usages::merge_mut([
            &mut lhs_name.usages,
            &mut elim.usages,
            &mut motive.usages,
            &mut lhs_inhab.usages,
            &mut rhs_inhab.usages,
        ]);

        let weak = Intern::new(RawStuckKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab });
        Weaken { usages, weak }
    }

    pub(crate) fn proj_head(
        mut head_name: RawName<S>,
        mut tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut head_name.usages,
            &mut tail_ty.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::ProjHead { head_name, tail_ty, elim });
        Weaken { usages, weak }
    }

    pub(crate) fn proj_tail(
        mut head_name: RawName<S>,
        mut tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut head_name.usages,
            &mut tail_ty.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::ProjTail { head_name, tail_ty, elim });
        Weaken { usages, weak }
    }

    pub(crate) fn app(
        mut arg_name: RawName<S>,
        mut res_ty: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
        mut arg_term: RawTm<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut arg_name.usages,
            &mut res_ty.usages,
            &mut elim.usages,
            &mut arg_term.usages,
        ]);

        let weak = Intern::new(RawStuckKind::App { arg_name, res_ty ,elim, arg_term });
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
                    let succ_inhab_inner = {
                        succ_inhab
                        .inner_unfiltered_with_var()
                        .inner_unfiltered_with_var()
                        .weaken(1)
                    };

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

            RawStuckKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                debug_assert!(matches!(motive.weak.inner.weak.get_clone(), RawTyKind::Universe));
                let inner_ctx_len = elim.usages.len();
                let lhs_inhab_term = lhs_inhab.unique_eta_term_opt(ty_var_etas)?;
                let rhs_inhab_term = rhs_inhab.unique_eta_term_opt(ty_var_etas)?;
                let lhs_ty = lhs_inhab.var_ty_unfiltered();
                let rhs_ty = rhs_inhab.var_ty_unfiltered();

                let term = RawTm::stuck(
                    RawStuck::case(
                        lhs_name.clone(),
                        elim,
                        RawScope::new(
                            RawTy::sum(lhs_name.clone(), lhs_ty, rhs_ty),
                            RawTy::stuck(
                                RawStuck::case(
                                    lhs_name.clone_weaken(1),
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

            RawStuckKind::TagsApart { .. } => None,
            RawStuckKind::EqualEqEqTyInjective { .. } => None,
            RawStuckKind::EqualEqEqTerm0Injective { .. } => None,
            RawStuckKind::EqualEqEqTerm1Injective { .. } => None,
            RawStuckKind::SumEqNameInjective { .. } => None,
            RawStuckKind::SumEqLhsInjective { .. } => None,
            RawStuckKind::SumEqRhsInjective { .. } => None,
            RawStuckKind::SigmaEqNameInjective { .. } => None,
            RawStuckKind::SigmaEqHeadInjective { .. } => None,
            RawStuckKind::SigmaEqTailInjective { .. } => None,
            RawStuckKind::PiEqNameInjective { .. } => None,
            RawStuckKind::PiEqArgInjective { .. } => None,
            RawStuckKind::PiEqResInjective { .. } => None,
        }
    }

    pub(crate) fn tags_apart(
        tag_0: S::Tag,
        tag_1: S::Tag,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([&mut elim.usages]);

        let weak = Intern::new(RawStuckKind::TagsApart { tag_0, tag_1, elim });
        Weaken { usages, weak }
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
        mut eq_ty: RawTy<S>,
        mut eq_term_0_0: RawTm<S>,
        mut eq_term_0_1: RawTm<S>,
        mut eq_term_1_0: RawTm<S>,
        mut eq_term_1_1: RawTm<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut eq_ty.usages,
            &mut eq_term_0_0.usages,
            &mut eq_term_0_1.usages,
            &mut eq_term_1_0.usages,
            &mut eq_term_1_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::EqualEqEqTerm0Injective {
            eq_ty,
            eq_term_0_0, eq_term_0_1,
            eq_term_1_0, eq_term_1_1,
            elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn equal_eq_eq_term_1_injective(
        mut eq_ty: RawTy<S>,
        mut eq_term_0_0: RawTm<S>,
        mut eq_term_0_1: RawTm<S>,
        mut eq_term_1_0: RawTm<S>,
        mut eq_term_1_1: RawTm<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut eq_ty.usages,
            &mut eq_term_0_0.usages,
            &mut eq_term_0_1.usages,
            &mut eq_term_1_0.usages,
            &mut eq_term_1_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::EqualEqEqTerm1Injective {
            eq_ty,
            eq_term_0_0, eq_term_0_1,
            eq_term_1_0, eq_term_1_1,
            elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sum_eq_name_injective(
        mut lhs_name_0: RawName<S>,
        mut lhs_name_1: RawName<S>,
        mut lhs_ty_0: RawTy<S>,
        mut lhs_ty_1: RawTy<S>,
        mut rhs_ty_0: RawTy<S>,
        mut rhs_ty_1: RawTy<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut lhs_name_0.usages,
            &mut lhs_name_1.usages,
            &mut lhs_ty_0.usages,
            &mut lhs_ty_1.usages,
            &mut rhs_ty_0.usages,
            &mut rhs_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SumEqNameInjective {
            lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sum_eq_lhs_injective(
        mut lhs_name_0: RawName<S>,
        mut lhs_name_1: RawName<S>,
        mut lhs_ty_0: RawTy<S>,
        mut lhs_ty_1: RawTy<S>,
        mut rhs_ty_0: RawTy<S>,
        mut rhs_ty_1: RawTy<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut lhs_name_0.usages,
            &mut lhs_name_1.usages,
            &mut lhs_ty_0.usages,
            &mut lhs_ty_1.usages,
            &mut rhs_ty_0.usages,
            &mut rhs_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SumEqLhsInjective {
            lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sum_eq_rhs_injective(
        mut lhs_name_0: RawName<S>,
        mut lhs_name_1: RawName<S>,
        mut lhs_ty_0: RawTy<S>,
        mut lhs_ty_1: RawTy<S>,
        mut rhs_ty_0: RawTy<S>,
        mut rhs_ty_1: RawTy<S>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut lhs_name_0.usages,
            &mut lhs_name_1.usages,
            &mut lhs_ty_0.usages,
            &mut lhs_ty_1.usages,
            &mut rhs_ty_0.usages,
            &mut rhs_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SumEqRhsInjective {
            lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sigma_eq_name_injective(
        mut head_name_0: RawName<S>,
        mut head_name_1: RawName<S>,
        mut tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut head_name_0.usages,
            &mut head_name_1.usages,
            &mut tail_ty_0.usages,
            &mut tail_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SigmaEqNameInjective {
            head_name_0, head_name_1, tail_ty_0, tail_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sigma_eq_head_injective(
        mut head_name_0: RawName<S>,
        mut head_name_1: RawName<S>,
        mut tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut head_name_0.usages,
            &mut head_name_1.usages,
            &mut tail_ty_0.usages,
            &mut tail_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SigmaEqHeadInjective {
            head_name_0, head_name_1, tail_ty_0, tail_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn sigma_eq_tail_injective(
        mut head_name: RawName<S>,
        mut tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut head_name.usages,
            &mut tail_ty_0.usages,
            &mut tail_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::SigmaEqTailInjective {
            head_name, tail_ty_0, tail_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn pi_eq_name_injective(
        mut arg_name_0: RawName<S>,
        mut arg_name_1: RawName<S>,
        mut res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut arg_name_0.usages,
            &mut arg_name_1.usages,
            &mut res_ty_0.usages,
            &mut res_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::PiEqNameInjective {
            arg_name_0, arg_name_1, res_ty_0, res_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn pi_eq_arg_injective(
        mut arg_name_0: RawName<S>,
        mut arg_name_1: RawName<S>,
        mut res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut arg_name_0.usages,
            &mut arg_name_1.usages,
            &mut res_ty_0.usages,
            &mut res_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::PiEqArgInjective {
            arg_name_0, arg_name_1, res_ty_0, res_ty_1, elim,
        });
        Weaken { usages, weak }
    }

    pub(crate) fn pi_eq_res_injective(
        mut arg_name: RawName<S>,
        mut res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        mut res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        mut elim: RawStuck<S>,
    ) -> RawStuck<S> {
        let usages = Usages::merge_mut([
            &mut arg_name.usages,
            &mut res_ty_0.usages,
            &mut res_ty_1.usages,
            &mut elim.usages,
        ]);

        let weak = Intern::new(RawStuckKind::PiEqResInjective {
            arg_name, res_ty_0, res_ty_1, elim,
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
                lhs_name,
                elim,
                motive,
                lhs_inhab,
                rhs_inhab,
            } => {
                let RawTyKind::Stuck { stuck: ty_stuck } = ty.weak.get_clone() else {
                    return false;
                };
                let RawStuckKind::Case {
                    lhs_name: ty_lhs_name,
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

                lhs_name == ty_lhs_name
                && (
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
            RawStuckKind::TagsApart { .. } |
            RawStuckKind::EqualEqEqTyInjective { .. } |
            RawStuckKind::EqualEqEqTerm0Injective { .. } |
            RawStuckKind::EqualEqEqTerm1Injective { .. } |
            RawStuckKind::SumEqNameInjective { .. } |
            RawStuckKind::SumEqLhsInjective { .. } |
            RawStuckKind::SumEqRhsInjective { .. } |
            RawStuckKind::SigmaEqNameInjective { .. } |
            RawStuckKind::SigmaEqHeadInjective { .. } |
            RawStuckKind::SigmaEqTailInjective { .. } |
            RawStuckKind::PiEqNameInjective { .. } |
            RawStuckKind::PiEqArgInjective { .. } |
            RawStuckKind::PiEqResInjective { .. } => false,
        }
    }
}

impl<S: Scheme> RawStuckKind<S> {
    pub(crate) fn var() -> Intern<RawStuckKind<S>> {
        Intern::new(RawStuckKind::Var)
    }
}

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
        if let Some(term) = S::interner().check_stuck_subst_cache(*self, filter, &var_term) {
            return term;
        }

        let term = match self.get_clone() {
            RawStuckKind::Var => {
                var_term.clone_weaken(filter.len().strict_sub(1).strict_sub(var_term.usages.len()))
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

            RawStuckKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                let lhs_name = lhs_name.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let lhs_inhab = lhs_inhab.subst(filter, &var_term);
                let rhs_inhab = rhs_inhab.subst(filter, &var_term);
                RawTm::case(lhs_name, elim, motive, lhs_inhab, rhs_inhab)
            },

            RawStuckKind::ProjHead { head_name, tail_ty, elim } => {
                let head_name = head_name.subst(filter, &var_term);
                let tail_ty = tail_ty.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::proj_head(head_name, tail_ty, elim)
            },

            RawStuckKind::ProjTail { head_name, tail_ty, elim } => {
                let head_name = head_name.subst(filter, &var_term);
                let tail_ty = tail_ty.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::proj_tail(head_name, tail_ty, elim)
            },

            RawStuckKind::App { arg_name, res_ty, elim, arg_term } => {
                let arg_name = arg_name.subst(filter, &var_term);
                let res_ty = res_ty.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                let arg_term = arg_term.subst(filter, &var_term);
                RawTm::app(arg_name, res_ty, elim, arg_term)
            },

            RawStuckKind::TagsApart { tag_0, tag_1, elim } => {
                let elim = elim.subst(filter, &var_term);
                RawTm::tags_apart(tag_0, tag_1, elim)
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
                eq_ty,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                let eq_ty = eq_ty.subst(filter, &var_term);
                let eq_term_0_0 = eq_term_0_0.subst(filter, &var_term);
                let eq_term_0_1 = eq_term_0_1.subst(filter, &var_term);
                let eq_term_1_0 = eq_term_1_0.subst(filter, &var_term);
                let eq_term_1_1 = eq_term_1_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::equal_eq_eq_term_0_injective(
                    eq_ty,
                    eq_term_0_0,
                    eq_term_0_1,
                    eq_term_1_0,
                    eq_term_1_1,
                    elim,
                )
            },
            RawStuckKind::EqualEqEqTerm1Injective {
                eq_ty,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                let eq_ty = eq_ty.subst(filter, &var_term);
                let eq_term_0_0 = eq_term_0_0.subst(filter, &var_term);
                let eq_term_0_1 = eq_term_0_1.subst(filter, &var_term);
                let eq_term_1_0 = eq_term_1_0.subst(filter, &var_term);
                let eq_term_1_1 = eq_term_1_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::equal_eq_eq_term_1_injective(
                    eq_ty,
                    eq_term_0_0,
                    eq_term_0_1,
                    eq_term_1_0,
                    eq_term_1_1,
                    elim,
                )
            },

            RawStuckKind::SumEqNameInjective {
                lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
            } => {
                let lhs_name_0 = lhs_name_0.subst(filter, &var_term);
                let lhs_name_1 = lhs_name_1.subst(filter, &var_term);
                let lhs_ty_0 = lhs_ty_0.subst(filter, &var_term);
                let lhs_ty_1 = lhs_ty_1.subst(filter, &var_term);
                let rhs_ty_0 = rhs_ty_0.subst(filter, &var_term);
                let rhs_ty_1 = rhs_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sum_eq_name_injective(
                    lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
                )
            },

            RawStuckKind::SumEqLhsInjective {
                lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
            } => {
                let lhs_name_0 = lhs_name_0.subst(filter, &var_term);
                let lhs_name_1 = lhs_name_1.subst(filter, &var_term);
                let lhs_ty_0 = lhs_ty_0.subst(filter, &var_term);
                let lhs_ty_1 = lhs_ty_1.subst(filter, &var_term);
                let rhs_ty_0 = rhs_ty_0.subst(filter, &var_term);
                let rhs_ty_1 = rhs_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sum_eq_lhs_injective(
                    lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
                )
            },

            RawStuckKind::SumEqRhsInjective {
                lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
            } => {
                let lhs_name_0 = lhs_name_0.subst(filter, &var_term);
                let lhs_name_1 = lhs_name_1.subst(filter, &var_term);
                let lhs_ty_0 = lhs_ty_0.subst(filter, &var_term);
                let lhs_ty_1 = lhs_ty_1.subst(filter, &var_term);
                let rhs_ty_0 = rhs_ty_0.subst(filter, &var_term);
                let rhs_ty_1 = rhs_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sum_eq_rhs_injective(
                    lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
                )
            },

            RawStuckKind::SigmaEqNameInjective {
                head_name_0, head_name_1, tail_ty_0, tail_ty_1, elim,
            } => {
                let head_name_0 = head_name_0.subst(filter, &var_term);
                let head_name_1 = head_name_1.subst(filter, &var_term);
                let tail_ty_0 = tail_ty_0.subst(filter, &var_term);
                let tail_ty_1 = tail_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sigma_eq_name_injective(
                    head_name_0, head_name_1, tail_ty_0, tail_ty_1, elim,
                )
            },

            RawStuckKind::SigmaEqHeadInjective {
                head_name_0, head_name_1, tail_ty_0, tail_ty_1, elim,
            } => {
                let head_name_0 = head_name_0.subst(filter, &var_term);
                let head_name_1 = head_name_1.subst(filter, &var_term);
                let tail_ty_0 = tail_ty_0.subst(filter, &var_term);
                let tail_ty_1 = tail_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sigma_eq_head_injective(
                    head_name_0, head_name_1, tail_ty_0, tail_ty_1, elim,
                )
            },

            RawStuckKind::SigmaEqTailInjective {
                head_name,
                tail_ty_0,
                tail_ty_1,
                elim,
            } => {
                let head_name = head_name.subst(filter, &var_term);
                let tail_ty_0 = tail_ty_0.subst(filter, &var_term);
                let tail_ty_1 = tail_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::sigma_eq_tail_injective(
                    head_name,
                    tail_ty_0,
                    tail_ty_1,
                    elim,
                )
            },

            RawStuckKind::PiEqNameInjective {
                arg_name_0, arg_name_1, res_ty_0, res_ty_1, elim,
            } => {
                let arg_name_0 = arg_name_0.subst(filter, &var_term);
                let arg_name_1 = arg_name_1.subst(filter, &var_term);
                let res_ty_0 = res_ty_0.subst(filter, &var_term);
                let res_ty_1 = res_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::pi_eq_name_injective(
                    arg_name_0, arg_name_1, res_ty_0, res_ty_1, elim,
                )
            },

            RawStuckKind::PiEqArgInjective {
                arg_name_0, arg_name_1, res_ty_0, res_ty_1, elim,
            } => {
                let arg_name_0 = arg_name_0.subst(filter, &var_term);
                let arg_name_1 = arg_name_1.subst(filter, &var_term);
                let res_ty_0 = res_ty_0.subst(filter, &var_term);
                let res_ty_1 = res_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::pi_eq_arg_injective(
                    arg_name_0, arg_name_1, res_ty_0, res_ty_1, elim,
                )
            },

            RawStuckKind::PiEqResInjective {
                arg_name,
                res_ty_0,
                res_ty_1,
                elim,
            } => {
                let arg_name = arg_name.subst(filter, &var_term);
                let res_ty_0 = res_ty_0.subst(filter, &var_term);
                let res_ty_1 = res_ty_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                RawTm::pi_eq_res_injective(
                    arg_name,
                    res_ty_0,
                    res_ty_1,
                    elim,
                )
            },
        };

        S::interner().insert_stuck_subst_cache(*self, filter.clone(), var_term, term.clone());
        term
    }

    fn eliminates_var(&self, index: usize) -> bool {
        match self.get_clone() {
            RawStuckKind::Var => false,
            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                motive.eliminates_var(index) ||
                elim.eliminates_var(index) ||
                zero_inhab.eliminates_var(index) ||
                succ_inhab.eliminates_var(index)
            },
            RawStuckKind::Nat { nat } => nat.eliminates_var(index),
            RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                eq_term_0.eliminates_var(index) ||
                eq_term_1.eliminates_var(index) ||
                elim.eliminates_var(index) ||
                motive.eliminates_var(index) ||
                inhab.eliminates_var(index)
            },
            RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                eq_term.eliminates_var(index) ||
                elim.eliminates_var(index) ||
                motive.eliminates_var(index) ||
                inhab.eliminates_var(index)
            },
            RawStuckKind::Explode { elim, motive } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index) ||
                motive.eliminates_var(index)
            },
            RawStuckKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                lhs_name.eliminates_var(index) ||
                elim.eliminates_var(index) ||
                motive.eliminates_var(index) ||
                lhs_inhab.eliminates_var(index) ||
                rhs_inhab.eliminates_var(index)
            },
            RawStuckKind::ProjHead { head_name, tail_ty, elim } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                head_name.eliminates_var(index) ||
                tail_ty.eliminates_var(index) ||
                elim.eliminates_var(index)
            },
            RawStuckKind::ProjTail { head_name, tail_ty, elim } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                head_name.eliminates_var(index) ||
                tail_ty.eliminates_var(index) ||
                elim.eliminates_var(index)
            },
            RawStuckKind::App { arg_name, res_ty, elim, arg_term } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                arg_name.eliminates_var(index) ||
                res_ty.eliminates_var(index) ||
                elim.eliminates_var(index) ||
                arg_term.eliminates_var(index)
            },

            RawStuckKind::TagsApart { elim, .. } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::EqualEqEqTyInjective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                eq_ty_0.eliminates_var(index) ||
                eq_ty_1.eliminates_var(index) ||
                eq_term_0_0.eliminates_var(index) ||
                eq_term_0_1.eliminates_var(index) ||
                eq_term_1_0.eliminates_var(index) ||
                eq_term_1_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },
            RawStuckKind::EqualEqEqTerm0Injective {
                eq_ty,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                eq_ty.eliminates_var(index) ||
                eq_term_0_0.eliminates_var(index) ||
                eq_term_0_1.eliminates_var(index) ||
                eq_term_1_0.eliminates_var(index) ||
                eq_term_1_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },
            RawStuckKind::EqualEqEqTerm1Injective {
                eq_ty,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                eq_ty.eliminates_var(index) ||
                eq_term_0_0.eliminates_var(index) ||
                eq_term_0_1.eliminates_var(index) ||
                eq_term_1_0.eliminates_var(index) ||
                eq_term_1_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::SumEqNameInjective {
                lhs_name_0, lhs_name_1,
                lhs_ty_0, lhs_ty_1,
                rhs_ty_0, rhs_ty_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                lhs_name_0.eliminates_var(index) ||
                lhs_name_1.eliminates_var(index) ||
                lhs_ty_0.eliminates_var(index) ||
                lhs_ty_1.eliminates_var(index) ||
                rhs_ty_0.eliminates_var(index) ||
                rhs_ty_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::SumEqLhsInjective {
                lhs_name_0, lhs_name_1,
                lhs_ty_0, lhs_ty_1,
                rhs_ty_0, rhs_ty_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                lhs_name_0.eliminates_var(index) ||
                lhs_name_1.eliminates_var(index) ||
                lhs_ty_0.eliminates_var(index) ||
                lhs_ty_1.eliminates_var(index) ||
                rhs_ty_0.eliminates_var(index) ||
                rhs_ty_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::SumEqRhsInjective {
                lhs_name_0, lhs_name_1,
                lhs_ty_0, lhs_ty_1,
                rhs_ty_0, rhs_ty_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                lhs_name_0.eliminates_var(index) ||
                lhs_name_1.eliminates_var(index) ||
                lhs_ty_0.eliminates_var(index) ||
                lhs_ty_1.eliminates_var(index) ||
                rhs_ty_0.eliminates_var(index) ||
                rhs_ty_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::SigmaEqNameInjective {
                head_name_0, head_name_1,
                tail_ty_0, tail_ty_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                head_name_0.eliminates_var(index) ||
                head_name_1.eliminates_var(index) ||
                tail_ty_0.eliminates_var(index) ||
                tail_ty_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::SigmaEqHeadInjective {
                head_name_0, head_name_1,
                tail_ty_0, tail_ty_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                head_name_0.eliminates_var(index) ||
                head_name_1.eliminates_var(index) ||
                tail_ty_0.eliminates_var(index) ||
                tail_ty_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::SigmaEqTailInjective {
                head_name,
                tail_ty_0, tail_ty_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                head_name.eliminates_var(index) ||
                tail_ty_0.eliminates_var(index) ||
                tail_ty_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::PiEqNameInjective {
                arg_name_0, arg_name_1,
                res_ty_0, res_ty_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                arg_name_0.eliminates_var(index) ||
                arg_name_1.eliminates_var(index) ||
                res_ty_0.eliminates_var(index) ||
                res_ty_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::PiEqArgInjective {
                arg_name_0, arg_name_1,
                res_ty_0, res_ty_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                arg_name_0.eliminates_var(index) ||
                arg_name_1.eliminates_var(index) ||
                res_ty_0.eliminates_var(index) ||
                res_ty_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },

            RawStuckKind::PiEqResInjective {
                arg_name,
                res_ty_0, res_ty_1,
                elim,
            } => {
                elim.as_var().map_or(false, |var_index| var_index == index) ||
                arg_name.eliminates_var(index) ||
                res_ty_0.eliminates_var(index) ||
                res_ty_1.eliminates_var(index) ||
                elim.eliminates_var(index)
            },
        }
    }

    fn contains_subterm(&self, subterm: RawTm<S>) -> bool {
        match self.get_clone() {
            RawStuckKind::Var => false,
            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                motive.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm) ||
                zero_inhab.contains_subterm(&subterm) ||
                succ_inhab.contains_subterm(&subterm)
            },
            RawStuckKind::Nat { nat } => nat.contains_subterm(&subterm),
            RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
                eq_term_0.contains_subterm(&subterm) ||
                eq_term_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm) ||
                motive.contains_subterm(&subterm) ||
                inhab.contains_subterm(&subterm)
            },
            RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
                eq_term.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm) ||
                motive.contains_subterm(&subterm) ||
                inhab.contains_subterm(&subterm)
            },
            RawStuckKind::Explode { elim, motive } => {
                elim.contains_subterm(&subterm) ||
                motive.contains_subterm(&subterm)
            },
            RawStuckKind::Case { lhs_name, elim, motive, lhs_inhab, rhs_inhab } => {
                lhs_name.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm) ||
                motive.contains_subterm(&subterm) ||
                lhs_inhab.contains_subterm(&subterm) ||
                rhs_inhab.contains_subterm(&subterm)
            },
            RawStuckKind::ProjHead { head_name, tail_ty, elim } => {
                head_name.contains_subterm(&subterm) ||
                tail_ty.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },
            RawStuckKind::ProjTail { head_name, tail_ty, elim } => {
                head_name.contains_subterm(&subterm) ||
                tail_ty.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },
            RawStuckKind::App { arg_name, res_ty, elim, arg_term } => {
                arg_name.contains_subterm(&subterm) ||
                res_ty.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm) ||
                arg_term.contains_subterm(&subterm)
            },

            RawStuckKind::TagsApart { elim, .. } => {
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::EqualEqEqTyInjective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                eq_ty_0.contains_subterm(&subterm) ||
                eq_ty_1.contains_subterm(&subterm) ||
                eq_term_0_0.contains_subterm(&subterm) ||
                eq_term_0_1.contains_subterm(&subterm) ||
                eq_term_1_0.contains_subterm(&subterm) ||
                eq_term_1_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },
            RawStuckKind::EqualEqEqTerm0Injective {
                eq_ty,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                eq_ty.contains_subterm(&subterm) ||
                eq_term_0_0.contains_subterm(&subterm) ||
                eq_term_0_1.contains_subterm(&subterm) ||
                eq_term_1_0.contains_subterm(&subterm) ||
                eq_term_1_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },
            RawStuckKind::EqualEqEqTerm1Injective {
                eq_ty,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                eq_ty.contains_subterm(&subterm) ||
                eq_term_0_0.contains_subterm(&subterm) ||
                eq_term_0_1.contains_subterm(&subterm) ||
                eq_term_1_0.contains_subterm(&subterm) ||
                eq_term_1_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::SumEqNameInjective {
                lhs_name_0, lhs_name_1,
                lhs_ty_0, lhs_ty_1,
                rhs_ty_0, rhs_ty_1,
                elim,
            } => {
                lhs_name_0.contains_subterm(&subterm) ||
                lhs_name_1.contains_subterm(&subterm) ||
                lhs_ty_0.contains_subterm(&subterm) ||
                lhs_ty_1.contains_subterm(&subterm) ||
                rhs_ty_0.contains_subterm(&subterm) ||
                rhs_ty_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::SumEqLhsInjective {
                lhs_name_0, lhs_name_1,
                lhs_ty_0, lhs_ty_1,
                rhs_ty_0, rhs_ty_1,
                elim,
            } => {
                lhs_name_0.contains_subterm(&subterm) ||
                lhs_name_1.contains_subterm(&subterm) ||
                lhs_ty_0.contains_subterm(&subterm) ||
                lhs_ty_1.contains_subterm(&subterm) ||
                rhs_ty_0.contains_subterm(&subterm) ||
                rhs_ty_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::SumEqRhsInjective {
                lhs_name_0, lhs_name_1,
                lhs_ty_0, lhs_ty_1,
                rhs_ty_0, rhs_ty_1,
                elim,
            } => {
                lhs_name_0.contains_subterm(&subterm) ||
                lhs_name_1.contains_subterm(&subterm) ||
                lhs_ty_0.contains_subterm(&subterm) ||
                lhs_ty_1.contains_subterm(&subterm) ||
                rhs_ty_0.contains_subterm(&subterm) ||
                rhs_ty_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::SigmaEqNameInjective {
                head_name_0, head_name_1,
                tail_ty_0, tail_ty_1,
                elim,
            } => {
                head_name_0.contains_subterm(&subterm) ||
                head_name_1.contains_subterm(&subterm) ||
                tail_ty_0.contains_subterm(&subterm) ||
                tail_ty_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::SigmaEqHeadInjective {
                head_name_0, head_name_1,
                tail_ty_0, tail_ty_1,
                elim,
            } => {
                head_name_0.contains_subterm(&subterm) ||
                head_name_1.contains_subterm(&subterm) ||
                tail_ty_0.contains_subterm(&subterm) ||
                tail_ty_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::SigmaEqTailInjective {
                head_name,
                tail_ty_0, tail_ty_1,
                elim,
            } => {
                head_name.contains_subterm(&subterm) ||
                tail_ty_0.contains_subterm(&subterm) ||
                tail_ty_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::PiEqNameInjective {
                arg_name_0, arg_name_1,
                res_ty_0, res_ty_1,
                elim,
            } => {
                arg_name_0.contains_subterm(&subterm) ||
                arg_name_1.contains_subterm(&subterm) ||
                res_ty_0.contains_subterm(&subterm) ||
                res_ty_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::PiEqArgInjective {
                arg_name_0, arg_name_1,
                res_ty_0, res_ty_1,
                elim,
            } => {
                arg_name_0.contains_subterm(&subterm) ||
                arg_name_1.contains_subterm(&subterm) ||
                res_ty_0.contains_subterm(&subterm) ||
                res_ty_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },

            RawStuckKind::PiEqResInjective {
                arg_name,
                res_ty_0, res_ty_1,
                elim,
            } => {
                arg_name.contains_subterm(&subterm) ||
                res_ty_0.contains_subterm(&subterm) ||
                res_ty_1.contains_subterm(&subterm) ||
                elim.contains_subterm(&subterm)
            },
        }
    }
}

