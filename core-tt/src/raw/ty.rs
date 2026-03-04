use crate::priv_prelude::*;

pub type RawTy<S> = Weaken<Intern<RawTyKind<S>>>;

#[derive_where(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RawTyKind<S: Scheme> {
    Stuck {
        stuck: RawStuck<S>,
    },
    Name,
    Universe,
    Nat,
    Equal {
        eq_ty: RawTy<S>,
        eq_term_0: RawTm<S>,
        eq_term_1: RawTm<S>,
    },
    Never,
    Unit,
    Sum {
        lhs_name: RawName<S>,
        lhs_ty: RawTy<S>,
        rhs_ty: RawTy<S>,
    },
    Sigma {
        head_name: RawName<S>,
        tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
    },
    Pi {
        arg_name: RawName<S>,
        res_ty: RawScope<S, Intern<RawTyKind<S>>>,
    },
}

impl<S: Scheme> RawTy<S> {
    pub(crate) fn from_term(term: RawTm<S>) -> RawTy<S> {
        match term.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let stuck = stuck.clone_unfilter(&term.usages);
                RawTy::stuck(stuck)
            },
            RawTmKind::Type { ty } => {
                let ty = ty.clone_unfilter(&term.usages);
                ty
            },
            _ => {
                unreachable!()
            },
        }
    }

    pub(crate) fn stuck(mut stuck: RawStuck<S>) -> RawTy<S> {
        let usages = Usages::merge_mut([&mut stuck.usages]);

        let weak = Intern::new(RawTyKind::Stuck { stuck });
        Weaken { usages, weak }
    }

    pub(crate) fn name(ctx_len: usize) -> RawTy<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawTyKind::name(),
        }
    }

    pub(crate) fn universe(ctx_len: usize) -> RawTy<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawTyKind::universe(),
        }
    }

    pub(crate) fn nat(ctx_len: usize) -> RawTy<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawTyKind::nat(),
        }
    }

    pub(crate) fn equal(mut eq_ty: RawTy<S>, mut eq_term_0: RawTm<S>, mut eq_term_1: RawTm<S>) -> RawTy<S> {
        let usages = Usages::merge_mut([&mut eq_ty.usages, &mut eq_term_0.usages, &mut eq_term_1.usages]);
        let weak = Intern::new(RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 });
        Weaken { usages, weak }
    }

    pub(crate) fn never(ctx_len: usize) -> RawTy<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawTyKind::never(),
        }
    }

    pub(crate) fn unit(ctx_len: usize) -> RawTy<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawTyKind::unit(),
        }
    }

    pub(crate) fn sum(
        mut lhs_name: RawName<S>,
        mut lhs_ty: RawTy<S>, mut rhs_ty: RawTy<S>,
    ) -> RawTy<S> {
        let usages = Usages::merge_mut([&mut lhs_name.usages, &mut lhs_ty.usages, &mut rhs_ty.usages]);

        let weak = Intern::new(RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty });
        Weaken { usages, weak }
    }

    pub(crate) fn sigma(
        mut head_name: RawName<S>,
        mut tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
    ) -> RawTy<S> {
        let usages = Usages::merge_mut([&mut head_name.usages, &mut tail_ty.usages]);

        let weak = Intern::new(RawTyKind::Sigma { head_name, tail_ty });
        Weaken { usages, weak }
    }

    pub(crate) fn pi(
        mut arg_name: RawName<S>,
        mut res_ty: RawScope<S, Intern<RawTyKind<S>>>,
    ) -> RawTy<S> {
        let usages = Usages::merge_mut([&mut arg_name.usages, &mut res_ty.usages]);

        let weak = Intern::new(RawTyKind::Pi { arg_name, res_ty });
        Weaken { usages, weak }
    }

    pub(crate) fn unique_eta_term_opt(
        &self,
        ty_var_etas: &mut Vec<(usize, usize)>,
    ) -> Option<RawTm<S>> {
        match self.weak.get_clone() {
            RawTyKind::Stuck { stuck } => {
                let term = stuck.unique_eta_term_opt(ty_var_etas)?;
                Some(term.unfilter(&self.usages))
            },
            RawTyKind::Name => None,
            RawTyKind::Universe => None,
            RawTyKind::Nat => None,
            RawTyKind::Equal { .. } => None,
            RawTyKind::Never => None,
            RawTyKind::Unit => Some(RawTm::unit(self.usages.len())),
            RawTyKind::Sum { .. } => None,
            RawTyKind::Sigma { head_name, tail_ty } => {
                let head_term = {
                    tail_ty
                    .weak
                    .var_ty
                    .unique_eta_term_opt(ty_var_etas)?
                    .unfilter(&tail_ty.usages)
                    .unfilter(&self.usages)
                };
                let tail_term = {
                    let mut tail_term = tail_ty.weak.inner.unique_eta_term_opt(ty_var_etas)?;
                    assert!(!tail_term.usages.pop());

                    tail_term
                    .unfilter(&tail_ty.usages)
                    .unfilter(&self.usages)
                };
                let head_name = head_name.unfilter(&self.usages);
                Some(RawTm::pair(head_name, head_term, tail_term))
            },
            RawTyKind::Pi { arg_name, res_ty } => {
                let res_term = res_ty.unique_eta_term_opt(ty_var_etas)?.unfilter(&self.usages);
                let arg_name = arg_name.unfilter(&self.usages);
                Some(RawTm::func(arg_name, res_term))
            },
        }
    }

    /*
    pub(crate) fn heterogeneous_equal(
        eq_name_0: RawName<S>,
        eq_name_1: RawName<S>,
        eq_ty_0: RawTy<S>,
        eq_ty_1: RawTy<S>,
        tys_eq: RawTm<S>,
        eq_term_0: RawTm<S>,
        eq_term_1: RawTm<S>,
    ) -> RawTy<S> {
        debug_assert_eq!(tys_eq.usages.len(), eq_name_0.usages.len());
        debug_assert_eq!(tys_eq.usages.len(), eq_name_1.usages.len());
        debug_assert_eq!(tys_eq.usages.len(), eq_ty_0.usages.len());
        debug_assert_eq!(tys_eq.usages.len(), eq_ty_1.usages.len());
        debug_assert_eq!(tys_eq.usages.len(), eq_term_0.usages.len());
        debug_assert_eq!(tys_eq.usages.len(), eq_term_1.usages.len());

        let ctx_len = tys_eq.usages.len();

        RawTy::from_term(
            RawTm::app(
                eq_name_1.clone(),
                RawScope::new(
                    eq_ty_1.clone(),
                    RawTy::universe(ctx_len + 1),
                ),
                RawTm::app(
                    eq_name_0.clone(),
                    RawScope::new(
                        eq_ty_0.clone(),
                        RawTy::pi(
                            eq_name_1.clone_weaken(1),
                            RawScope::new(
                                eq_ty_1.clone_weaken(1),
                                RawTy::universe(ctx_len + 2),
                            ),
                        ),
                    ),
                    RawTm::cong(
                        RawTm::from_ty(eq_ty_0.clone()),
                        RawTm::from_ty(eq_ty_1.clone()),
                        tys_eq,
                        RawScope::new(
                            RawTy::universe(ctx_len),
                            RawScope::new(
                                RawTy::universe(ctx_len + 1),
                                RawScope::new(
                                    RawTy::equal(
                                        RawTy::universe(ctx_len + 2),
                                        RawTm::stuck(RawStuck::var(ctx_len + 2, ctx_len)),
                                        RawTm::stuck(RawStuck::var(ctx_len + 2, ctx_len + 1)),
                                    ),
                                    RawTy::pi(
                                        eq_name_0.clone_weaken(3),
                                        RawScope::new(
                                            RawTy::from_term(
                                                RawTm::stuck(RawStuck::var(ctx_len + 3, ctx_len)),
                                            ),
                                            RawTy::pi(
                                                eq_name_1.clone_weaken(4),
                                                RawScope::new(
                                                    RawTy::from_term(
                                                        RawTm::stuck(RawStuck::var(ctx_len + 4, ctx_len + 1)),
                                                    ),
                                                    RawTy::universe(ctx_len + 5),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                        RawScope::new(
                            RawTy::universe(ctx_len),
                            RawTm::func(
                                eq_name_0.clone_weaken(1),
                                RawScope::new(
                                    RawTy::from_term(
                                        RawTm::stuck(RawStuck::var(ctx_len + 1, ctx_len)),
                                    ),
                                    RawTm::func(
                                        eq_name_1.clone_weaken(2),
                                        RawScope::new(
                                            RawTy::from_term(
                                                RawTm::stuck(RawStuck::var(ctx_len + 2, ctx_len)),
                                            ),
                                            RawTm::from_ty(
                                                RawTy::equal(
                                                    RawTy::from_term(
                                                        RawTm::stuck(RawStuck::var(ctx_len + 3, ctx_len)),
                                                    ),
                                                    RawTm::stuck(RawStuck::var(ctx_len + 3, ctx_len + 1)),
                                                    RawTm::stuck(RawStuck::var(ctx_len + 3, ctx_len + 2)),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                    eq_term_0,
                ),
                eq_term_1,
            )
        )
    }
    */

    /*
    pub(crate) fn named_scoped_tys_congruence_ty(
        var_name_0: RawName<S>,
        var_name_1: RawName<S>,
        scoped_name_0: RawName<S>,
        scoped_name_1: RawName<S>,
        scoped_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        scoped_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        var_names_eq: RawTm<S>,
        var_tys_eq: RawTm<S>,
    ) -> RawTy<S> {
        debug_assert_eq!(var_tys_eq.usages.len(), var_name_0.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), var_name_1.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), scoped_name_0.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), scoped_name_1.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), scoped_ty_0.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), scoped_ty_1.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), var_names_eq.usages.len());
        let ctx_len = var_tys_eq.usages.len();


        /*
            This is the type:

            cong(
                elim = var_names_eq,
                Motive(var_name_0, var_name_1, var_names_eq) = Type,
                inhab(var_name) = scoped_tys_congruence_ty(
                    var_name,
                    scoped_name_0,
                    scoped_name_1,
                    scoped_ty_0,
                    scoped_ty_1,
                    var_tys_eq,
                ),
            )
        */

        RawTy::from_term(
            RawTm::cong(
                RawTm::from_name(var_name_0),
                RawTm::from_name(var_name_1),
                var_names_eq,
                RawScope::new(
                    RawTy::name(ctx_len),
                    RawScope::new(
                        RawTy::name(ctx_len + 1),
                        RawScope::new(
                            RawTy::equal(
                                RawTy::name(ctx_len + 2),
                                RawTm::stuck(RawStuck::var(ctx_len + 2, ctx_len)),
                                RawTm::stuck(RawStuck::var(ctx_len + 2, ctx_len + 1)),
                            ),
                            RawTy::universe(ctx_len + 3),
                        ),
                    ),
                ),
                RawScope::new(
                    RawTy::name(ctx_len),
                    RawTm::from_ty(
                        RawTy::scoped_tys_congruence_ty(
                            RawName::stuck(RawStuck::var(ctx_len + 1, ctx_len)),
                            scoped_name_0.clone_weaken(1),
                            scoped_name_1.clone_weaken(1),
                            scoped_ty_0.clone_weaken(1),
                            scoped_ty_1.clone_weaken(1),
                            var_tys_eq.clone_weaken(1),
                        ),
                    ),
                ),
            ),
        )
    }
    */

    /*
    pub(crate) fn scoped_tys_congruence_ty(
        var_name: RawName<S>,
        scoped_name_0: RawName<S>,
        scoped_name_1: RawName<S>,
        scoped_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        scoped_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        var_tys_eq: RawTm<S>,
    ) -> RawTy<S> {
        debug_assert_eq!(var_tys_eq.usages.len(), var_name.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), scoped_name_0.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), scoped_name_1.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), scoped_ty_0.usages.len());
        debug_assert_eq!(var_tys_eq.usages.len(), scoped_ty_1.usages.len());
        let ctx_len = var_tys_eq.usages.len();
        let var_ty_0 = scoped_ty_0.var_ty_unfiltered();
        let var_ty_1 = scoped_ty_1.var_ty_unfiltered();


        /*
            This is the type:

            cong(
                elim = var_tys_eq,
                Motive(VarTy0, VarTy1, var_tys_eq) = Fn(
                    ScopedTy0: Fn(val_0: VarTy0) -> Type,
                    ScopedTy1: Fn(val_1: VarTy1) -> Type,
                ) -> Type,
                inhab(VarTy, ScopedTy0, ScopedTy1) = ScopedTy0 == ScopedTy1,
                ScopedTy0,
                ScopedTy1,
            )
        */

        RawTy::from_term(
            RawTm::app(
                scoped_name_1.clone(),
                RawScope::new(
                    RawTy::pi(
                        var_name.clone(),
                        RawScope::new(
                            var_ty_1.clone(),
                            RawTy::universe(ctx_len + 1),
                        ),
                    ),
                    RawTy::universe(ctx_len + 1),
                ),
                RawTm::app(
                    scoped_name_0.clone(),
                    RawScope::new(
                        RawTy::pi(
                            var_name.clone(),
                            RawScope::new(
                                var_ty_0.clone(),
                                RawTy::universe(ctx_len + 1),
                            ),
                        ),
                        RawTy::pi(
                            scoped_name_1.clone_weaken(1),
                            RawScope::new(
                                RawTy::pi(
                                    var_name.clone_weaken(1),
                                    RawScope::new(
                                        var_ty_1.clone_weaken(1),
                                        RawTy::universe(ctx_len + 2),
                                    ),
                                ),
                                RawTy::universe(ctx_len + 2),
                            ),
                        ),
                    ),
                    RawTm::cong(
                        RawTm::from_ty(var_ty_0.clone()),
                        RawTm::from_ty(var_ty_1.clone()),
                        var_tys_eq,
                        RawScope::new(
                            RawTy::universe(ctx_len),
                            RawScope::new(
                                RawTy::universe(ctx_len + 1),
                                RawScope::new(
                                    RawTy::equal(
                                        RawTy::universe(ctx_len + 2),
                                        RawTm::stuck(RawStuck::var(ctx_len + 2, ctx_len)),
                                        RawTm::stuck(RawStuck::var(ctx_len + 2, ctx_len + 1)),
                                    ),
                                    RawTy::pi(
                                        scoped_name_0.clone_weaken(3),
                                        RawScope::new(
                                            RawTy::pi(
                                                var_name.clone_weaken(3),
                                                RawScope::new(
                                                    RawTy::from_term(
                                                        RawTm::stuck(RawStuck::var(ctx_len + 3, ctx_len)),
                                                    ),
                                                    RawTy::universe(ctx_len + 4),
                                                ),
                                            ),
                                            RawTy::pi(
                                                scoped_name_1.clone_weaken(4),
                                                RawScope::new(
                                                    RawTy::pi(
                                                        var_name.clone_weaken(4),
                                                        RawScope::new(
                                                            RawTy::from_term(
                                                                RawTm::stuck(RawStuck::var(ctx_len + 4, ctx_len + 1)),
                                                            ),
                                                            RawTy::universe(ctx_len + 5),
                                                        ),
                                                    ),
                                                    RawTy::universe(ctx_len + 5),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                        RawScope::new(
                            RawTy::universe(ctx_len),
                            RawTm::func(
                                scoped_name_0.clone_weaken(1),
                                RawScope::new(
                                    RawTy::pi(
                                        var_name.clone_weaken(1),
                                        RawScope::new(
                                            RawTy::from_term(
                                                RawTm::stuck(RawStuck::var(ctx_len + 1, ctx_len)),
                                            ),
                                            RawTy::universe(ctx_len + 2),
                                        ),
                                    ),
                                    RawTm::func(
                                        scoped_name_1.clone_weaken(2),
                                        RawScope::new(
                                            RawTy::pi(
                                                var_name.clone_weaken(2),
                                                RawScope::new(
                                                    RawTy::from_term(
                                                        RawTm::stuck(RawStuck::var(ctx_len + 2, ctx_len)),
                                                    ),
                                                    RawTy::universe(ctx_len + 3),
                                                ),
                                            ),
                                            RawTm::from_ty(
                                                RawTy::equal(
                                                    RawTy::pi(
                                                        var_name.clone_weaken(3),
                                                        RawScope::new(
                                                            RawTy::from_term(
                                                                RawTm::stuck(RawStuck::var(ctx_len + 3, ctx_len)),
                                                            ),
                                                            RawTy::universe(ctx_len + 4),
                                                        ),
                                                    ),
                                                    RawTm::stuck(RawStuck::var(ctx_len + 3, ctx_len + 1)),
                                                    RawTm::stuck(RawStuck::var(ctx_len + 3, ctx_len + 2)),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                    RawTm::func(
                        scoped_name_0.clone(),
                        RawScope::new(
                            var_ty_0.clone(),
                            RawTm::from_ty(scoped_ty_0.inner_unfiltered_with_var()),
                        ),
                    ),
                ),
                RawTm::func(
                    scoped_name_1.clone(),
                    RawScope::new(
                        var_ty_1.clone(),
                        RawTm::from_ty(scoped_ty_1.inner_unfiltered_with_var()),
                    ),
                ),
            ),
        )
    }
    */
}

impl<S: Scheme> RawTyKind<S> {
    pub(crate) fn name() -> Intern<RawTyKind<S>> {
        Intern::new(RawTyKind::Name)
    }

    pub(crate) fn universe() -> Intern<RawTyKind<S>> {
        Intern::new(RawTyKind::Universe)
    }

    pub(crate) fn nat() -> Intern<RawTyKind<S>> {
        Intern::new(RawTyKind::Nat)
    }

    pub(crate) fn never() -> Intern<RawTyKind<S>> {
        Intern::new(RawTyKind::Never)
    }

    pub(crate) fn unit() -> Intern<RawTyKind<S>> {
        Intern::new(RawTyKind::Unit)
    }
}

impl<S: Scheme> Substitute<S> for Intern<RawTyKind<S>> {
    type RawSubstOutput = Intern<RawTyKind<S>>;

    fn to_subst_output(&self, _num_usages: usize) -> Intern<RawTyKind<S>> {
        self.clone()
    }

    fn subst(&self, filter: &Usages, var_term: RawTm<S>) -> RawTy<S> {
        match self.get_clone() {
            RawTyKind::Stuck { stuck } => {
                let stuck = stuck.subst(filter, &var_term);
                RawTy::from_term(stuck)
            },
            RawTyKind::Name => RawTy::name(filter.len()),
            RawTyKind::Universe => RawTy::universe(filter.len()),
            RawTyKind::Nat => RawTy::nat(filter.len()),
            RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } => {
                let eq_ty = eq_ty.subst(filter, &var_term);
                let eq_term_0 = eq_term_0.subst(filter, &var_term);
                let eq_term_1 = eq_term_1.subst(filter, &var_term);
                RawTy::equal(eq_ty, eq_term_0, eq_term_1)
            },
            RawTyKind::Never => RawTy::never(filter.len()),
            RawTyKind::Unit => RawTy::unit(filter.len()),
            RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_name = lhs_name.subst(filter, &var_term);
                let lhs_ty = lhs_ty.subst(filter, &var_term);
                let rhs_ty = rhs_ty.subst(filter, &var_term);
                RawTy::sum(lhs_name, lhs_ty, rhs_ty)
            },
            RawTyKind::Sigma { head_name, tail_ty } => {
                let head_name = head_name.subst(filter, &var_term);
                let tail_ty = tail_ty.subst(filter, &var_term);
                RawTy::sigma(head_name, tail_ty)
            },
            RawTyKind::Pi { arg_name, res_ty } => {
                let arg_name = arg_name.subst(filter, &var_term);
                let res_ty = res_ty.subst(filter, &var_term);
                RawTy::pi(arg_name, res_ty)
            },
        }
    }

    fn eliminates_var(&self, index: usize) -> bool {
        match self.get_clone() {
            RawTyKind::Stuck { stuck } => stuck.eliminates_var(index),
            RawTyKind::Name => false,
            RawTyKind::Universe => false,
            RawTyKind::Nat => false,
            RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } => {
                eq_ty.eliminates_var(index) ||
                eq_term_0.eliminates_var(index) ||
                eq_term_1.eliminates_var(index)
            },
            RawTyKind::Never => false,
            RawTyKind::Unit => false,
            RawTyKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                lhs_ty.eliminates_var(index) ||
                rhs_ty.eliminates_var(index)
            },
            RawTyKind::Sigma { head_name, tail_ty } => {
                head_name.eliminates_var(index) ||
                tail_ty.eliminates_var(index)
            },
            RawTyKind::Pi { arg_name, res_ty } => {
                arg_name.eliminates_var(index) ||
                res_ty.eliminates_var(index)
            },
        }
    }

    fn contains_subterm(&self, subterm: RawTm<S>) -> bool {
        match self.get_clone() {
            RawTyKind::Stuck { stuck } => {
                stuck.contains_subterm(&subterm)
            },
            RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } => {
                eq_ty.contains_subterm(&subterm) ||
                eq_term_0.contains_subterm(&subterm) ||
                eq_term_1.contains_subterm(&subterm)
            },
            RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                lhs_name.contains_subterm(&subterm) ||
                lhs_ty.contains_subterm(&subterm) ||
                rhs_ty.contains_subterm(&subterm)
            },
            RawTyKind::Sigma { head_name, tail_ty } => {
                head_name.contains_subterm(&subterm) ||
                tail_ty.contains_subterm(&subterm)
            },
            RawTyKind::Pi { arg_name, res_ty } => {
                arg_name.contains_subterm(&subterm) ||
                res_ty.contains_subterm(&subterm)
            },
            RawTyKind::Name |
            RawTyKind::Universe |
            RawTyKind::Nat |
            RawTyKind::Never |
            RawTyKind::Unit => false,
        }
    }
}

