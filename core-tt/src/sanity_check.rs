#![allow(dead_code)]

use crate::priv_prelude::*;

pub(crate) trait SanityCheck<S: Scheme> {
    type Meta<'m>
        where S: 'm;

    fn sanity_check<'m>(&self, ctx_opt: Option<&Ctx<S>>, filter: &Usages, meta: Self::Meta<'m>);
}

impl<S: Scheme, T: SanityCheck<S>> SanityCheck<S> for Weaken<T> {
    type Meta<'m> = T::Meta<'m>
        where S: 'm;
    
    fn sanity_check<'m>(&self, ctx_opt: Option<&Ctx<S>>, filter: &Usages, meta: T::Meta<'m>) {
        if let Some(ctx) = ctx_opt {
            assert_eq!(filter.len(), ctx.len());
        }
        assert_eq!(filter.count_ones(), self.usages.len());
        let mut filter = filter.clone();
        filter.zero_unused(&self.usages);
        self.weak.sanity_check(ctx_opt, &filter, meta);
    }
}

impl<S: Scheme> SanityCheck<S> for Intern<RawTyKind<S>> {
    type Meta<'m> = ()
        where S: 'm;

    fn sanity_check(&self, ctx_opt: Option<&Ctx<S>>, filter: &Usages, (): ()) {
        if let Some(ctx) = ctx_opt {
            assert_eq!(filter.len(), ctx.len());
        }
        match self.get_clone() {
            RawTyKind::Stuck { stuck } => {
                let ty_filter = Usages::zeros(filter.len());
                let stuck_ty = RawTy::universe(0);
                Usages::assert_or_to_ones([&stuck.usages]);
                stuck.sanity_check(ctx_opt, filter, (&ty_filter, &stuck_ty));
            },
            RawTyKind::User { .. } => {
                assert!(filter.is_zeros());
            },
            RawTyKind::Universe => {
                assert!(filter.is_zeros());
            },
            RawTyKind::Nat => {
                assert!(filter.is_zeros());
            },
            RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } => {
                Usages::assert_or_to_ones([&eq_ty.usages, &eq_term_0.usages, &eq_term_1.usages]);
                eq_ty.sanity_check(ctx_opt, filter, ());
                eq_term_0.sanity_check(ctx_opt, filter, (filter, &eq_ty));
                eq_term_1.sanity_check(ctx_opt, filter, (filter, &eq_ty));
            },
            RawTyKind::Never => {
                assert!(filter.is_zeros());
            },
            RawTyKind::Unit => {
                assert!(filter.is_zeros());
            },
            RawTyKind::Sum { lhs_ty, rhs_ty } => {
                Usages::assert_or_to_ones([&lhs_ty.usages, &rhs_ty.usages]);
                lhs_ty.sanity_check(ctx_opt, filter, ());
                rhs_ty.sanity_check(ctx_opt, filter, ());
            },
            RawTyKind::Sigma { tail_ty } => {
                Usages::assert_or_to_ones([&tail_ty.usages]);
                tail_ty.sanity_check(ctx_opt, filter, (None, ()));
            },
            RawTyKind::Pi { res_ty } => {
                Usages::assert_or_to_ones([&res_ty.usages]);
                res_ty.sanity_check(ctx_opt, filter, (None, ()));
            },
        }
    }
}

impl<S: Scheme> SanityCheck<S> for Intern<RawTmKind<S>> {
    type Meta<'m> = (&'m Usages, &'m RawTy<S>)
        where S: 'm;

    fn sanity_check<'m>(
        &self,
        ctx_opt: Option<&Ctx<S>>,
        filter: &Usages,
        (ty_filter, raw_ty): (&'m Usages, &'m RawTy<S>),
    ) {
        if let Some(ctx) = ctx_opt {
            assert_eq!(filter.len(), ctx.len());
        }
        match self.get_clone() {
            RawTmKind::Stuck { stuck } => {
                Usages::assert_or_to_ones([&stuck.usages]);
                stuck.sanity_check(ctx_opt, filter, (ty_filter, raw_ty));
            },
            RawTmKind::User { user_term } => {
                assert!(filter.is_zeros());
                let RawTyKind::User { user_ty } = raw_ty.weak.get_clone() else { panic!() };
                assert_eq!(user_ty, S::user_ty_of(&user_term));
            },
            RawTmKind::Type { ty } => {
                Usages::assert_or_to_ones([&ty.usages]);
                let RawTyKind::Universe = raw_ty.weak.get_clone() else { panic!() };
                ty.sanity_check(ctx_opt, filter, ());
            },
            RawTmKind::Zero => {
                assert!(filter.is_zeros());
                let RawTyKind::Nat = raw_ty.weak.get_clone() else { panic!() };
            },
            RawTmKind::Succs { count: _, pred_term } => {
                Usages::assert_or_to_ones([&pred_term.usages]);
                let RawTyKind::Nat = raw_ty.weak.get_clone() else { panic!() };
                pred_term.sanity_check(ctx_opt, filter, (ty_filter, raw_ty));
            },
            RawTmKind::Refl => {
                assert!(filter.is_zeros());
                let RawTyKind::Equal {
                    eq_ty: _,
                    eq_term_0,
                    eq_term_1,
                } = raw_ty.weak.get_clone() else { panic!() };
                assert_eq!(eq_term_0, eq_term_1);
            },
            RawTmKind::Unit => {
                assert!(filter.is_zeros());
                let RawTyKind::Unit = raw_ty.weak.get_clone() else { panic!() };
            },
            RawTmKind::InjLhs { lhs_term } => {
                Usages::assert_or_to_ones([&lhs_term.usages]);
                let RawTyKind::Sum {
                    lhs_ty,
                    rhs_ty: _,
                } = raw_ty.weak.get_clone() else { panic!() };
                let mut ty_filter = ty_filter.clone();
                ty_filter.zero_unused(&raw_ty.usages);
                lhs_term.sanity_check(ctx_opt, filter, (&ty_filter, &lhs_ty));
            },
            RawTmKind::InjRhs { rhs_term } => {
                Usages::assert_or_to_ones([&rhs_term.usages]);
                let RawTyKind::Sum {
                    lhs_ty: _,
                    rhs_ty,
                } = raw_ty.weak.get_clone() else { panic!() };
                let mut ty_filter = ty_filter.clone();
                ty_filter.zero_unused(&raw_ty.usages);
                rhs_term.sanity_check(ctx_opt, filter, (&ty_filter, &rhs_ty));
            },
            RawTmKind::Pair { head_term, tail_term } => {
                Usages::assert_or_to_ones([&head_term.usages, &tail_term.usages]);
                let RawTyKind::Sigma { tail_ty } = raw_ty.weak.get_clone() else { panic!() };
                let mut head_ty_filter = ty_filter.clone();
                head_ty_filter.zero_unused(&raw_ty.usages);
                head_ty_filter.zero_unused(&tail_ty.usages);
                head_term.sanity_check(ctx_opt, filter, (&head_ty_filter, &tail_ty.weak.var_ty));
                let bound_tail_ty = {
                    tail_ty
                    .clone_unfilter(&raw_ty.usages)
                    .unfilter(&ty_filter)
                    .bind(&head_term.clone_unfilter(filter))
                };
                let tail_ty_filter = Usages::ones(filter.len());
                tail_term.sanity_check(ctx_opt, filter, (&tail_ty_filter, &bound_tail_ty));
            },
            RawTmKind::Func { res_term } => {
                Usages::assert_or_to_ones([&res_term.usages]);
                let RawTyKind::Pi { res_ty } = raw_ty.weak.get_clone() else { panic!() };
                let mut ty_filter = ty_filter.clone();
                ty_filter.zero_unused(&raw_ty.usages);
                ty_filter.zero_unused(&res_ty.usages);
                let arg_ty_filter = ty_filter.clone();
                ty_filter.push(true);
                res_term.sanity_check(
                    ctx_opt,
                    filter,
                    (Some((&arg_ty_filter, &res_ty.weak.var_ty)), (&ty_filter, &res_ty.weak.inner)),
                );
            },
        }
    }
}

impl<S: Scheme> SanityCheck<S> for Intern<RawStuckKind<S>> {
    type Meta<'m> = (&'m Usages, &'m RawTy<S>)
        where S: 'm;

    fn sanity_check<'m>(
        &self,
        ctx_opt: Option<&Ctx<S>>,
        filter: &Usages, (ty_filter, raw_ty): (&'m Usages, &'m RawTy<S>),
    ) {
        if let Some(ctx) = ctx_opt {
            assert_eq!(filter.len(), ctx.len());
        }
        assert!(raw_ty.unique_eta_term_opt(&mut Vec::new()).is_none());
        match self.get_clone() {
            RawStuckKind::Var => {
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                if let Some(ctx) = ctx_opt {
                    let index = filter.index_of_single_one().unwrap();
                    let actual_ty = ctx.get_raw_ty(index);
                    let actual_ty = actual_ty.clone_weaken(ctx.len() - index);
                    assert_eq!(actual_ty, expected_ty);
                }
                assert!(expected_ty.unique_eta_term_opt(&mut Vec::new()).is_none());
            },

            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                Usages::assert_or_to_ones([&elim.usages, &motive.usages, &zero_inhab.usages, &succ_inhab.usages]);
                let nat_ty_filter = Usages::zeros(filter.len());
                let nat_ty = RawTy::nat(0);
                elim.sanity_check(ctx_opt, filter, (&nat_ty_filter, &nat_ty));
                
                motive.sanity_check(
                    ctx_opt,
                    filter,
                    (
                        Some((&nat_ty_filter, &nat_ty)),
                        (),
                    )
                );

                let zero_inhab_ty = {
                    motive
                    .clone()
                    .bind(&RawTm::zero(motive.usages.len()))
                };
                zero_inhab.sanity_check(ctx_opt, filter, (filter, &zero_inhab_ty));

                let succ_inhab_ty = {
                    let mut motive_weak = motive.clone();
                    motive_weak.weaken(2);
                    motive_weak
                    .bind(
                        &RawTm::succs(
                            NonZeroBigUint::one(),
                            RawTm::var(motive.usages.len() + 2, motive.usages.len(), &RawTy::nat(motive.usages.len())),
                        ),
                    )
                };

                let succ_inhab_ty_filter = Usages::ones(filter.len() + 2);
                let mut state_filter = filter.clone();
                state_filter.zero_unused(&motive.usages);
                state_filter.push(true);
                succ_inhab.sanity_check(
                    ctx_opt,
                    filter,
                    (
                        Some((&nat_ty_filter, &nat_ty)),
                        (
                            Some((&state_filter, &motive.weak.inner)),
                            (&succ_inhab_ty_filter, &succ_inhab_ty),
                        ),
                    ),
                );

                let actual_ty = {
                    motive
                    .clone()
                    .bind(&RawTm::stuck(elim.clone()))
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::Nat { nat } => {
                Usages::assert_or_to_ones([&nat.usages]);
                nat.sanity_check(ctx_opt, filter);
                assert!(matches!(raw_ty.weak.get_clone(), RawTyKind::Nat));
            },

            RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
                Usages::assert_or_to_ones([
                    &eq_term_0.usages, &eq_term_1.usages, &elim.usages, &motive.usages, &inhab.usages,
                ]);

                let eq_ty = inhab.var_ty_unfiltered();
                eq_term_0.sanity_check(ctx_opt, filter, (filter, &eq_ty));
                eq_term_1.sanity_check(ctx_opt, filter, (filter, &eq_ty));

                let elim_ty = RawTy::equal(eq_ty.clone(), eq_term_0.clone(), eq_term_1.clone());
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let mut motive_filter_1 = filter.clone();
                motive_filter_1.push(false);
                let mut motive_filter_2 = filter.clone();
                motive_filter_2.extend([true, true]);
                let motive_elim_ty = {
                    let eq_ty_weak_1 = eq_ty.clone_weaken(1);
                    let eq_ty_weak_2 = eq_ty.clone_weaken(2);
                    let var_term_0 = RawTm::var(motive.usages.len() + 2, motive.usages.len(), &eq_ty);
                    let var_term_1 = RawTm::var(motive.usages.len() + 2, motive.usages.len() + 1, &eq_ty_weak_1);
                    RawTy::equal(eq_ty_weak_2, var_term_0, var_term_1)
                };
                motive.sanity_check(
                    ctx_opt,
                    filter,
                    (
                        Some((filter, &eq_ty)),
                        (
                            Some((&motive_filter_1, &eq_ty)),
                            (
                                Some((&motive_filter_2, &motive_elim_ty)),
                                (),
                            ),
                        ),
                    ),
                );

                let inhab_ty = {
                    let (inhab_ty, _) = motive.clone().into_inner();
                    inhab_ty
                    .bind(&RawTm::var(motive.usages.len() + 1, motive.usages.len(), &eq_ty))
                    .bind(&RawTm::refl(motive.usages.len() + 1))
                };
                let mut inhab_ty_filter = filter.clone();
                inhab_ty_filter.push(true);
                inhab.sanity_check(
                    ctx_opt,
                    filter,
                    (
                        Some((filter, &eq_ty)),
                        (&inhab_ty_filter, &inhab_ty),
                    ),
                );

                let actual_ty = {
                    motive
                    .clone()
                    .bind(&eq_term_0)
                    .bind(&eq_term_1)
                    .bind(&RawTm::stuck(elim.clone()))
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                if actual_ty != expected_ty {
                    if let Some(ctx) = ctx_opt {
                        let actual_ty = Ty {
                            raw_ctx: ctx.raw_ctx.clone(),
                            raw_ty: actual_ty,
                        };
                        let expected_ty = Ty {
                            raw_ctx: ctx.raw_ctx.clone(),
                            raw_ty: expected_ty,
                        };
                        println!("actual_ty == {:?}", actual_ty);
                        println!("expected_ty == {:?}", expected_ty);
                    }
                    panic!("type mismatch");
                }
            },

            RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
                Usages::assert_or_to_ones([
                    &eq_term.usages, &elim.usages, &motive.usages, &inhab.usages,
                ]);

                let eq_ty = inhab.var_ty_unfiltered();
                eq_term.sanity_check(ctx_opt, filter, (filter, &eq_ty));

                let elim_ty = RawTy::equal(eq_ty.clone(), eq_term.clone(), eq_term.clone());
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let mut motive_filter_1 = filter.clone();
                motive_filter_1.push(true);
                let motive_elim_ty = {
                    let eq_ty_weak = eq_ty.clone_weaken(1);
                    let var_term = RawTm::var(motive.usages.len() + 1, motive.usages.len(), &eq_ty);
                    RawTy::equal(eq_ty_weak, var_term.clone(), var_term)
                };
                motive.sanity_check(
                    ctx_opt,
                    filter,
                    (
                        Some((filter, &eq_ty)),
                        (
                            Some((&motive_filter_1, &motive_elim_ty)),
                            (),
                        ),
                    ),
                );

                let inhab_ty = {
                    let (inhab_ty, _) = motive.clone().into_inner();
                    inhab_ty
                    .bind(&RawTm::refl(motive.usages.len() + 1))
                };
                let mut inhab_ty_filter = filter.clone();
                inhab_ty_filter.push(true);
                inhab.sanity_check(
                    ctx_opt,
                    filter,
                    (
                        Some((filter, &eq_ty)),
                        (&inhab_ty_filter, &inhab_ty),
                    ),
                );

                let actual_ty = {
                    motive
                    .clone()
                    .bind(&eq_term)
                    .bind(&RawTm::stuck(elim.clone()))
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::Explode { elim, motive } => {
                Usages::assert_or_to_ones([&elim.usages, &motive.usages]);

                let nat_ty_filter = Usages::zeros(filter.len());
                let nat_ty = RawTy::nat(0);
                elim.sanity_check(ctx_opt, filter, (&nat_ty_filter, &nat_ty));
                motive.sanity_check(ctx_opt, filter, (Some((&nat_ty_filter, &nat_ty)), ()));

                let actual_ty = {
                    motive
                    .clone()
                    .bind(&RawTm::stuck(elim))
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                Usages::assert_or_to_ones([&elim.usages, &motive.usages, &lhs_inhab.usages, &rhs_inhab.usages]);
                let lhs_ty = lhs_inhab.var_ty_unfiltered();
                let rhs_ty = rhs_inhab.var_ty_unfiltered();
                let elim_ty = RawTy::sum(lhs_ty.clone(), rhs_ty.clone());
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                motive.sanity_check(
                    ctx_opt,
                    filter,
                    (Some((filter, &elim_ty)), ()),
                );

                let mut inhab_ty_filter = filter.clone();
                inhab_ty_filter.push(true);
                let lhs_inhab_ty = {
                    motive
                    .clone_weaken(1)
                    .bind(
                        &RawTm::inj_lhs(RawTm::var(motive.usages.len() + 1, motive.usages.len(), &lhs_ty)),
                    )
                };
                lhs_inhab.sanity_check(
                    ctx_opt,
                    filter,
                    (Some((&filter, &lhs_ty)), (&inhab_ty_filter, &lhs_inhab_ty)),
                );

                let rhs_inhab_ty = {
                    motive
                    .clone_weaken(1)
                    .bind(
                        &RawTm::inj_rhs(RawTm::var(motive.usages.len() + 1, motive.usages.len(), &rhs_ty)),
                    )
                };
                rhs_inhab.sanity_check(ctx_opt, filter, (Some((&filter, &rhs_ty)), (&inhab_ty_filter, &rhs_inhab_ty)));

                let actual_ty = {
                    motive
                    .clone()
                    .bind(&RawTm::stuck(elim.clone()))
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::ProjHead { elim, tail_ty } => {
                Usages::assert_or_to_ones([&elim.usages, &tail_ty.usages]);

                let elim_ty = RawTy::sigma(tail_ty.clone());
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));
                tail_ty.sanity_check(ctx_opt, filter, (None, ()));

                let actual_ty = {
                    tail_ty
                    .var_ty_unfiltered()
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::ProjTail { elim, tail_ty } => {
                Usages::assert_or_to_ones([&elim.usages, &tail_ty.usages]);

                let elim_ty = RawTy::sigma(tail_ty.clone());
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));
                tail_ty.sanity_check(ctx_opt, filter, (None, ()));

                let actual_ty = {
                    tail_ty
                    .clone()
                    .bind(&RawTm::proj_head(tail_ty.clone(), RawTm::stuck(elim.clone())))
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::App { res_ty, elim, arg_term } => {
                Usages::assert_or_to_ones([&res_ty.usages, &elim.usages, &arg_term.usages]);

                let elim_ty = RawTy::pi(res_ty.clone());
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let arg_ty = res_ty.var_ty_unfiltered();
                arg_term.sanity_check(ctx_opt, filter, (filter, &arg_ty));

                res_ty.sanity_check(ctx_opt, filter, (None, ()));

                let actual_ty = {
                    res_ty
                    .clone()
                    .bind(&arg_term)
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::EqualEqEqTyInjective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                Usages::assert_or_to_ones([
                    &eq_ty_0.usages,
                    &eq_ty_1.usages,
                    &eq_term_0_0.usages,
                    &eq_term_0_1.usages,
                    &eq_term_1_0.usages,
                    &eq_term_1_1.usages,
                    &elim.usages,
                ]);
                eq_ty_0.sanity_check(ctx_opt, filter, ());
                eq_ty_1.sanity_check(ctx_opt, filter, ());
                eq_term_0_0.sanity_check(ctx_opt, filter, (filter, &eq_ty_0));
                eq_term_1_0.sanity_check(ctx_opt, filter, (filter, &eq_ty_0));
                eq_term_0_1.sanity_check(ctx_opt, filter, (filter, &eq_ty_1));
                eq_term_1_1.sanity_check(ctx_opt, filter, (filter, &eq_ty_1));
                let elim_ty = RawTy::equal(
                    RawTy::universe(filter.count_ones()),
                    RawTm::from_ty(RawTy::equal(
                        eq_ty_0.clone(), eq_term_0_0.clone(), eq_term_1_0.clone(),
                    )),
                    RawTm::from_ty(RawTy::equal(
                        eq_ty_1.clone(), eq_term_0_1.clone(), eq_term_1_1.clone(),
                    )),
                );
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let actual_ty = {
                    RawTy::equal(
                        RawTy::universe(filter.count_ones()),
                        RawTm::from_ty(eq_ty_0),
                        RawTm::from_ty(eq_ty_1),
                    )
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::EqualEqEqTerm0Injective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                Usages::assert_or_to_ones([
                    &eq_ty_0.usages,
                    &eq_ty_1.usages,
                    &eq_term_0_0.usages,
                    &eq_term_0_1.usages,
                    &eq_term_1_0.usages,
                    &eq_term_1_1.usages,
                    &elim.usages,
                ]);
                eq_ty_0.sanity_check(ctx_opt, filter, ());
                eq_ty_1.sanity_check(ctx_opt, filter, ());
                eq_term_0_0.sanity_check(ctx_opt, filter, (filter, &eq_ty_0));
                eq_term_1_0.sanity_check(ctx_opt, filter, (filter, &eq_ty_0));
                eq_term_0_1.sanity_check(ctx_opt, filter, (filter, &eq_ty_1));
                eq_term_1_1.sanity_check(ctx_opt, filter, (filter, &eq_ty_1));
                let elim_ty = RawTy::equal(
                    RawTy::universe(filter.count_ones()),
                    RawTm::from_ty(RawTy::equal(
                        eq_ty_0.clone(), eq_term_0_0.clone(), eq_term_1_0.clone(),
                    )),
                    RawTm::from_ty(RawTy::equal(
                        eq_ty_1.clone(), eq_term_0_1.clone(), eq_term_1_1.clone(),
                    )),
                );
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let actual_ty = {
                    RawTy::heterogeneous_equal(
                        eq_ty_0.clone(),
                        eq_ty_1.clone(),
                        RawTm::equal_eq_eq_ty_injective(
                            eq_ty_0, eq_ty_1,
                            eq_term_0_0.clone(), eq_term_0_1.clone(),
                            eq_term_1_0, eq_term_1_1,
                            RawTm::stuck(elim),
                        ),
                        eq_term_0_0,
                        eq_term_0_1,
                    )
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::EqualEqEqTerm1Injective {
                eq_ty_0, eq_ty_1,
                eq_term_0_0, eq_term_0_1,
                eq_term_1_0, eq_term_1_1,
                elim,
            } => {
                Usages::assert_or_to_ones([
                    &eq_ty_0.usages,
                    &eq_ty_1.usages,
                    &eq_term_0_0.usages,
                    &eq_term_0_1.usages,
                    &eq_term_1_0.usages,
                    &eq_term_1_1.usages,
                    &elim.usages,
                ]);
                eq_ty_0.sanity_check(ctx_opt, filter, ());
                eq_ty_1.sanity_check(ctx_opt, filter, ());
                eq_term_0_0.sanity_check(ctx_opt, filter, (filter, &eq_ty_0));
                eq_term_1_0.sanity_check(ctx_opt, filter, (filter, &eq_ty_0));
                eq_term_0_1.sanity_check(ctx_opt, filter, (filter, &eq_ty_1));
                eq_term_1_1.sanity_check(ctx_opt, filter, (filter, &eq_ty_1));
                let elim_ty = RawTy::equal(
                    RawTy::universe(filter.count_ones()),
                    RawTm::from_ty(RawTy::equal(
                        eq_ty_0.clone(), eq_term_0_0.clone(), eq_term_1_0.clone(),
                    )),
                    RawTm::from_ty(RawTy::equal(
                        eq_ty_1.clone(), eq_term_0_1.clone(), eq_term_1_1.clone(),
                    )),
                );
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let actual_ty = {
                    RawTy::heterogeneous_equal(
                        eq_ty_0.clone(),
                        eq_ty_1.clone(),
                        RawTm::equal_eq_eq_ty_injective(
                            eq_ty_0, eq_ty_1,
                            eq_term_0_0, eq_term_0_1,
                            eq_term_1_0.clone(), eq_term_1_1.clone(),
                            RawTm::stuck(elim),
                        ),
                        eq_term_1_0,
                        eq_term_1_1,
                    )
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::SumEqLhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
                Usages::assert_or_to_ones([
                    &lhs_ty_0.usages, &lhs_ty_1.usages, &rhs_ty_0.usages, &rhs_ty_1.usages, &elim.usages,
                ]);
                lhs_ty_0.sanity_check(ctx_opt, filter, ());
                lhs_ty_1.sanity_check(ctx_opt, filter, ());
                rhs_ty_0.sanity_check(ctx_opt, filter, ());
                rhs_ty_1.sanity_check(ctx_opt, filter, ());
                let elim_ty = RawTy::equal(
                    RawTy::universe(filter.count_ones()),
                    RawTm::from_ty(RawTy::sum(lhs_ty_0.clone(), rhs_ty_0)),
                    RawTm::from_ty(RawTy::sum(lhs_ty_1.clone(), rhs_ty_1)),
                );
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let actual_ty = {
                    RawTy::equal(
                        RawTy::universe(filter.count_ones()),
                        RawTm::from_ty(lhs_ty_0),
                        RawTm::from_ty(lhs_ty_1),
                    )
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::SumEqRhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
                Usages::assert_or_to_ones([
                    &lhs_ty_0.usages, &lhs_ty_1.usages, &rhs_ty_0.usages, &rhs_ty_1.usages, &elim.usages,
                ]);
                lhs_ty_0.sanity_check(ctx_opt, filter, ());
                lhs_ty_1.sanity_check(ctx_opt, filter, ());
                rhs_ty_0.sanity_check(ctx_opt, filter, ());
                rhs_ty_1.sanity_check(ctx_opt, filter, ());
                let elim_ty = RawTy::equal(
                    RawTy::universe(filter.count_ones()),
                    RawTm::from_ty(RawTy::sum(lhs_ty_0, rhs_ty_0.clone())),
                    RawTm::from_ty(RawTy::sum(lhs_ty_1, rhs_ty_1.clone())),
                );
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let actual_ty = {
                    RawTy::equal(
                        RawTy::universe(filter.count_ones()),
                        RawTm::from_ty(rhs_ty_0),
                        RawTm::from_ty(rhs_ty_1),
                    )
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::SigmaEqHeadInjective { tail_ty_0, tail_ty_1, elim } => {
                Usages::assert_or_to_ones([
                    &tail_ty_0.usages, &tail_ty_1.usages, &elim.usages
                ]);

                tail_ty_0.sanity_check(ctx_opt, filter, (None, ()));
                tail_ty_1.sanity_check(ctx_opt, filter, (None, ()));

                let elim_ty = RawTy::equal(
                    RawTy::universe(filter.count_ones()),
                    RawTm::from_ty(RawTy::sigma(tail_ty_0.clone())),
                    RawTm::from_ty(RawTy::sigma(tail_ty_1.clone())),
                );
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let actual_ty = {
                    RawTy::equal(
                        RawTy::universe(filter.count_ones()),
                        RawTm::from_ty(tail_ty_0.var_ty_unfiltered()),
                        RawTm::from_ty(tail_ty_1.var_ty_unfiltered()),
                    )
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::SigmaEqTailInjective { tail_ty_0, tail_ty_1, elim } => {
                Usages::assert_or_to_ones([
                    &tail_ty_0.usages, &tail_ty_1.usages, &elim.usages
                ]);

                tail_ty_0.sanity_check(ctx_opt, filter, (None, ()));
                tail_ty_1.sanity_check(ctx_opt, filter, (None, ()));

                let elim_ty = RawTy::equal(
                    RawTy::universe(filter.count_ones()),
                    RawTm::from_ty(RawTy::sigma(tail_ty_0.clone())),
                    RawTm::from_ty(RawTy::sigma(tail_ty_1.clone())),
                );
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let actual_ty = {
                    RawTy::scoped_tys_congruence_ty(
                        tail_ty_0.clone(),
                        tail_ty_1.clone(),
                        RawTm::sigma_eq_head_injective(tail_ty_0, tail_ty_1, RawTm::stuck(elim)),
                    )
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::PiEqArgInjective { res_ty_0, res_ty_1, elim } => {
                Usages::assert_or_to_ones([
                    &res_ty_0.usages, &res_ty_1.usages, &elim.usages
                ]);

                res_ty_0.sanity_check(ctx_opt, filter, (None, ()));
                res_ty_1.sanity_check(ctx_opt, filter, (None, ()));

                let elim_ty = RawTy::equal(
                    RawTy::universe(filter.count_ones()),
                    RawTm::from_ty(RawTy::pi(res_ty_0.clone())),
                    RawTm::from_ty(RawTy::pi(res_ty_1.clone())),
                );
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let actual_ty = {
                    RawTy::equal(
                        RawTy::universe(filter.count_ones()),
                        RawTm::from_ty(res_ty_0.var_ty_unfiltered()),
                        RawTm::from_ty(res_ty_1.var_ty_unfiltered()),
                    )
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);

                assert_eq!(actual_ty, expected_ty);
            },

            RawStuckKind::PiEqResInjective { res_ty_0, res_ty_1, elim } => {
                Usages::assert_or_to_ones([
                    &res_ty_0.usages, &res_ty_1.usages, &elim.usages
                ]);

                res_ty_0.sanity_check(ctx_opt, filter, (None, ()));
                res_ty_1.sanity_check(ctx_opt, filter, (None, ()));

                let elim_ty = RawTy::equal(
                    RawTy::universe(filter.count_ones()),
                    RawTm::from_ty(RawTy::pi(res_ty_0.clone())),
                    RawTm::from_ty(RawTy::pi(res_ty_1.clone())),
                );
                elim.sanity_check(ctx_opt, filter, (filter, &elim_ty));

                let actual_ty = {
                    RawTy::scoped_tys_congruence_ty(
                        res_ty_0.clone(),
                        res_ty_1.clone(),
                        RawTm::pi_eq_arg_injective(res_ty_0, res_ty_1, RawTm::stuck(elim)),
                    )
                    .unfilter(filter)
                };
                let expected_ty = raw_ty.clone_unfilter(ty_filter);
                assert_eq!(actual_ty, expected_ty);
            },
        }
    }
}

impl<S: Scheme, T: SanityCheck<S>> SanityCheck<S> for RawScopeKind<S, T> {
    type Meta<'m> = (Option<(&'m Usages, &'m RawTy<S>)>, T::Meta<'m>)
        where S: 'm;

    fn sanity_check<'m>(
        &self,
        ctx_opt: Option<&Ctx<S>>,
        filter: &Usages,
        (var_filter_ty_opt, meta): (Option<(&'m Usages, &'m RawTy<S>)>, T::Meta<'m>),
    ) {
        if let Some(ctx) = ctx_opt {
            assert_eq!(filter.len(), ctx.len());
        }

        let mut inner_usages = self.inner.usages.clone();
        inner_usages.pop();
        Usages::assert_or_to_ones([
            &self.var_ty.usages,
            &inner_usages,
        ]);

        self.var_ty.sanity_check(ctx_opt, filter, ());

        if let Some((var_ty_filter, var_ty)) = var_filter_ty_opt {
            assert_eq!(
                var_ty.clone_unfilter(var_ty_filter),
                self.var_ty.clone_unfilter(filter),
            );
        }

        let sub_ctx;
        let ctx_opt = match ctx_opt {
            None => None,
            Some(ctx) => {
                sub_ctx = Ctx {
                    raw_ctx: ctx.raw_ctx.cons(
                        self.var_ty.clone_unfilter(&filter),
                    ),
                };
                Some(&sub_ctx)
            },
        };

        let mut filter = filter.clone();
        filter.push(true);
        self.inner.sanity_check(ctx_opt, &filter, meta);
    }
}

impl<S: Scheme> SanityCheck<S> for RawTypedKind<S, Intern<RawTmKind<S>>> {
    type Meta<'m> = ()
        where S: 'm;

    fn sanity_check<'m>(
        &self,
        ctx_opt: Option<&Ctx<S>>,
        filter: &Usages,
        (): (),
    ) {
        if let Some(ctx) = ctx_opt {
            assert_eq!(filter.len(), ctx.len());
        }
        self.raw_ty.sanity_check(ctx_opt, &filter, ());
        self.inner.sanity_check(ctx_opt, &filter, (&filter, &self.raw_ty));
    }
}

impl<S: Scheme> SanityCheck<S> for RawTypedKind<S, Intern<RawStuckKind<S>>> {
    type Meta<'m> = ()
        where S: 'm;

    fn sanity_check<'m>(
        &self,
        ctx_opt: Option<&Ctx<S>>,
        filter: &Usages,
        (): (),
    ) {
        if let Some(ctx) = ctx_opt {
            assert_eq!(filter.len(), ctx.len());
        }
        self.raw_ty.sanity_check(ctx_opt, &filter, ());
        self.inner.sanity_check(ctx_opt, &filter, (&filter, &self.raw_ty));
    }
}

impl<S: Scheme> RawNat<S> {
    pub(crate) fn sanity_check(&self, ctx_opt: Option<&Ctx<S>>, filter: &Usages) {
        let mut filter = filter.clone();
        filter.zero_unused(&self.usages);

        let mut usages = Usages::zeros(filter.count_ones());
        for term in self.iter_terms() {
            assert_eq!(term.usages.len(), usages.len());
            for index in 0..usages.len() {
                if term.usages[index] {
                    usages.set(index, true);
                }
            }
        }
        assert!(usages.iter().all(|bit| bit));

        self.max_all.sanity_check(ctx_opt, &filter);
    }
}

impl<S: Scheme> MaxAll<S> {
    pub(crate) fn sanity_check(&self, ctx_opt: Option<&Ctx<S>>, filter: &Usages) {
        for add_all in self.terms.iter() {
            add_all.sanity_check(ctx_opt, filter);
        }
    }
}

impl<S: Scheme> AddAll<S> {
    pub(crate) fn sanity_check(&self, ctx_opt: Option<&Ctx<S>>, filter: &Usages) {
        for mul_all in self.terms.keys() {
            mul_all.sanity_check(ctx_opt, filter);
        }
    }
}

impl<S: Scheme> MulAll<S> {
    pub(crate) fn sanity_check(&self, ctx_opt: Option<&Ctx<S>>, filter: &Usages) {
        let nat_ty_filter = Usages::zeros(filter.len());
        let nat_ty = RawTy::nat(0);
        for stuck in self.terms.keys() {
            stuck.sanity_check(ctx_opt, filter, (&nat_ty_filter, &nat_ty));
        }
    }
}

impl Usages {
    pub(crate) fn assert_or_to_ones<const LEN: usize>(usagess: [&Usages; LEN]) {
        let (first, rest) = usagess.split_first().unwrap();
        for usages in rest {
            assert_eq!(usages.len(), first.len());
        }
        for index in 0..first.len() {
            let mut bit = false;
            for usages in usagess {
                bit |= usages[index];
            }
            assert!(bit);
        }
    }
}

impl<S: Scheme> RawCtx<S> {
    pub(crate) fn sanity_check(&self, ctx_len: usize) {
        match &self.cons_opt {
            None => assert_eq!(ctx_len, 0),
            Some(cons) => {
                let ctx_len = ctx_len.strict_sub(1);
                cons.parent.sanity_check(ctx_len);
                let ctx = Ctx { raw_ctx: cons.parent.clone() };
                cons.var_ty.sanity_check(Some(&ctx), &Usages::ones(ctx_len), ());
            },
        }
    }
}

impl<S: Scheme> Ctx<S> {
    pub(crate) fn sanity_check(&self) {
        self.raw_ctx.sanity_check(self.len());
    }
}

impl<S: Scheme> Ty<S> {
    pub(crate) fn sanity_check(&self) {
        let ctx_len = self.raw_ty.usages.len();
        let ctx = Ctx { raw_ctx: self.raw_ctx.clone() };
        ctx.sanity_check();
        let filter = Usages::ones(ctx_len);
        self.raw_ty.sanity_check(Some(&ctx), &filter, ());
    }
}

impl<S: Scheme> Tm<S> {
    pub(crate) fn sanity_check(&self) {
        let ctx_len = self.raw_typed_term.usages.len();
        let ctx = Ctx { raw_ctx: self.raw_ctx.clone() };
        ctx.sanity_check();
        let filter = Usages::ones(ctx_len);
        self.raw_typed_term.sanity_check(Some(&ctx), &filter, ());
    }
}

impl<S: Scheme> Stuck<S> {
    pub(crate) fn sanity_check(&self) {
        let ctx_len = self.raw_typed_stuck.usages.len();
        let ctx = Ctx { raw_ctx: self.raw_ctx.clone() };
        ctx.sanity_check();
        let filter = Usages::ones(ctx_len);
        self.raw_typed_stuck.sanity_check(Some(&ctx), &filter, ());
    }
}

