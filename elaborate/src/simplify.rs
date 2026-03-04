use crate::priv_prelude::*;

#[extension(pub trait IsoSimplifyExt)]
impl Iso {
    fn simplify_output(
        &self,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {
        let (new_constraint_name, next_iso) = Iso::simplify_ty(
            &self.output_ty(), constraint_name, recursion_depth,
        );
        (new_constraint_name, self.transitivity(&next_iso))
    }

    fn simplify_ty(
        input_ty: &Ty,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {
        let (input_ty, constraint_name) = Ctx::into_common_ctx((input_ty, constraint_name));

        let Some(_recursion_depth) = recursion_depth.checked_sub(1) else {
            return (constraint_name, input_ty.iso_refl());
        };

        if let Some(unique_term) = input_ty.unique_term_opt() {
            let iso = Iso::uniquely_inhabited_ty_to_unit(&unique_term);
            return (constraint_name, iso);
        }

        let (new_constraint_name, iso) = match input_ty.kind() {
            TyKind::Name |
            TyKind::Universe |
            TyKind::Nat |
            TyKind::Never |
            TyKind::Unit => (constraint_name, input_ty.iso_refl()),

            TyKind::Stuck { stuck } => {
                Iso::simplify_stuck_ty(&stuck, &constraint_name, recursion_depth)
            },

            TyKind::Equal { eq_term_0, eq_term_1 } => {
                Iso::simplify_equality_ty(
                    &eq_term_0, &eq_term_1, &constraint_name, recursion_depth,
                )
            },

            TyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                Iso::simplify_sum_ty(
                    &lhs_name, &lhs_ty, &rhs_ty, &constraint_name, recursion_depth,
                )
            },

            TyKind::Sigma { head_name, tail_ty } => {
                Iso::simplify_sigma_ty(&head_name, &tail_ty, &constraint_name, recursion_depth)
            },

            TyKind::Pi { arg_name, res_ty } => {
                Iso::simplify_pi_ty(&arg_name, &res_ty, &constraint_name, recursion_depth)
            },
        };
        debug_assert_eq!(input_ty, iso.input_ty());
        (new_constraint_name, iso)
    }

    fn simplify_equality_ty(
        eq_term_0: &Tm,
        eq_term_1: &Tm,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {
        let (eq_term_0, eq_term_1, constraint_name) = Ctx::into_common_ctx((
            eq_term_0, eq_term_1, constraint_name,
        ));
        let input_ty = eq_term_0.equals(&eq_term_1);

        if let Some(eq_term) = as_equal(&eq_term_0, &eq_term_1) {
            let iso = Iso::reflexive_equality_to_unit(eq_term);
            return (constraint_name, iso);
        }

        match eq_term_0.ty().kind() {
            TyKind::Stuck { .. } => {
                // TODO
            },

            TyKind::Name => {
                if let TmKind::Tag { tag: tag_0 } = eq_term_0.kind()
                && let TmKind::Tag { tag: tag_1 } = eq_term_1.kind()
                {
                    debug_assert_ne!(tag_0, tag_1);
                    let iso = {
                        input_ty
                        .scope(|eq| eq.tags_apart())
                        .scope_never_to_iso_never()
                    };
                    return (constraint_name, iso);
                }
            },

            TyKind::Universe => {
                let ty_0 = eq_term_0.to_ty();
                let ty_1 = eq_term_1.to_ty();

                match (ty_0.kind(), ty_1.kind()) {
                    (
                        TyKind::Equal { eq_term_0: eq_term_0_0, eq_term_1: eq_term_1_0 },
                        TyKind::Equal { eq_term_0: eq_term_0_1, eq_term_1: eq_term_1_1 },
                    ) => {
                        return {
                            Iso::equality_of_equality_types(
                                &eq_term_0_0,
                                &eq_term_1_0,
                                &eq_term_0_1,
                                &eq_term_1_1,
                            )
                            .simplify_output(&constraint_name, recursion_depth)
                        };
                    },

                    (
                        TyKind::Sum { lhs_name: lhs_name_0, lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 },
                        TyKind::Sum { lhs_name: lhs_name_1, lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 },
                    ) => {
                        return {
                            Iso::equality_of_sum_types_to_equality_of_type_parameters(
                                &lhs_name_0, &lhs_name_1,
                                &lhs_ty_0, &lhs_ty_1,
                                &rhs_ty_0, &rhs_ty_1,
                            )
                            .simplify_output(&constraint_name, recursion_depth)
                        };
                    },

                    (
                        TyKind::Sigma { head_name: head_name_0, tail_ty: tail_ty_0 },
                        TyKind::Sigma { head_name: head_name_1, tail_ty: tail_ty_1 },
                    ) => {
                        return {
                            Iso::equality_of_sigma_types_to_equality_of_type_parameters(
                                &head_name_0,
                                &head_name_1,
                                &tail_ty_0.var_ty(),
                                &tail_ty_1.var_ty(),
                                tail_ty_0.unbind(),
                                tail_ty_1.unbind(),
                            )
                            .simplify_output(&constraint_name, recursion_depth)
                        };
                    },

                    (
                        TyKind::Pi { arg_name: arg_name_0, res_ty: res_ty_0 },
                        TyKind::Pi { arg_name: arg_name_1, res_ty: res_ty_1 },
                    ) => {
                        return {
                            Iso::equality_of_pi_types_to_equality_of_type_parameters(
                                &arg_name_0,
                                &arg_name_1,
                                &res_ty_0.var_ty(),
                                &res_ty_1.var_ty(),
                                res_ty_0.unbind(),
                                res_ty_1.unbind(),
                            )
                            .simplify_output(&constraint_name, recursion_depth)
                        };
                    },

                    _ => (),
                }

                if let Some(uninhabited_0) = ty_0.try_prove_uninhabited()
                && let Some(term_1) = ty_1.try_find_arbitrary_term()
                {
                    let iso = {
                        input_ty
                        .scope(|tys_eq| {
                            uninhabited_0.contradiction(&tys_eq.symmetry().transport(&term_1))
                        })
                        .scope_never_to_iso_never()
                    };
                    return (constraint_name, iso);
                }

                if let Some(uninhabited_1) = ty_1.try_prove_uninhabited()
                && let Some(term_0) = ty_0.try_find_arbitrary_term()
                {
                    let iso = {
                        input_ty
                        .scope(|tys_eq| {
                            uninhabited_1.contradiction(&tys_eq.transport(&term_0))
                        })
                        .scope_never_to_iso_never()
                    };
                    return (constraint_name, iso);
                }
            },

            TyKind::Nat => {
                match (eq_term_0.kind(), eq_term_1.kind()) {
                    (
                        TmKind::Succs { count: count_0, pred_term: pred_term_0 },
                        TmKind::Succs { count: count_1, pred_term: pred_term_1 },
                    ) => {

                        let count = cmp::min(&count_0, &count_1);
                        let diff_0 = count_0.strict_sub(&count);
                        let diff_1 = count_1.strict_sub(&count);
                        let term_0 = match NonZeroBigUint::new(diff_0) {
                            None => pred_term_0,
                            Some(count) => pred_term_0.succs(count),
                        };
                        let term_1 = match NonZeroBigUint::new(diff_1) {
                            None => pred_term_1,
                            Some(count) => pred_term_1.succs(count),
                        };

                        let iso = Iso::new(
                            &input_ty,
                            &term_0.equals(&term_1),
                            |big_eq| big_eq.nat_succs_injective(count.clone()),
                            |small_eq| {
                                small_eq
                                .map_eq(|nat| nat.succs(count.clone()))
                            },
                            |big_eq| {
                                big_eq
                                .nat_succs_injective(count.clone())
                                .map_eq(|nat| nat.succs(count.clone()))
                                .equality_contractible(&big_eq)
                            },
                            |small_eq| {
                                small_eq
                                .map_eq(|nat| nat.succs(count.clone()))
                                .nat_succs_injective(count.clone())
                                .equality_contractible(&small_eq)
                            },
                        );
                        return (constraint_name, iso);
                    },

                    (TmKind::Zero, TmKind::Succs { .. }) |
                    (TmKind::Succs { .. }, TmKind::Zero) => {
                        let iso = {
                            input_ty
                            .scope(|eq| eq.nat_eq())
                            .scope_never_to_iso_never()
                        };
                        return (constraint_name, iso);
                    },

                    _ => (),
                }
            },

            TyKind::Equal { .. } => {
                let iso = Iso::equality_equality_to_unit(&eq_term_0, &eq_term_1);
                return (constraint_name, iso);
            },

            TyKind::Never => {
                let iso = input_ty.scope(|_| eq_term_0.clone()).scope_never_to_iso_never();
                return (constraint_name, iso);
            },

            TyKind::Unit => unreachable!(),

            TyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                match (eq_term_0.kind(), eq_term_1.kind()) {
                    (
                        TmKind::InjLhs { lhs_name: _, lhs_term: lhs_term_0, rhs_ty: _ },
                        TmKind::InjLhs { lhs_name: _, lhs_term: lhs_term_1, rhs_ty: _ },
                    ) => {
                        let iso = Iso::sum_injective_lhs(
                            &lhs_name, &lhs_term_0, &lhs_term_1, &rhs_ty,
                        );
                        return (constraint_name, iso);
                    },
                    (
                        TmKind::InjRhs { lhs_name: _, rhs_term: rhs_term_0, lhs_ty: _ },
                        TmKind::InjRhs { lhs_name: _, rhs_term: rhs_term_1, lhs_ty: _ },
                    ) => {
                        let iso = Iso::sum_injective_rhs(
                            &lhs_name, &rhs_term_0, &rhs_term_1, &lhs_ty,
                        );
                        return (constraint_name, iso);
                    },

                    (TmKind::InjLhs { .. }, TmKind::InjRhs { .. }) |
                    (TmKind::InjRhs { .. }, TmKind::InjLhs { .. }) => {
                        let iso = {
                            input_ty
                            .scope(|sum_eq| sum_eq.case_eq())
                            .scope_never_to_iso_never()
                        };
                        return (constraint_name, iso);
                    },

                    _ => (),
                }
            },

            TyKind::Sigma { head_name, tail_ty } => {
                if let TmKind::Pair {
                    head_name: _,
                    tail_ty: _,
                    head_term: head_term_0,
                    tail_term: tail_term_0,
                } = eq_term_0.kind()
                && let TmKind::Pair {
                    head_name: _,
                    tail_ty: _,
                    head_term: head_term_1,
                    tail_term: tail_term_1,
                } = eq_term_1.kind()
                {
                    let iso = Iso::sigma_equality_to_projected_field_equalities(
                        &head_name,
                        tail_ty.unbind(),
                        &head_term_0,
                        &head_term_1,
                        &tail_term_0,
                        &tail_term_1,
                    );
                    return (constraint_name, iso);
                }
            },

            TyKind::Pi { arg_name, res_ty } => {
                if let TmKind::Func { arg_name: _, res_term: res_term_0 } = eq_term_0.kind()
                && let TmKind::Func { arg_name: _, res_term: res_term_1 } = eq_term_1.kind()
                {
                    // TODO: pass funext in
                    let funext = input_ty.ctx().try_get_funext().expect("no funext");
                    let iso = {
                        Iso::function_extensionality(
                            &arg_name,
                            &res_ty.var_ty(),
                            |arg| res_term_0.bind(&arg).equals(&res_term_1.bind(&arg)),
                            &funext,
                        )
                        .symmetry()
                    };
                    return (constraint_name, iso);
                }
            },
        }

        (constraint_name, input_ty.iso_refl())
    }

    fn simplify_sum_ty(
        lhs_name: &Name,
        lhs_ty: &Ty,
        rhs_ty: &Ty,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {
        let (new_lhs_name, lhs_iso) = Iso::simplify_ty(
            &lhs_ty, lhs_name, recursion_depth,
        );
        let (new_constraint_name, rhs_iso) = Iso::simplify_ty(
            &rhs_ty, constraint_name, recursion_depth,
        );

        let iso = Iso::sum_congruence(&lhs_name, &new_lhs_name, &lhs_iso, &rhs_iso);

        if let TyKind::Never = lhs_iso.output_ty().kind() {
            let iso = iso.transitivity(&Iso::sum_never_lhs(&lhs_name, &rhs_iso.output_ty()));
            return (new_constraint_name, iso);
        }
        if let TyKind::Never = rhs_iso.output_ty().kind() {
            let iso = iso.transitivity(&Iso::sum_never_rhs(&lhs_name, &lhs_iso.output_ty()));
            return (new_lhs_name, iso);
        }

        (new_constraint_name, iso)
    }

    fn simplify_sigma_ty(
        head_name: &Name,
        tail_ty: &Scope<Ty>,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {
        let (head_name, tail_ty) = Ctx::into_common_ctx((head_name, tail_ty));

        let head_ty = tail_ty.var_ty();
        let (mut constraint_name, tail_iso) = Iso::simplify_scoped_ty(
            &tail_ty, constraint_name, recursion_depth,
        );

        let mut iso = Iso::sigma_tail_congruence(&head_name, &head_ty, tail_iso.unbind());
        let (_, mut tail_ty) = iso.output_ty().unwrap_sigma();

        let mut recursion_depth = recursion_depth;
        loop {
            let head_ty = tail_ty.var_ty();

            if let Some(tail_ty) = tail_ty.try_strengthen() {
                if let TyKind::Never = tail_ty.kind() {
                    let iso = iso.transitivity(
                        &Iso::sigma_never_tail(&head_name, &head_ty),
                    );
                    return (constraint_name, iso);
                }

                let (new_head_name, head_iso) = Iso::simplify_ty(
                    &head_ty, &head_name, recursion_depth,
                );
                let head_ty = head_iso.output_ty();

                let iso = {
                    iso
                    .transitivity(
                        &Iso::sigma_head_congruence(
                            &head_name,
                            &new_head_name,
                            &head_iso,
                            |_| tail_ty.clone(),
                            &constraint_name,
                        )
                    )
                };
                let head_name = new_head_name;

                if let TyKind::Never = head_ty.kind() {
                    let iso = iso.transitivity(
                        &Iso::sigma_never_head(&head_name, |_| tail_ty.clone()),
                    );
                    return (head_name, iso);
                }

                if let TyKind::Unit = head_ty.kind() {
                    let iso = iso.transitivity(
                        &Iso::sigma_unit_head(&head_name, |_| tail_ty.clone()),
                    );
                    return (constraint_name, iso);
                }
                if let TyKind::Unit = tail_ty.kind() {
                    let iso = iso.transitivity(
                        &Iso::sigma_unit_tail(&head_name, &head_ty),
                    );
                    return (head_name, iso);
                }

                return (constraint_name, iso);
            }
            
            let (new_head_name, head_iso) = Iso::simplify_ty(
                &head_ty, &head_name, recursion_depth,
            );
            iso = iso.transitivity(
                &Iso::sigma_head_congruence(
                    &head_name, &new_head_name, &head_iso, tail_ty.unbind(), &constraint_name,
                ),
            );
            let head_name = new_head_name;
            let (_, next_tail_ty) = iso.output_ty().unwrap_sigma();
            tail_ty = next_tail_ty;
            let next_head_ty = tail_ty.var_ty();

            if let TyKind::Never = next_head_ty.kind() {
                let iso = iso.transitivity(
                    &Iso::sigma_never_head(&head_name, tail_ty.unbind()),
                );
                return (constraint_name, iso);
            }

            if let Some(head_ty) = as_equal(&head_ty, &next_head_ty) {
                if let Some(next_iso) = Iso::check_sigma_constrained_or_eliminated_head(
                    &head_name,
                    head_ty,
                    &tail_ty,
                    &constraint_name,
                ) {
                    return {
                        iso
                        .transitivity(&next_iso)
                        .simplify_output(&constraint_name, recursion_depth)
                    };
                }
                return (constraint_name, iso);
            }

            let head_ty = next_head_ty;

            let (new_constraint_name, tail_iso) = Iso::simplify_scoped_ty(
                &tail_ty, &constraint_name, recursion_depth,
            );
            constraint_name = new_constraint_name;
            iso = iso.transitivity(
                &Iso::sigma_tail_congruence(&head_name, &head_ty, tail_iso.unbind()),
            );
            let (_, next_tail_ty) = iso.output_ty().unwrap_sigma();
            tail_ty = next_tail_ty;

            if let Some(tail_ty) = tail_ty.try_strengthen() {
                if let TyKind::Never = tail_ty.kind() {
                    let iso = iso.transitivity(
                        &Iso::sigma_never_tail(&head_name, &head_ty),
                    );
                    return (constraint_name, iso);
                }
                if let TyKind::Unit = tail_ty.kind() {
                    let iso = iso.transitivity(
                        &Iso::sigma_unit_tail(&head_name, &head_ty),
                    );
                    return (head_name, iso);
                }

                return (constraint_name, iso);
            }

            if let Some(next_iso) = Iso::check_sigma_constrained_or_eliminated_head(
                &head_name,
                &head_ty,
                &tail_ty,
                &constraint_name,
            ) {
                return {
                    iso
                    .transitivity(&next_iso)
                    .simplify_output(&constraint_name, recursion_depth)
                };
            }

            let Some(next_recursion_depth) = recursion_depth.checked_sub(1) else {
                return (constraint_name, iso);
            };
            recursion_depth = next_recursion_depth;
        }
    }

    fn check_sigma_constrained_or_eliminated_head(
        head_name: &Name,
        head_ty: &Ty,
        tail_ty: &Scope<Ty>,
        constraint_name: &Name,
    ) -> Option<Iso> {
        let (head_name, head_ty, tail_ty) = Ctx::into_common_ctx((head_name, head_ty, tail_ty));

        if let Some((head_term, proof)) = tail_ty.constrains_own_var(&head_name) {
            return Some(Iso::sigma_tail_ty_constrains_head_ty(
                &head_name,
                tail_ty.unbind(),
                &head_term,
                |head, tail| proof.bind(&head).bind(&tail),
                &constraint_name,
            ));
        }
        if tail_ty.var_eliminated() {
            // TODO:
            //  sum distributivity
            //  nat distributivity
            if let TyKind::Sigma {
                head_name: head_head_name, tail_ty: head_tail_ty,
            } = head_ty.kind() {
                return Some(Iso::sigma_reassociate_to_tail(
                    &head_name,
                    &head_head_name,
                    &head_tail_ty.var_ty(),
                    head_tail_ty.unbind(),
                    tail_ty.unbind(),
                ));
            }
        }
        None
    }

    fn simplify_pi_ty(
        arg_name: &Name,
        res_ty: &Scope<Ty>,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {

        let (arg_name, res_ty, constraint_name) = Ctx::into_common_ctx((
            arg_name, res_ty, constraint_name,
        ));

        let input_ty = res_ty.to_pi(&arg_name);
        // TODO: pass funext in
        let funext = input_ty.ctx().try_get_funext().expect("no funext");
        let arg_ty = res_ty.var_ty();

        let (constraint_name, res_iso) = Iso::simplify_scoped_ty(
            &res_ty, &constraint_name, recursion_depth,
        );

        let iso = Iso::pi_res_congruence(
            &arg_name,
            &arg_ty,
            res_iso.unbind(),
            &funext,
        );

        let (_, res_ty) = iso.output_ty().unwrap_pi();

        if let Some(res_ty) = res_ty.try_strengthen() {
            let (new_arg_name, arg_iso) = Iso::simplify_ty(&arg_ty, &arg_name, recursion_depth);
            let iso = iso.transitivity(&Iso::pi_arg_congruence(
                &arg_name,
                &new_arg_name,
                &arg_iso,
                |_| res_ty.clone(),
                &funext,
            ));
            let arg_name = new_arg_name;
            let arg_ty = arg_iso.output_ty();

            if let Some(next_iso) = Iso::try_apply_pi_arg_identities(
                &arg_name,
                &arg_ty,
                &arg_ty.scope(|_| res_ty.clone()),
                &funext,
            ) {
                let iso = iso.transitivity(&next_iso);
                return (constraint_name, iso);
            }

            if let Some(next_iso) = Iso::try_apply_pi_res_identities(
                &arg_name,
                &arg_ty,
                &res_ty,
            ) {
                let iso = iso.transitivity(&next_iso);
                return (constraint_name, iso);
            }

            return (constraint_name, iso);
        }

        let (new_arg_name, arg_iso) = Iso::simplify_ty(&arg_ty, &arg_name, recursion_depth);
        let iso = iso.transitivity(&Iso::pi_arg_congruence(
            &arg_name,
            &new_arg_name,
            &arg_iso,
            res_ty.unbind(),
            &funext,
        ));
        let arg_name = new_arg_name;
        let (_, res_ty) = iso.output_ty().unwrap_pi();
        let arg_ty = res_ty.var_ty();

        if let Some(next_iso) = Iso::try_apply_pi_arg_identities(
            &arg_name,
            &arg_ty,
            &res_ty,
            &funext,
        ) {
            let iso = iso.transitivity(&next_iso);
            return (constraint_name, iso);
        }

        if let Some(res_ty) = res_ty.try_strengthen() {
            if let Some(next_iso) = Iso::try_apply_pi_res_identities(
                &arg_name,
                &arg_ty,
                &res_ty,
            ) {
                let iso = iso.transitivity(&next_iso);
                return (constraint_name, iso);
            }

            return (constraint_name, iso);
        }

        if let Some(next_iso) = Iso::check_pi_constrained_or_eliminated_arg(
            &arg_name,
            &res_ty,
        ) {
            let iso = iso.transitivity(&next_iso);
            return (constraint_name, iso);
        }

        let (constraint_name, res_iso) = Iso::simplify_scoped_ty(
            &res_ty, &constraint_name, recursion_depth,
        );

        let iso = iso.transitivity(&Iso::pi_res_congruence(
            &arg_name,
            &arg_ty,
            res_iso.unbind(),
            &funext,
        ));

        let (_, new_res_ty) = iso.output_ty().unwrap_pi();

        if new_res_ty != res_ty {
            let res_ty = new_res_ty;

            if let Some(res_ty) = res_ty.try_strengthen() {
                if let Some(next_iso) = Iso::try_apply_pi_res_identities(
                    &arg_name,
                    &arg_ty,
                    &res_ty,
                ) {
                    let iso = iso.transitivity(&next_iso);
                    return (constraint_name, iso);
                }

                return (constraint_name, iso);
            }

            if let Some(next_iso) = Iso::check_pi_constrained_or_eliminated_arg(
                &arg_name,
                &res_ty,
            ) {
                let iso = iso.transitivity(&next_iso);
                return (constraint_name, iso);
            }
        }

        (constraint_name, iso)
    }

    fn try_apply_pi_arg_identities(
        arg_name: &Name,
        arg_ty: &Ty,
        res_ty: &Scope<Ty>,
        funext: &Tm,
    ) -> Option<Iso> {
        if let TyKind::Never = arg_ty.kind() {
            return Some(Iso::pi_never_arg(&arg_name, res_ty.unbind(), &funext));
        }

        if let TyKind::Unit = arg_ty.kind() {
            return Some(Iso::pi_unit_arg(&arg_name, res_ty.unbind()));
        }

        None
    }

    fn try_apply_pi_res_identities(
        arg_name: &Name,
        arg_ty: &Ty,
        res_ty: &Ty,
    ) -> Option<Iso> {
        if let TyKind::Never = res_ty.kind()
        && let Some(arg_term) = arg_ty.try_find_arbitrary_term()
        {
            let iso = {
                arg_ty
                .pi(&arg_name, |_| res_ty.clone())
                .scope(|func| func.app(&arg_term))
                .scope_never_to_iso_never()
            };
            return Some(iso);
        }

        if let TyKind::Unit = res_ty.kind() {
            return Some(Iso::pi_unit_res(&arg_name, &arg_ty));
        }

        None
    }

    fn check_pi_constrained_or_eliminated_arg(
        arg_name: &Name,
        res_ty: &Scope<Ty>,
    ) -> Option<Iso> {
        // TODO:
        // when arg is eliminated do:
        //  (A + B) -> C ==> (A -> C) * (B -> C)
        //  and
        //  (A * B) -> C ==> A -> (B -> C)
        if let Some((arg_term_0, eq_proof)) = res_ty.constrains_own_var(&arg_name)
        && let Some((arg_term_1, apart_proof)) = arg_term_0.try_find_alternate_term()
        {
            let iso = {
                res_ty
                .to_pi(&arg_name)
                .scope(|func| {
                    apart_proof.bind(
                        &eq_proof
                        .bind(&arg_term_1)
                        .bind(&func.app(&arg_term_1))
                        .symmetry()
                    )
                })
                .scope_never_to_iso_never()
            };
            return Some(iso);
        }

        None
    }

    fn simplify_stuck_ty(
        stuck: &Stuck,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {
        debug_assert!(matches!(stuck.ty().kind(), TyKind::Universe));

        match stuck.kind() {
            StuckKind::ForLoop { .. } => {
                // TODO
                (constraint_name.clone(), stuck.to_ty().iso_refl())
            },

            StuckKind::Cong { motive: _, inhab, elim } => {
                let elim = elim.to_term();
                let inhab = inhab.map(|_, ty| ty.to_ty());
                Iso::simplify_cong_ty(&elim, &inhab, constraint_name, recursion_depth)
            },

            StuckKind::UniqueIdentity { motive: _, inhab, elim } => {
                let elim = elim.to_term();
                let inhab = inhab.map(|_, ty| ty.to_ty());
                Iso::simplify_unique_identity_ty(&elim, &inhab, constraint_name, recursion_depth)
            },

            /*
            // not sure this is a good idea.
            // we can convert to any type under an inconsistent context. Sometimes it might help
            // inferrence if this is converted to unit instead of never.
            StuckKind::Explode { motive: _, elim } => {
                let iso = Iso::simplify_explode_ty(&elim.to_term());
                (constraint_name.clone(), iso)
            },
            */

            StuckKind::Case { motive: _, lhs_inhab, rhs_inhab, elim } => {
                let elim = elim.to_term();
                let lhs_inhab = lhs_inhab.map(|_, ty| ty.to_ty());
                let rhs_inhab = rhs_inhab.map(|_, ty| ty.to_ty());
                Iso::simplify_case_ty(
                    &elim, &lhs_inhab, &rhs_inhab, constraint_name, recursion_depth,
                )
            },

            _ => (constraint_name.clone(), stuck.to_ty().iso_refl()),
        }
    }

    fn simplify_cong_ty(
        elim: &Tm,
        inhab: &Scope<Ty>,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {
        let (elim, inhab, constraint_name) = Ctx::into_common_ctx((elim, inhab, constraint_name));

        let (constraint_name, inhab_iso) = Iso::simplify_scoped_ty(
            &inhab, &constraint_name, recursion_depth,
        );
        let iso = Iso::cong_congruence(&elim, inhab_iso.unbind());
        let inhab = inhab_iso.map(|_, inhab_iso| inhab_iso.output_ty());

        if let Some(inhab) = inhab.try_strengthen() {
            let iso = iso.transitivity(&Iso::cong_ty_lift(&elim, &inhab));
            return (constraint_name, iso)
        }

        (constraint_name, iso)
    }

    fn simplify_unique_identity_ty(
        elim: &Tm,
        inhab: &Scope<Ty>,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {
        let (elim, inhab, constraint_name) = Ctx::into_common_ctx((elim, inhab, constraint_name));

        let (constraint_name, inhab_iso) = Iso::simplify_scoped_ty(
            &inhab, &constraint_name, recursion_depth,
        );
        let iso = Iso::unique_identity_congruence(&elim, inhab_iso.unbind());
        let inhab = inhab_iso.map(|_, inhab_iso| inhab_iso.output_ty());

        if let Some(inhab) = inhab.try_strengthen() {
            let iso = iso.transitivity(&Iso::unique_identity_ty_lift(&elim, &inhab));
            return (constraint_name, iso)
        }

        (constraint_name, iso)
    }

    fn simplify_explode_ty(
        elim: &Tm,
    ) -> Iso {
        elim
        .explode(|_| elim.ctx().universe())
        .to_ty()
        .scope(|_| elim.clone())
        .scope_never_to_iso_never()
    }

    fn simplify_case_ty(
        elim: &Tm,
        lhs_inhab: &Scope<Ty>,
        rhs_inhab: &Scope<Ty>,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Iso) {
        let (elim, lhs_inhab, rhs_inhab, constraint_name) = Ctx::into_common_ctx((
            elim, lhs_inhab, rhs_inhab, constraint_name,
        ));

        let (_, lhs_inhab_iso) = Iso::simplify_scoped_ty(
            &lhs_inhab, &constraint_name, recursion_depth,
        );
        let (constraint_name, rhs_inhab_iso) = Iso::simplify_scoped_ty(
            &rhs_inhab, &constraint_name, recursion_depth,
        );
        let iso = Iso::case_congruence(
            &elim,
            lhs_inhab_iso.unbind(),
            rhs_inhab_iso.unbind(),
        );

        if let Some(lhs_inhab) = lhs_inhab_iso.map(|_, iso| iso.output_ty()).try_strengthen()
        && let Some(rhs_inhab) = rhs_inhab_iso.map(|_, iso| iso.output_ty()).try_strengthen()
        && let Some(inhab) = as_equal(lhs_inhab, rhs_inhab)
        {
            let iso = iso.transitivity(&Iso::case_ty_lift(&elim, &inhab));
            return (constraint_name, iso);
        }

        (constraint_name, iso)
    }

    fn simplify_scoped_ty(
        scope: &Scope<Ty>,
        constraint_name: &Name,
        recursion_depth: u32,
    ) -> (Name, Scope<Iso>) {
        let (constraint_name, scope) = Ctx::into_common_ctx((constraint_name, scope));

        let (new_constraint_name, iso) = scope.map_out(|_, inner| {
            Iso::simplify_ty(&inner, &constraint_name, recursion_depth)
        });
        let new_constraint_name = Scope::new(new_constraint_name).force_strengthen();
        let iso = Scope::new(iso);

        (new_constraint_name, iso)
    }
}

