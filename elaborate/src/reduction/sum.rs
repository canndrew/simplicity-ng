use crate::priv_prelude::*;

impl InferScope<Tm> {
    pub(crate) fn reduce_constraint_sum(&self, recursion_depth: u32) -> Reduction {
        let constraint_name = self.constraint_name();
        let constraint_ty = self.constraint_ty();
        let body = self.body();
        let (lhs_name, lhs_ty, rhs_ty) = constraint_ty.unwrap_sum();

        let lhs_scope = InferScope::from_scope(
            &lhs_name,
            &lhs_ty.scope(|lhs_term| {
                body.bind(&lhs_term.inj_lhs(&lhs_name, &rhs_ty))
            })
        );
        let rhs_scope = InferScope::from_scope(
            &constraint_name,
            &rhs_ty.scope(|rhs_term| {
                body.bind(&rhs_term.inj_rhs(&lhs_name, &lhs_ty))
            }),
        );
        let lhs_reduction = lhs_scope.reduce_constraint(recursion_depth);
        let rhs_reduction = rhs_scope.reduce_constraint(recursion_depth);

        let reduction = self.reduction_sum_congruence(&lhs_reduction, &rhs_reduction);
        let new_lhs_name = lhs_reduction.new_constraint_name();
        let new_lhs_ty = lhs_reduction.new_constraint_ty();
        let new_rhs_ty = rhs_reduction.new_constraint_ty();

        if let TyKind::Never = new_lhs_ty.kind() {
            return reduction.and_then(|scope| {
                scope.reduce_over_iso(
                    &Iso::sum_never_lhs(&new_lhs_name, &new_rhs_ty),
                    &constraint_name,
                )
            });
        }

        if let TyKind::Never = new_rhs_ty.kind() {
            return reduction.and_then(|scope| {
                scope
                .reduce_over_iso(
                    &Iso::sum_never_rhs(&new_lhs_name, &new_lhs_ty),
                    &new_lhs_name,
                )
            });
        }

        reduction
    }

    fn reduction_sum_congruence(
        &self,
        lhs_reduction: &Reduction,
        rhs_reduction: &Reduction,
    ) -> Reduction {
        let (infer_scope, lhs_reduction, rhs_reduction) = Ctx::into_common_ctx((
            self, lhs_reduction, rhs_reduction,
        ));
        let body = infer_scope.body();

        let old_lhs_name = lhs_reduction.old_constraint_name();
        let old_lhs_ty = lhs_reduction.old_constraint_ty();
        let old_constraint_name = rhs_reduction.old_constraint_name();
        let old_rhs_ty = rhs_reduction.old_constraint_ty();
        let new_lhs_name = lhs_reduction.new_constraint_name();
        let new_lhs_ty = lhs_reduction.new_constraint_ty();
        let new_constraint_name = rhs_reduction.new_constraint_name();
        let new_rhs_ty = rhs_reduction.new_constraint_ty();

        let old_constraint_ty = old_lhs_ty.sum(&old_lhs_name, &old_rhs_ty);
        let new_constraint_ty = new_lhs_ty.sum(&new_lhs_name, &new_rhs_ty);
        debug_assert_eq!(body.var_ty(), old_constraint_ty);

        let fwd = {
            new_constraint_ty
            .scope(|sum| {
                sum
                .case(
                    |_| old_constraint_ty.clone(),
                    |lhs_term| {
                        lhs_reduction.fwd(&lhs_term).inj_lhs(&old_lhs_name, &old_rhs_ty)
                    },
                    |rhs_term| {
                        rhs_reduction.fwd(&rhs_term).inj_rhs(&old_lhs_name, &old_lhs_ty)
                    },
                )
            })
        };
        let rev = {
            old_constraint_ty
            .scope(|sum| {
                sum
                .case(
                    |_| new_constraint_ty.clone(),
                    |lhs_term| {
                        lhs_reduction.rev(&lhs_term).inj_lhs(&new_lhs_name, &new_rhs_ty)
                    },
                    |rhs_term| {
                        rhs_reduction.rev(&rhs_term).inj_rhs(&new_lhs_name, &new_lhs_ty)
                    },
                )
            })
        };
        let covering_ty = {
            old_constraint_ty
            .scope(|sum| {
                sum
                .case(
                    |sum| {
                        body
                        .bind(&sum)
                        .ty()
                        .to_term()
                        .equals(
                            &body
                            .bind(&fwd.bind(&rev.bind(&sum)))
                            .ty()
                            .to_term()
                        )
                    },
                    |lhs_term| lhs_reduction.covering_ty(&lhs_term),
                    |rhs_term| rhs_reduction.covering_ty(&rhs_term),
                )
            })
        };
        let covering = {
            old_constraint_ty
            .scope(|sum| {
                sum
                .case(
                    |sum| {
                        covering_ty
                        .bind(&sum)
                        .heterogeneous_equal(
                            &body.bind(&sum),
                            &body.bind(&fwd.bind(&rev.bind(&sum))),
                        )
                    },
                    |lhs_term| lhs_reduction.covering(&lhs_term),
                    |rhs_term| rhs_reduction.covering(&rhs_term),
                )
            })
        };

        Reduction::new(
            &old_constraint_name,
            &new_constraint_name,
            &body,
            &new_constraint_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }
}

