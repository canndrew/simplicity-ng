use crate::priv_prelude::*;

#[expect(unused)] // FIXME
impl Scope<Tm> {
    pub(crate) fn reduce_constraint_sum(&self, recursion_depth: u32) -> Reduction {
        let (var_tag, var_ty) = self.var_tag_and_ty();
        let (lhs_tag, lhs_ty, rhs_ty) = var_ty.unwrap_sum();

        let lhs_scope = lhs_ty.scope(&lhs_tag, |lhs_term| {
            self.bind(&lhs_term.inj_lhs(&lhs_tag, &rhs_ty))
        });
        let rhs_scope = rhs_ty.scope(&var_tag, |rhs_term| {
            self.bind(&rhs_term.inj_rhs(&lhs_tag, &lhs_ty))
        });
        let lhs_reduction = lhs_scope.reduce_constraint(recursion_depth);
        let rhs_reduction = rhs_scope.reduce_constraint(recursion_depth);

        let reduction = self.reduction_sum_congruence(&lhs_reduction, &rhs_reduction);

        if let TyKind::Never = lhs_reduction.new_var_ty().kind() {
            return reduction.and_then(|scope| scope.reduce_sum_never_lhs());
        }

        if let TyKind::Never = rhs_reduction.new_var_ty().kind() {
            return reduction.and_then(|scope| scope.reduce_sum_never_rhs());
        }

        reduction
    }

    fn reduction_sum_congruence(
        &self,
        lhs_reduction: &Reduction,
        rhs_reduction: &Reduction,
    ) -> Reduction {
        let (old_var_tag, new_var_tag, rhs_reduction) = {
            rhs_reduction.core_ref().strip_var_ty_tags()
        };
        let (body_old_var_tag, body) = self.core_ref().strip_var_ty_tag();
        debug_assert_eq!(body_old_var_tag, old_var_tag);

        Reduction::from_core(
            body
            .reduction_sum_congruence(lhs_reduction.core_ref(), &rhs_reduction)
            .with_var_ty_tags(&old_var_tag, &new_var_tag)
        )
    }

    fn reduce_sum_never_lhs(&self) -> Reduction {
        let (lhs_tag, lhs_ty, rhs_ty) = self.var_ty().unwrap_sum();
        let () = lhs_ty.unwrap_never();
        self.reduce_over_iso(
            &Iso::sum_never_lhs(&lhs_tag, &rhs_ty)
        )
        /*
        Reduction::from_core(
            self
            .core_ref()
            .reduce_under_tag(|body| {
                let (lhs_ty, rhs_ty) = body.var_ty().unwrap_sum();
                let (lhs_tag, lhs_ty) = lhs_ty.unwrap_tagged();
                body
                .reduce_over_iso(
                    &more_tt::Iso::sum_congruence(
                        &lhs_ty.iso_tag(&lhs_tag).symmetry(),
                        &rhs_ty.iso_refl(),
                    )
                )
                .and_then(|body| body.reduce_sum_never_lhs())
            })
        )
        */
    }

    fn reduce_sum_never_rhs(&self) -> Reduction {
        Reduction::from_core(
            self
            .core_ref()
            .reduce_strip_tag()
            .and_then(|body| {
                body.reduce_sum_never_rhs()
            })
        )
    }
}

