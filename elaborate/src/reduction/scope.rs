use crate::priv_prelude::*;

impl InferScope<Tm> {
    pub fn irreducible(&self) -> Reduction {
        let constraint_name = self.constraint_name();
        let constraint_ty = self.constraint_ty();
        let body = self.body();

        Reduction::new(
            &constraint_name,
            &constraint_name,
            &body,
            &constraint_ty,
            |term| term,
            |term| term,
            |term| body.bind(&term).ty().to_term().refl(),
            |term| body.bind(&term).refl(),
        )
    }

    /*
    pub fn reduce_unique(
        &self,
        unique_term: &Tm,
        covering_ty: impl FnOnce(Tm) -> Tm,
        covering: impl FnOnce(Tm) -> Tm,
    ) -> Reduction {
        let (body, unique_term) = Ctx::into_common_ctx((self, unique_term));

        Reduction::new(
            &body,
            &body.var_tag(),
            &body.ctx().unit_ty(),
            |_| unique_term.clone(),
            |term| term.ctx().unit_term(),
            covering_ty,
            covering,
        )
    }
    */

    pub fn reduce_impossible(
        &self,
        never_scope: impl FnOnce(Tm) -> Tm,
    ) -> Reduction {
        let constraint_name = self.constraint_name();
        let old_constraint_ty = self.constraint_ty();
        let body = self.body();
        let new_constraint_ty = self.ctx().never();
        let fwd = new_constraint_ty.scope(|never| {
            never.explode(|_| old_constraint_ty.clone())
        });
        let rev = old_constraint_ty.scope(never_scope);
        let covering_ty = old_constraint_ty.scope(|term| {
            rev
            .bind(&term)
            .explode(|_| {
                body
                .bind(&term)
                .ty()
                .to_term()
                .equals(
                    &body
                    .bind(&fwd.bind(&rev.bind(&term)))
                    .ty()
                    .to_term()
                )
            })
        });
        let covering = old_constraint_ty.scope(|term| {
            rev
            .bind(&term)
            .explode(|_| {
                covering_ty
                .bind(&term)
                .heterogeneous_equal(
                    &body.bind(&term),
                    &body.bind(&fwd.bind(&rev.bind(&term))),
                )
            })
        });
        Reduction::new(
            &constraint_name,
            &constraint_name,
            &body,
            &new_constraint_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    pub fn try_reduce_irrelevant(&self) -> Option<Reduction> {
        let constraint_name = self.constraint_name();
        let body = self.body();

        if let Some(inner) = body.try_strengthen() {
            if let Some(solution) = body.var_ty().try_find_arbitrary_term() {
                let reduction = Reduction::new(
                    &constraint_name,
                    &constraint_name,
                    &body,
                    &body.ctx().unit_ty(),
                    |_| solution.clone(),
                    |_| body.ctx().unit_term(),
                    |_| inner.ty().to_term().refl(),
                    |_| inner.refl(),
                );
                return Some(reduction);
            }
        }
        None
    }

    pub fn reduce_over_iso(
        &self,
        iso: &Iso,
        new_constraint_name: &Name,
    ) -> Reduction {
        let (infer_scope, iso) = Ctx::into_common_ctx((self, iso));
        let constraint_name = infer_scope.constraint_name();
        let body = infer_scope.body();
        assert_eq!(body.var_ty(), iso.input_ty());

        Reduction::new(
            &constraint_name,
            &new_constraint_name,
            &body,
            &iso.output_ty(),
            |new_term| iso.rev(&new_term),
            |old_term| iso.fwd(&old_term),
            |old_term| {
                body
                .map(|_, body| body.ty())
                .bind_eq(&iso.fwd_rev(&old_term).symmetry())
            },
            |old_term| {
                iso
                .fwd_rev(&old_term)
                .symmetry()
                .cong(
                    |old_term_0, old_term_1, old_term_eq| {
                        body
                        .map(|_, body| body.ty())
                        .bind_eq(&old_term_eq)
                        .heterogeneous_equal(
                            &body.bind(&old_term_0),
                            &body.bind(&old_term_1),
                        )
                    },
                    |old_term| body.bind(&old_term).refl(),
                )
            },
        )
    }

    pub fn reduce_constraint(&self, recursion_depth: u32) -> Reduction {
        let Some(_recursion_depth) = recursion_depth.checked_sub(1) else {
            return self.irreducible();
        };

        if let Some(reduction) = self.try_reduce_irrelevant() {
            return reduction;
        }

        let constraint_name = self.constraint_name();
        let constraint_ty = self.constraint_ty();
        match constraint_ty.kind() {
            TyKind::Stuck { .. } => {
                // TODO
                self.irreducible()
            },

            TyKind::Name |
            TyKind::Universe |
            TyKind::Nat |
            TyKind::Never |
            TyKind::Unit => {
                self.irreducible()
            },

            TyKind::Equal { .. } => {
                self.reduce_constraint_equality(recursion_depth)
            },

            TyKind::Sum { .. } => {
                self.reduce_constraint_sum(recursion_depth)
            },

            TyKind::Sigma { .. } => {
                self.reduce_constraint_sigma(recursion_depth)
            },

            TyKind::Pi { .. } => {
                let (new_constraint_name, iso) = {
                    Iso::simplify_ty(&constraint_ty, &constraint_name, recursion_depth)
                };
                self.reduce_over_iso(&iso, &new_constraint_name)
            },
        }
    }
}

