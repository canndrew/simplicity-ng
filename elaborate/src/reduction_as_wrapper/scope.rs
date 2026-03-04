use crate::priv_prelude::*;

#[expect(unused)] // FIXME
impl Scope<Tm> {
    pub(crate) fn irreducible(&self) -> Reduction {
        Reduction::from_core(self.core_ref().identity_reduction())
    }

    pub(crate) fn reduce_unique(
        &self,
        unique_term: &Tm,
        covering_ty: impl FnOnce(Tm) -> Tm,
        covering: impl FnOnce(Tm) -> Tm,
    ) -> Reduction {
        let (var_tag, body) = self.core_ref().strip_var_ty_tag();
        Reduction::from_core(
            body
            .reduce_unique(
                &unique_term.core_ref(),
                |term| covering_ty(Tm::from_core(term)).into_core(),
                |term| covering(Tm::from_core(term)).into_core(),
            )
            .with_var_ty_tags(&var_tag, &var_tag)
        )
    }

    pub(crate) fn reduce_impossible(
        &self,
        never_scope: impl FnOnce(Tm) -> Tm,
    ) -> Reduction {
        let (var_tag, body) = self.core_ref().strip_var_ty_tag();
        Reduction::from_core(
            body
            .reduce_impossible(
                |never| never_scope(Tm::from_core(never)).into_core()
            )
            .with_var_ty_tags(&var_tag, &var_tag)
        )
    }

    pub(crate) fn try_reduce_irrelevant(&self) -> Option<Reduction> {
        let (var_tag, body) = self.core_ref().strip_var_ty_tag();
        Some(Reduction::from_core(
            body.try_reduce_irrelevant()?.with_var_ty_tags(&var_tag, &var_tag)
        ))
    }

    pub(crate) fn reduce_constraint(&self, recursion_depth: u32) -> Reduction {
        let Some(_recursion_depth) = recursion_depth.checked_sub(1) else {
            return self.irreducible();
        };

        if let Some(reduction) = self.try_reduce_irrelevant() {
            return reduction;
        }

        let (_var_tag, var_ty) = self.var_tag_and_ty();

        match var_ty.kind() {
            TyKind::Stuck { .. } => {
                // TODO
                self.irreducible()
            },

            TyKind::Universe |
            TyKind::Nat |
            TyKind::Never |
            TyKind::Unit => {
                self.irreducible()
            },

            TyKind::Equal { .. } => {
                //self.reduce_constraint_equality(recursion_depth)
                todo!()
            },

            TyKind::Sum { .. } => {
                //self.reduce_constraint_sum(recursion_depth)
                todo!()
            },

            TyKind::Sigma { .. } => {
                //self.reduce_constraint_sigma(recursion_depth)
                todo!()
            },

            TyKind::Pi { .. } => {
                /*
                let iso = var_ty.simplify_iso(recursion_depth);
                self.reduce_over_iso(&iso)
                */
                todo!()
            },
        }
    }

    pub(crate) fn reduce_over_iso(
        &self,
        iso: &Iso,
    ) -> Reduction {
        let (var_tag, body) = self.core_ref().strip_var_ty_tag();
        Reduction::from_core(
            body.reduce_over_iso(&iso.core_ref()).with_var_ty_tags(&var_tag, &var_tag)
        )
    }
}

