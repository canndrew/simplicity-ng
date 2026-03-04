use crate::priv_prelude::*;

#[derive(Clone, Debug)]
#[derive(core_tt::Contextual)]
#[scheme(TagScheme)]
pub struct Reduction {
    reduction: more_tt::Reduction<TagScheme>,
}

impl Contextual for Reduction {
    type Core = more_tt::Reduction<TagScheme>;

    fn from_core(reduction: more_tt::Reduction<TagScheme>) -> Reduction {
        Reduction { reduction }
    }

    fn into_core(self) -> more_tt::Reduction<TagScheme> {
        self.reduction
    }

    fn core_ref(&self) -> &more_tt::Reduction<TagScheme> {
        &self.reduction
    }
}

impl Reduction {
    pub fn new(
        body: &Scope<Tm>,
        fwd: &Scope<Tm>,
        rev: &Scope<Tm>,
        covering_ty: &Scope<Tm>,
        covering: &Scope<Tm>,
    ) -> Reduction {
        let old_var_tag = rev.var_tag();
        let new_var_tag = fwd.var_tag();

        let reduction = more_tt::Reduction::new(
            &rev.core_ref().var_ty(),
            &fwd.core_ref().var_ty(),
            body.core_ref().unbind(),
            |term| fwd.bind(&Tm::from_core(term.strip_tag())).into_core().tag(&old_var_tag),
            |term| rev.bind(&Tm::from_core(term.strip_tag())).into_core().tag(&new_var_tag),
            covering_ty.core_ref().unbind(),
            covering.core_ref().unbind(),
        );
        Reduction { reduction }
    }

    pub fn old_var_tag_and_ty(&self) -> (Tag, Ty) {
        let (old_var_tag, old_var_ty) = self.reduction.old_var_ty().unwrap_tagged();
        let old_var_ty = Ty::from_core(old_var_ty);
        (old_var_tag, old_var_ty)
    }

    pub fn new_var_tag_and_ty(&self) -> (Tag, Ty) {
        let (new_var_tag, new_var_ty) = self.reduction.new_var_ty().unwrap_tagged();
        let new_var_ty = Ty::from_core(new_var_ty);
        (new_var_tag, new_var_ty)
    }

    pub fn old_var_tag(&self) -> Tag {
        let (old_var_tag, _) = self.reduction.old_var_ty().unwrap_tagged();
        old_var_tag
    }

    pub fn new_var_tag(&self) -> Tag {
        let (new_var_tag, _) = self.reduction.new_var_ty().unwrap_tagged();
        new_var_tag
    }

    pub fn old_var_ty(&self) -> Ty {
        let (_, old_var_ty) = self.reduction.old_var_ty().unwrap_tagged();
        Ty::from_core(old_var_ty)
    }

    pub fn new_var_ty(&self) -> Ty {
        let (_, new_var_ty) = self.reduction.new_var_ty().unwrap_tagged();
        Ty::from_core(new_var_ty)
    }

    pub fn old_body(&self) -> Scope<Tm> {
        Scope::from_core(self.reduction.old_body())
    }

    pub fn new_body(&self) -> Scope<Tm> {
        Scope::from_core(self.reduction.new_body())
    }

    pub fn fwd(&self, new_term: &Tm) -> Tm {
        Tm::from_core(
            self
            .reduction
            .fwd(&new_term.core_ref().tag(&self.new_var_tag()))
            .strip_tag()
        )
    }

    pub fn rev(&self, old_term: &Tm) -> Tm {
        Tm::from_core(
            self
            .reduction
            .fwd(&old_term.core_ref().tag(&self.old_var_tag()))
            .strip_tag()
        )
    }

    pub fn covering_ty(&self, old_term: &Tm) -> Tm {
        Tm::from_core(
            self
            .reduction
            .covering_ty(&old_term.core_ref().tag(&self.old_var_tag()))
            .strip_tag()
        )
    }

    pub fn covering(&self, old_term: &Tm) -> Tm {
        Tm::from_core(
            self
            .reduction
            .covering(&old_term.core_ref().tag(&self.old_var_tag()))
            .strip_tag()
        )
    }

    pub fn compose(&self, other: &Reduction) -> Reduction {
        Reduction::from_core(self.core_ref().compose(&other.core_ref()))
    }

    pub fn and_then(
        &self,
        next_reduction: impl FnOnce(Scope<Tm>) -> Reduction,
    ) -> Reduction {
        let next_reduction = next_reduction(self.new_body());
        self.compose(&next_reduction)
    }
}



/*
impl Reduction {
    pub fn compose(&self, other: &Reduction) -> Reduction {
        let (reduction_0, reduction_1) = Ctx::into_common_ctx((self, other));

        assert_eq!(reduction_0.reduced_scope(), reduction_1.body);
        assert_eq!(reduction_0.new_var_tag(), reduction_1.old_var_tag());
        assert_eq!(reduction_0.new_var_ty(), reduction_1.old_var_ty());

        let (old_var_tag, old_var_ty) = reduction_0.rev.var_tag_and_ty();
        let (new_var_tag, new_var_ty) = reduction_1.fwd.var_tag_and_ty();

        let body = reduction_0.body.clone();

        let fwd = new_var_ty.scope(&new_var_tag, |new_var_1| {
            reduction_0.fwd(&reduction_1.fwd(&new_var_1))
        });
        let rev = old_var_ty.scope(&old_var_tag, |old_var| {
            reduction_1.rev(&reduction_0.rev(&old_var))
        });
        let covering_ty = old_var_ty.scope(&old_var_tag, |old_var| {
            reduction_0
            .covering_ty
            .bind(&old_var)
            .transitivity(&reduction_1.covering_ty(&reduction_0.rev(&old_var)))
        });
        let covering = old_var_ty.scope(&old_var_tag, |old_var| {
            Tm::heterogeneous_transitivity(
                &body.bind(&old_var),
                &body.bind(&reduction_0.fwd(&reduction_0.rev(&old_var))),
                &body.bind(
                    &reduction_0.fwd(
                        &reduction_1.fwd(
                            &reduction_1.rev(&reduction_0.rev(&old_var)),
                        ),
                    ),
                ),
                &reduction_0.covering_ty(&old_var),
                &reduction_1.covering_ty(&reduction_0.rev(&old_var)),
                &reduction_0.covering(&old_var),
                &reduction_1.covering(&reduction_0.rev(&old_var)),
            )
        });

        Reduction::new(&self.body, &fwd, &rev, &covering_ty, &covering)
    }

    pub fn and_then(
        &self,
        next_reduction: impl FnOnce(Scope<Tm>) -> Reduction,
    ) -> Reduction {
        let next_reduction = next_reduction(self.reduced_scope());
        self.compose(&next_reduction)
    }

    pub fn reduce_more(&self, recursion_depth: u32) -> Reduction {
        self.and_then(|scope| scope.reduce_constraint(recursion_depth))
    }
}
*/

