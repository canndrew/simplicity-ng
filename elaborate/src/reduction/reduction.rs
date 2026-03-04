use crate::priv_prelude::*;

#[derive(Clone, Debug)]
#[derive(core_tt::Contextual)]
#[scheme(TagScheme)]
pub struct Reduction {
    old_constraint_name: Name,
    new_constraint_name: Name,
    body: Scope<Tm>,
    fwd: Scope<Tm>,
    rev: Scope<Tm>,
    covering_ty: Scope<Tm>,
    covering: Scope<Tm>,
}

impl Reduction {
    pub fn new(
        old_constraint_name: &Name,
        new_constraint_name: &Name,
        body: &Scope<Tm>,
        new_constraint_ty: &Ty,
        fwd: impl FnOnce(Tm) -> Tm,
        rev: impl FnOnce(Tm) -> Tm,
        covering_ty: impl FnOnce(Tm) -> Tm,
        covering: impl FnOnce(Tm) -> Tm,
    ) -> Reduction {
        let (old_constraint_name, new_constraint_name, body, new_constraint_ty) = Ctx::into_common_ctx((
            old_constraint_name, new_constraint_name, body, new_constraint_ty,
        ));
        let old_constraint_ty = body.var_ty();

        let fwd = new_constraint_ty.scope(fwd);
        let rev = old_constraint_ty.scope(rev);
        let covering_ty = old_constraint_ty.scope(covering_ty);
        let covering = old_constraint_ty.scope(covering);

        if cfg!(debug_assertions) {
            assert_eq!(fwd.map(|_, term| term.ty()).try_strengthen().unwrap(), old_constraint_ty);
            assert_eq!(rev.map(|_, term| term.ty()).try_strengthen().unwrap(), new_constraint_ty);
            old_constraint_ty.with_cons(|var_term| {
                let term_0 = body.bind(&var_term);
                let term_1 = body.bind(&fwd.bind(&rev.bind(&var_term)));
                assert_eq!(
                    covering_ty.bind(&var_term).ty(),
                    term_0.ty().to_term().equals(&term_1.ty().to_term())
                );
                assert_eq!(
                    covering.bind(&var_term).ty(),
                    covering_ty.bind(&var_term).heterogeneous_equal(&term_0, &term_1)
                );
            });
        }

        Reduction { old_constraint_name, new_constraint_name, body, fwd, rev, covering_ty, covering }
    }

    pub fn old_constraint_name(&self) -> Name {
        self.old_constraint_name.clone()
    }

    pub fn new_constraint_name(&self) -> Name {
        self.new_constraint_name.clone()
    }

    pub fn old_constraint_ty(&self) -> Ty {
        self.rev.var_ty()
    }

    pub fn new_constraint_ty(&self) -> Ty {
        self.fwd.var_ty()
    }

    pub fn old_body(&self) -> Scope<Tm> {
        self.body.clone()
    }

    pub fn new_body(&self) -> Scope<Tm> {
        self.fwd.map(|_, term| self.body.bind(&term))
    }

    pub fn reduced_scope(&self) -> InferScope<Tm> {
        InferScope::from_scope(&self.new_constraint_name, &self.new_body())
    }

    pub fn fwd(&self, term: &Tm) -> Tm {
        self.fwd.bind(term)
    }

    pub fn rev(&self, term: &Tm) -> Tm {
        self.rev.bind(term)
    }

    pub fn covering_ty(&self, term: &Tm) -> Tm {
        self.covering_ty.bind(term)
    }

    pub fn covering(&self, term: &Tm) -> Tm {
        self.covering.bind(term)
    }

    pub fn compose(&self, other: &Reduction) -> Reduction {
        let (reduction_0, reduction_1) = Ctx::into_common_ctx((self, other));

        debug_assert_eq!(reduction_0.new_body(), reduction_1.body);
        debug_assert_eq!(reduction_0.new_constraint_name, reduction_1.old_constraint_name);

        let body = reduction_0.old_body();
        let old_constraint_name = reduction_0.old_constraint_name.clone();
        let new_constraint_name = reduction_1.new_constraint_name.clone();
        let new_constraint_ty = reduction_1.new_constraint_ty();

        Reduction::new(
            &old_constraint_name,
            &new_constraint_name,
            &body,
            &new_constraint_ty,
            |new_var| reduction_0.fwd(&reduction_1.fwd(&new_var)),
            |old_var| reduction_1.rev(&reduction_0.rev(&old_var)),
            |old_var| {
                reduction_0
                .covering_ty
                .bind(&old_var)
                .transitivity(&reduction_1.covering_ty(&reduction_0.rev(&old_var)))
            },
            |old_var| {
                Tm::heterogeneous_transitivity(
                    &body.bind(&old_var),
                    &body.bind(&reduction_0.fwd(&reduction_0.rev(&old_var))),
                    &body.bind(
                        &reduction_0.fwd(
                            &reduction_1.fwd(
                                &reduction_1.rev(
                                    &reduction_0.rev(&old_var),
                                ),
                            ),
                        ),
                    ),
                    &reduction_0.covering_ty(&old_var),
                    &reduction_1.covering_ty(&reduction_0.rev(&old_var)),
                    &reduction_0.covering(&old_var),
                    &reduction_1.covering(&reduction_0.rev(&old_var)),
                )
            },
        )
    }

    pub fn and_then(
        &self,
        next_reduction: impl FnOnce(InferScope<Tm>) -> Reduction,
    ) -> Reduction {
        let next_reduction = next_reduction(self.reduced_scope());
        self.compose(&next_reduction)
    }

    /*
    pub fn replace_new_constraint_name(self, new_constraint_name: &Name) -> Reduction {
        let mut ret = self;
        ret.new_constraint_name = new_constraint_name.clone();
        ret
    }
    */

    pub fn reduce_more(&self, recursion_depth: u32) -> Reduction {
        self.and_then(|scope| scope.reduce_constraint(recursion_depth))
    }
}


