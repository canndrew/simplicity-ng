use crate::priv_prelude::*;

#[derive_where(Clone, Debug)]
#[derive(Contextual)]
#[scheme(TagScheme)]
pub struct InferScope<T: Contextual<TagScheme> + fmt::Debug> {
    constraint_name: Name,
    scope: Scope<T>,
}

impl<T: Contextual<TagScheme> + fmt::Debug> InferScope<T> {
    pub fn from_scope(
        constraint_name: &Name,
        scope: &Scope<T>,
    ) -> InferScope<T> {
        let (constraint_name, scope) = Ctx::into_common_ctx((constraint_name, scope));
        InferScope { constraint_name, scope }
    }

    pub fn constraint_name(&self) -> Name {
        self.constraint_name.clone()
    }

    pub fn constraint_ty(&self) -> Ty {
        self.scope.var_ty()
    }

    pub fn body(&self) -> Scope<T> {
        self.scope.clone()
    }

    pub fn bind_constraint(self, term: &Tm) -> T {
        self.scope.bind(term)
    }

    pub fn try_map<U: Contextual<TagScheme> + fmt::Debug, E>(
        self,
        func: impl FnOnce(Tm, T) -> Result<U, E>,
    ) -> Result<InferScope<U>, E> {
        let InferScope { constraint_name, scope } = self;
        Ok(InferScope {
            constraint_name,
            scope: scope.try_map(func)?,
        })
    }

    pub fn map<U: Contextual<TagScheme> + fmt::Debug>(
        self,
        func: impl FnOnce(Tm, T) -> U,
    ) -> InferScope<U> {
        let InferScope { constraint_name, scope } = self;
        InferScope {
            constraint_name,
            scope: scope.map(func),
        }
    }

    pub fn try_flat_map<U: Contextual<TagScheme> + fmt::Debug, E>(
        self,
        func: impl FnOnce(Tm, T) -> Result<InferScope<U>, E>,
    ) -> Result<InferScope<U>, E> {
        Ok(self.try_map(func)?.flatten())
    }

    pub fn flat_map<U: Contextual<TagScheme> + fmt::Debug>(
        self,
        func: impl FnOnce(Tm, T) -> InferScope<U>,
    ) -> InferScope<U> {
        self.map(func).flatten()
    }
}

impl<T: Contextual<TagScheme> + fmt::Debug> InferScope<InferScope<T>> {
    pub fn flatten(self) -> InferScope<T> {
        let InferScope { constraint_name, scope } = self;
        let new_constraint_name = {
            scope
            .map(|_, inner| inner.constraint_name())
            .force_strengthen()
        };

        let head_ty = scope.var_ty();
        let tail_ty = scope.map(|_, inner| inner.scope.var_ty());

        let combined_metavar_ty = head_ty.sigma(&constraint_name, tail_ty.unbind());
        let new_scope = combined_metavar_ty.scope(|pair| {
            scope.bind(&pair.proj_head()).scope.bind(&pair.proj_tail())
        });

        InferScope {
            constraint_name: new_constraint_name,
            scope: new_scope,
        }
    }
}

impl InferScope<Tm> {
    pub fn minimize_constraint(&mut self, recursion_depth: u32) {
        let reduction = self.reduce_constraint(recursion_depth);
        *self = reduction.reduced_scope();
    }

    pub fn try_solve(&mut self, recursion_depth: u32) -> Option<Tm> {
        self.minimize_constraint(recursion_depth);

        if let TyKind::Unit = self.scope.var_ty().kind() {
            return Some(self.scope.bind(&self.scope.ctx().unit_term()));
        }

        None
    }
}

