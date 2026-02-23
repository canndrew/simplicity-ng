use crate::priv_prelude::*;

/// Trait for types that can be represented as terms.
pub trait AsTerm<S: Scheme> {
    /// Convert `self` to a term. This should be an infallible operation.
    fn to_term(&self) -> Tm<S>;
    /// Create a `Self` from a correctly-typed term.
    ///
    /// For `Ty::from_term(term)`, `term` must be a type.
    ///
    /// For `Scope::<_, T>::from_term(term)`, `term` must be a function whose output type can be
    /// converted to `T`.
    ///
    /// # Panics
    ///
    /// If `term` does not have the correct type for `Self`.
    fn from_term(term: &Tm<S>) -> Self;
}


impl<S: Scheme> AsTerm<S> for Tm<S> {
    fn to_term(&self) -> Tm<S> {
        self.clone()
    }

    fn from_term(term: &Tm<S>) -> Tm<S> {
        term.clone()
    }
}

impl<S: Scheme> AsTerm<S> for Ty<S> {
    fn to_term(&self) -> Tm<S> {
        self.to_term()
    }

    fn from_term(term: &Tm<S>) -> Ty<S> {
        term.to_ty()
    }
}

impl<S: Scheme, T: Contextual<S> + AsTerm<S>> AsTerm<S> for Scope<S, T> {
    fn to_term(&self) -> Tm<S> {
        let scope = self.map(|_var_term, inner| inner.to_term());

        self.var_ty().func(scope.unbind())
    }

    fn from_term(term: &Tm<S>) -> Scope<S, T> {
        let TyKind::Pi { res_ty } = term.ty().kind() else {
            panic!("term does not represent a scope. ty == {:#?}", term.ty());
        };
        res_ty.var_ty().scope(|arg_term| T::from_term(&term.app(&arg_term)))
    }
}

