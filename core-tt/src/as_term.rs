use crate::priv_prelude::*;

pub trait AsTerm<S: Scheme> {
    fn to_term(&self) -> Tm<S>;
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

