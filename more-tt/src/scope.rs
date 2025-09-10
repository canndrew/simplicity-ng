use crate::priv_prelude::*;

#[extension(pub trait ScopeTmExt)]
impl<S: Scheme> Scope<S, Tm<S>> {
    fn bind_eq(&self, eq: &Tm<S>) -> Tm<S> {
        eq.map_eq(|term| self.bind(&term))
    }

    fn bind_eq_dependent(&self, eq: &Tm<S>) -> Tm<S> {
        eq.map_eq_dependent(|term| self.bind(&term))
    }

    fn simplify_further(&self) -> Scope<S, Tm<S>> {
        self.var_ty().simplify().map(|_, term| self.bind(&term))
    }

    fn scope_never_to_iso_never(&self) -> Iso<S> {
        assert!(matches!(self.map_out(|_, term| term.ty()).kind(), TyKind::Never));

        Iso::new(
            &self.var_ty(),
            &self.ctx().never(),
            |term| self.bind(&term),
            |never| never.explode(|_| self.var_ty()),
            |term| self.bind(&term).explode(|never| never.explode(|_| self.var_ty()).equals(&term)),
            |never| never.explode(|never| self.bind(&never.explode(|_| self.var_ty())).equals(&never)),
        )
    }
}

#[extension(pub trait ScopeTyExt)]
impl<S: Scheme> Scope<S, Ty<S>> {
    fn bind_eq(&self, eq: &Tm<S>) -> Tm<S> {
        eq
        .cong(
            |x0, x1, _| {
                self.bind(&x0).to_term().equals(&self.bind(&x1).to_term())
            },
            |x| self.bind(&x).to_term().refl(),
        )
    }

    fn constrains_own_var(&self) -> Option<(Tm<S>, Scope<S, Scope<S, Tm<S>>>)> {
        let (var_term, proof) = self.map_out(|_, ty| ty.constrains_var(self.ctx().len()))?;
        let proof = Scope::new(proof);
        Some((var_term, proof))
    }

    fn try_bind_iso(&self, _iso: &Iso<S>) -> Option<Iso<S>> {
        assert!(matches!(self.var_ty().kind(), TyKind::Universe));

        // TODO
        None
    }
}

