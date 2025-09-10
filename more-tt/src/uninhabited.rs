use crate::priv_prelude::*;

#[derive_where(Clone, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct Uninhabited<S: Scheme> {
    proof: Scope<S, Tm<S>>,
}

impl<S: Scheme> Uninhabited<S> {
    pub fn new(
        ty: &Ty<S>,
        proof: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Uninhabited<S> {
        let proof = ty.scope(|term| {
            let ret = proof(term);
            let TyKind::Never = ret.ty().kind() else {
                panic!()
            };
            ret
        });
        Uninhabited { proof }
    }

    pub fn contradiction(&self, term: &Tm<S>) -> Tm<S> {
        self.proof.bind(term)
    }

    pub fn to_iso(&self) -> Iso<S> {
        Iso::new(
            &self.proof.var_ty(),
            &self.ctx().never(),
            |term| self.proof.bind(&term),
            |term| term.explode(|_| self.proof.var_ty()),
            |term| {
                self
                .proof
                .bind(&term)
                .explode(|elim| {
                    elim.explode(|_| self.proof.var_ty()).equals(&term)
                })
            },
            |term| {
                term
                .explode(|elim| {
                    self.proof.bind(&elim.explode(|_| self.proof.var_ty())).equals(&elim)
                })
            },
        )
    }
}

impl<S: Scheme> AsTerm<S> for Uninhabited<S> {
    fn to_term(&self) -> Tm<S> {
        self.proof.to_term()
    }

    fn from_term(term: &Tm<S>) -> Uninhabited<S> {
        Uninhabited {
            proof: AsTerm::from_term(term),
        }
    }
}

