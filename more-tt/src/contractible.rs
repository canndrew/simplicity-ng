use crate::priv_prelude::*;

#[derive_where(Clone, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct Contractible<S: Scheme> {
    term: Tm<S>,
    proof: Scope<S, Tm<S>>,
}

impl<S: Scheme> Contractible<S> {
    pub fn new(
        term: &Tm<S>,
        proof: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Contractible<S> {
        let proof = term.ty().scope(|term_1| {
            let ret = proof(term_1.clone());
            let TyKind::Equal { eq_term_0, eq_term_1 } = ret.ty().kind() else {
                panic!();
            };
            assert_eq!(eq_term_0, term_1);
            assert_eq!(eq_term_1, *term);
            ret
        });
        Contractible {
            term: term.clone(),
            proof,
        }
    }

    pub fn unique_term(&self) -> Tm<S> {
        self.term.clone()
    }

    pub fn contract(&self, term_1: &Tm<S>) -> Tm<S> {
        self.proof.bind(term_1)
    }
}

