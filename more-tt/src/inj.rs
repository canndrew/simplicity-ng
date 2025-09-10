use crate::priv_prelude::*;

#[derive_where(Clone, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct Inj<S: Scheme> {
    pub(crate) fwd: Scope<S, Tm<S>>,
    pub(crate) rev_eq: Scope<S, Scope<S, Scope<S, Tm<S>>>>,
}

impl<S: Scheme> Inj<S> {
    pub fn new(
        input_ty: &Ty<S>,
        fwd: impl FnOnce(Tm<S>) -> Tm<S>,
        rev_eq: impl FnOnce(Tm<S>, Tm<S>, Tm<S>) -> Tm<S>,
    ) -> Inj<S> {
        let fwd = input_ty.scope(fwd);
        let rev_eq = input_ty.scope(|term_0| {
            input_ty.weaken_into(&term_0.ctx()).scope(|term_1| {
                fwd.bind(&term_0).equals(&fwd.bind(&term_1)).scope(|fwd_eq| {
                    let term_0 = term_0.weaken_into(&fwd_eq.ctx());
                    let term_1 = term_0.weaken_into(&fwd_eq.ctx());
                    let ret = rev_eq(term_0.clone(), term_1.clone(), fwd_eq);
                    assert_eq!(ret.ty(), term_0.equals(&term_1));
                    ret
                })
            })
        });

        Inj { fwd, rev_eq }
    }

    pub fn input_ty(&self) -> Ty<S> {
        self.fwd.var_ty()
    }

    pub fn fwd(&self, term_0: &Tm<S>) -> Tm<S> {
        self.fwd.bind(term_0)
    }

    pub fn rev_eq(&self, term_0: &Tm<S>, term_1: &Tm<S>, term_eq: &Tm<S>) -> Tm<S> {
        self.rev_eq.bind(&term_0).bind(&term_1).bind(&term_eq)
    }

    pub fn transitivity(&self, other: &Inj<S>) -> Inj<S> {
        let fwd = self.fwd.map(|_, term_1| other.fwd.bind(&term_1));
        let rev_eq = self.rev_eq.map(|term_0, rev_eq| {
            rev_eq.map(|term_1, rev_eq| {
                let mid_term_0 = self.fwd.bind(&term_0);
                let mid_term_1 = self.fwd.bind(&term_1);
                other.rev_eq.bind(&mid_term_0).bind(&mid_term_1).map(|_, mid_term_eq| {
                    rev_eq.bind(&mid_term_eq)
                })
            })
        });
        Inj { fwd, rev_eq }
    }

    pub fn constant(term: &Tm<S>) -> Inj<S> {
        Inj::new(
            &term.ctx().unit_ty(),
            |_| term.clone(),
            |_, _, eq| eq.ctx().unit_term().refl(),
        )
    }
}

