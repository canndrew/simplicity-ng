use crate::priv_prelude::*;

#[derive_where(Clone, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct Equiprovable<S: Scheme> {
    pub(crate) fwd: Scope<S, Tm<S>>,
    pub(crate) rev: Scope<S, Tm<S>>,
}

impl<S: Scheme> Equiprovable<S> {
    pub fn new(
        input_ty: &Ty<S>,
        fwd: impl FnOnce(Tm<S>) -> Tm<S>,
        rev: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Equiprovable<S> {
        let fwd = input_ty.scope(fwd);
        let Some(output_ty) = fwd.map(|_, output| output.ty()).try_strengthen() else {
            panic!("fwd is dependent");
        };
        let rev = output_ty.scope(rev);
        let Some(input_ty_again) = rev.map(|_, input| input.ty()).try_strengthen() else {
            panic!("rev is dependent");
        };
        assert_eq!(*input_ty, input_ty_again);
        Equiprovable { fwd, rev }
    }

    pub fn input_ty(&self) -> Ty<S> {
        self.fwd.var_ty()
    }

    pub fn output_ty(&self) -> Ty<S> {
        self.rev.var_ty()
    }

    pub fn fwd(&self, term: &Tm<S>) -> Tm<S> {
        self.fwd.bind(term)
    }

    pub fn rev(&self, term: &Tm<S>) -> Tm<S> {
        self.rev.bind(term)
    }
}

