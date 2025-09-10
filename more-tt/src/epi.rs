use crate::priv_prelude::*;

#[derive_where(Clone, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct Epi<S: Scheme> {
    pub(crate) fwd: Scope<S, Tm<S>>,
    pub(crate) rev: Scope<S, Tm<S>>,
    pub(crate) rev_fwd: Scope<S, Tm<S>>,
}

impl<S: Scheme> Epi<S> {
    pub fn new(
        input_ty: &Ty<S>,
        output_ty: &Ty<S>,
        fwd: impl FnOnce(Tm<S>) -> Tm<S>,
        rev: impl FnOnce(Tm<S>) -> Tm<S>,
        rev_fwd: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Epi<S> {
        let fwd = input_ty.scope(fwd);
        let rev = output_ty.scope(rev);
        let rev_fwd = output_ty.scope(|term_1| {
            let ret = rev_fwd(term_1.clone());
            assert_eq!(
                ret.ty(),
                fwd.bind(&rev.bind(&term_1)).equals(&term_1),
            );
            ret
        });
        Epi { fwd, rev, rev_fwd }
    }

    pub fn input_ty(&self) -> Ty<S> {
        self.fwd.var_ty()
    }

    pub fn output_ty(&self) -> Ty<S> {
        self.rev.var_ty()
    }

    pub fn fwd(&self, term_0: &Tm<S>) -> Tm<S> {
        self.fwd.bind(term_0)
    }

    pub fn rev(&self, term_1: &Tm<S>) -> Tm<S> {
        self.rev.bind(term_1)
    }

    pub fn rev_fwd(&self, term_1: &Tm<S>) -> Tm<S> {
        self.rev_fwd.bind(term_1)
    }

    pub fn transitivity(&self, other: &Epi<S>) -> Epi<S> {
        let fwd = self.fwd.map(|_, term_1| other.fwd.bind(&term_1));
        let rev = other.rev.map(|_, term_1| self.rev.bind(&term_1));
        let rev_fwd = other.rev.var_ty().scope(|term_2| {
            other
            .fwd
            .bind_eq(&self.rev_fwd.bind(&other.rev.bind(&term_2)))
            .transitivity(&other.rev_fwd.bind(&term_2))
        });
        Epi { fwd, rev, rev_fwd }
    }

    pub fn sum_congruence(
        lhs_epi: &Epi<S>,
        rhs_epi: &Epi<S>,
    ) -> Epi<S> {
        let input_ty = Ty::sum(&lhs_epi.input_ty(), &rhs_epi.input_ty());
        let output_ty = Ty::sum(&lhs_epi.output_ty(), &rhs_epi.output_ty());
        Epi::new(
            &input_ty,
            &output_ty,
            |term| {
                term
                .case(
                    |_| output_ty.clone(),
                    |lhs_term| {
                        lhs_epi
                        .fwd
                        .bind(&lhs_term)
                        .inj_lhs(&rhs_epi.output_ty())
                    },
                    |rhs_term| {
                        rhs_epi
                        .fwd
                        .bind(&rhs_term)
                        .inj_rhs(&lhs_epi.output_ty())
                    },
                )
            },
            |term| {
                term
                .case(
                    |_| input_ty.clone(),
                    |lhs_term| {
                        lhs_epi
                        .rev
                        .bind(&lhs_term)
                        .inj_lhs(&rhs_epi.input_ty())
                    },
                    |rhs_term| {
                        rhs_epi
                        .rev
                        .bind(&rhs_term)
                        .inj_rhs(&lhs_epi.input_ty())
                    },
                )
            },

            |term| {
                term
                .case(
                    |term| {
                        term
                        .case(
                            |_| input_ty.clone(),
                            |lhs_term| {
                                lhs_epi
                                .rev
                                .bind(&lhs_term)
                                .inj_lhs(&rhs_epi.input_ty())
                            },
                            |rhs_term| {
                                rhs_epi
                                .rev
                                .bind(&rhs_term)
                                .inj_rhs(&lhs_epi.input_ty())
                            },
                        )
                        .case(
                            |_| output_ty.clone(),
                            |lhs_term| {
                                lhs_epi
                                .fwd
                                .bind(&lhs_term)
                                .inj_lhs(&rhs_epi.output_ty())
                            },
                            |rhs_term| {
                                rhs_epi
                                .fwd
                                .bind(&rhs_term)
                                .inj_rhs(&lhs_epi.output_ty())
                            },
                        )
                        .equals(&term)
                    },
                    |lhs_term| {
                        lhs_epi
                        .rev_fwd(&lhs_term)
                        .map_eq(|lhs_term| lhs_term.inj_lhs(&rhs_epi.output_ty()))
                    },
                    |rhs_term| {
                        rhs_epi
                        .rev_fwd(&rhs_term)
                        .map_eq(|rhs_term| rhs_term.inj_rhs(&lhs_epi.output_ty()))
                    },
                )
            },
        )
    }

    pub fn non_dependent_sigma_head_congruence(
        head_epi: &Epi<S>,
        tail_ty: &Ty<S>,
    ) -> Epi<S> {
        let input_ty = head_epi.input_ty().sigma(|_| tail_ty.clone());
        let output_ty = head_epi.output_ty().sigma(|_| tail_ty.clone());

        Epi::new(
            &input_ty,
            &output_ty,
            |term| {
                head_epi
                .fwd(&term.proj_head())
                .pair(|_| tail_ty.clone(), &term.proj_tail())
            },
            |term| {
                head_epi
                .rev(&term.proj_head())
                .pair(|_| tail_ty.clone(), &term.proj_tail())
            },
            |term| {
                head_epi
                .rev_fwd(&term.proj_head())
                .cong(
                    |head_0, head_1, _| {
                        head_0
                        .pair(|_| tail_ty.clone(), &term.proj_tail())
                        .equals(
                            &head_1
                            .pair(|_| tail_ty.clone(), &term.proj_tail())
                        )
                    },
                    |head| {
                        head
                        .pair(|_| tail_ty.clone(), &term.proj_tail())
                        .refl()
                    },
                )
            },
        )
    }
}

#[extension(pub trait ScopeEpiExt)]
impl<S: Scheme> Scope<S, Epi<S>> {
    fn sigma_tail_congruence(&self) -> Epi<S> {
        let input_tail_ty = self.map(|_, epi| epi.input_ty());
        let output_tail_ty = self.map(|_, epi| epi.output_ty());
        let tail_fwd = self.map(|_, epi| epi.fwd.clone());
        let tail_rev = self.map(|_, epi| epi.rev.clone());
        let tail_rev_fwd = self.map(|_, epi| epi.rev_fwd.clone());

        let input_ty = input_tail_ty.to_sigma();
        let output_ty = output_tail_ty.to_sigma();

        Epi::new(
            &input_ty,
            &output_ty,
            |term| {
                term
                .proj_head()
                .pair(
                    |head| output_tail_ty.bind(&head),
                    &tail_fwd.bind(&term.proj_head()).bind(&term.proj_tail()),
                )
            },
            |term| {
                term
                .proj_head()
                .pair(
                    |head| input_tail_ty.bind(&head),
                    &tail_rev.bind(&term.proj_head()).bind(&term.proj_tail()),
                )
            },
            |term| {
                tail_rev_fwd
                .bind(&term.proj_head())
                .bind(&term.proj_tail())
                .map_eq(|tail| {
                    tail
                    .proj_head()
                    .pair(|head| output_tail_ty.bind(&head), &tail)
                })
            },
        )
    }
}

