use crate::priv_prelude::*;

#[extension(pub trait StuckExt)]
impl<S: Scheme> Stuck<S> {
    fn try_find_arbitrary_term(&self) -> Option<Tm<S>> {
        assert!(matches!(self.ty().kind(), TyKind::Universe));

        match self.kind() {
            StuckKind::Var { .. } => None,

            StuckKind::ForLoop { elim, motive: _, zero_inhab, succ_inhab } => {
                let zero_term = zero_inhab.to_ty().try_find_arbitrary_term()?;
                let succ_term = {
                    self
                    .ctx()
                    .nat()
                    .try_scope(|elim| {
                        elim
                        .for_loop(
                            |elim| elim.ctx().universe(),
                            &zero_inhab,
                            |elim, state| succ_inhab.bind(&elim).bind(&state),
                        )
                        .to_ty()
                        .try_scope(|_| {
                            succ_inhab
                            .bind(&elim)
                            .bind(
                                &elim
                                .for_loop(
                                    |elim| elim.ctx().universe(),
                                    &zero_inhab,
                                    |elim, state| succ_inhab.bind(&elim).bind(&state),
                                ),
                            )
                            .to_ty()
                            .try_find_arbitrary_term()
                        })
                    })?
                };
                Some(
                    elim
                    .to_term()
                    .for_loop(
                        |elim| {
                            elim
                            .for_loop(
                                |elim| elim.ctx().universe(),
                                &zero_inhab,
                                |elim, state| succ_inhab.bind(&elim).bind(&state),
                            )
                            .to_ty()
                        },
                        &zero_term,
                        |elim, state| succ_term.bind(&elim).bind(&state),
                    ),
                )
            },

            StuckKind::Cong { elim, motive: _, inhab } => {
                let inhab_term = inhab.try_map(|_, inner| {
                    inner.to_ty().try_find_arbitrary_term()
                })?;
                Some(
                    elim
                    .to_term()
                    .cong(
                        |_, _, elim| {
                            elim
                            .cong(
                                |_, _, elim| elim.ctx().universe(),
                                |eq_term| inhab.bind(&eq_term),
                            )
                            .to_ty()
                        },
                        |eq_term| inhab_term.bind(&eq_term),
                    ),
                )
            },

            StuckKind::UniqueIdentity { elim, motive: _, inhab } => {
                let inhab_term = inhab.try_map(|_, inner| {
                    inner.to_ty().try_find_arbitrary_term()
                })?;
                Some(
                    elim
                    .to_term()
                    .unique_identity(
                        |_, elim| {
                            elim
                            .unique_identity(
                                |_, elim| elim.ctx().universe(),
                                |eq_term| inhab.bind(&eq_term),
                            )
                            .to_ty()
                        },
                        |eq_term| inhab_term.bind(&eq_term),
                    ),
                )
            },

            StuckKind::Explode { elim, motive: _ } => {
                Some(
                    elim
                    .to_term()
                    .explode(|elim| {
                        elim
                        .explode(|elim| elim.ctx().universe())
                        .to_ty()
                    })
                )
            },

            StuckKind::Case { elim, motive: _, lhs_inhab, rhs_inhab } => {
                let lhs_inhab_term = lhs_inhab.try_map(|_, inner| {
                    inner.to_ty().try_find_arbitrary_term()
                })?;
                let rhs_inhab_term = rhs_inhab.try_map(|_, inner| {
                    inner.to_ty().try_find_arbitrary_term()
                })?;
                Some(
                    elim
                    .to_term()
                    .case(
                        |elim| {
                            elim
                            .case(
                                |elim| elim.ctx().universe(),
                                |lhs_term| lhs_inhab.bind(&lhs_term),
                                |rhs_term| rhs_inhab.bind(&rhs_term),
                            )
                            .to_ty()
                        },
                        |lhs_term| lhs_inhab_term.bind(&lhs_term),
                        |rhs_term| rhs_inhab_term.bind(&rhs_term),
                    ),
                )
            },

            StuckKind::ProjHead { .. } |
            StuckKind::ProjTail { .. } |
            StuckKind::App { .. } => None,

            StuckKind::Max { .. } |
            StuckKind::Add { .. } |
            StuckKind::Mul { .. } |
            StuckKind::PowConstant { .. } |
            StuckKind::TagsApart { .. } |
            StuckKind::EqualEqEqTyInjective { .. } |
            StuckKind::EqualEqEqTerm0Injective { .. } |
            StuckKind::EqualEqEqTerm1Injective { .. } |
            StuckKind::SumEqNameInjective { .. } |
            StuckKind::SumEqLhsInjective { .. } |
            StuckKind::SumEqRhsInjective { .. } |
            StuckKind::SigmaEqNameInjective { .. } |
            StuckKind::SigmaEqHeadInjective { .. } |
            StuckKind::SigmaEqTailInjective { .. } |
            StuckKind::PiEqNameInjective { .. } |
            StuckKind::PiEqArgInjective { .. } |
            StuckKind::PiEqResInjective { .. } => unreachable!(),
        }
    }

    fn try_find_alternate_term(&self) -> Option<(Tm<S>, Scope<S, Tm<S>>)> {
        match self.kind() {
            StuckKind::Var { .. } => {
                // TODO
            },

            // TODO
            _ => (),
        }
        None
    }

    fn try_prove_uninhabited(&self) -> Option<Uninhabited<S>> {
        let inhabitant_name = S::name_from_str("inhabitant");

        assert!(matches!(self.ty().kind(), TyKind::Universe));

        match self.kind() {
            StuckKind::Var { .. } => None,

            StuckKind::ForLoop { .. } => {
                // TODO
                None
            },

            StuckKind::Cong { .. } => {
                // TODO
                None
            },

            StuckKind::UniqueIdentity { .. } => {
                // TODO
                None
            },

            StuckKind::Explode { elim, motive: _ } => {
                let elim = elim.to_term();
                Some(Uninhabited::new(
                    &elim.explode(|elim| elim.ctx().universe()).to_ty(),
                    |_| elim.clone(),
                ))
            },

            StuckKind::Case { elim, motive: _, lhs_inhab, rhs_inhab } => {
                let elim = elim.to_term();
                let lhs_inhab_uninhabited = lhs_inhab.try_map(|_, ty| {
                    ty.to_ty().try_prove_uninhabited()
                })?;
                let rhs_inhab_uninhabited = rhs_inhab.try_map(|_, ty| {
                    ty.to_ty().try_prove_uninhabited()
                })?;
                return Some(Uninhabited::new(
                    &self.to_ty(),
                    |term| {
                        elim
                        .case(
                            |elim| {
                                elim
                                .case(
                                    |elim| elim.ctx().universe(),
                                    |lhs_term| lhs_inhab.bind(&lhs_term),
                                    |rhs_term| rhs_inhab.bind(&rhs_term),
                                )
                                .to_ty()
                                .pi(&inhabitant_name, |term| term.ctx().never())
                            },
                            |lhs_term| {
                                lhs_inhab
                                .bind(&lhs_term)
                                .to_ty()
                                .func(&inhabitant_name, |term| {
                                    lhs_inhab_uninhabited.bind(&lhs_term).contradiction(&term)
                                })
                            },
                            |rhs_term| {
                                rhs_inhab
                                .bind(&rhs_term)
                                .to_ty()
                                .func(&inhabitant_name, |term| {
                                    rhs_inhab_uninhabited.bind(&rhs_term).contradiction(&term)
                                })
                            },
                        )
                        .app(&term)
                    },
                ));
            },

            StuckKind::ProjHead { .. } |
            StuckKind::ProjTail { .. } |
            StuckKind::App { .. } => None,

            StuckKind::Max { .. } |
            StuckKind::Add { .. } |
            StuckKind::Mul { .. } |
            StuckKind::PowConstant { .. } |
            StuckKind::TagsApart { .. } |
            StuckKind::EqualEqEqTyInjective { .. } |
            StuckKind::EqualEqEqTerm0Injective { .. } |
            StuckKind::EqualEqEqTerm1Injective { .. } |
            StuckKind::SumEqNameInjective { .. } |
            StuckKind::SumEqLhsInjective { .. } |
            StuckKind::SumEqRhsInjective { .. } |
            StuckKind::SigmaEqNameInjective { .. } |
            StuckKind::SigmaEqHeadInjective { .. } |
            StuckKind::SigmaEqTailInjective { .. } |
            StuckKind::PiEqNameInjective { .. } |
            StuckKind::PiEqArgInjective { .. } |
            StuckKind::PiEqResInjective { .. } => unreachable!(),
        }
    }

    fn try_prove_contractible(&self) -> Option<Contractible<S>> {
        assert!(matches!(self.ty().kind(), TyKind::Universe));
        
        match self.kind() {
            StuckKind::Var { .. } => None,

            StuckKind::ForLoop { .. } => {
                // TODO
                None
            },

            StuckKind::Cong { .. } => {
                // TODO
                None
            },

            StuckKind::UniqueIdentity { .. } => {
                // TODO
                None
            },

            StuckKind::Explode { elim, motive: _ } => {
                let elim = elim.to_term();
                let unique_term = {
                    elim.explode(|elim| elim.explode(|elim| elim.ctx().universe()).to_ty())
                };
                Some(Contractible::new(
                    &unique_term,
                    |term| elim.weaken_into(&term.ctx()).explode(|_| term.equals(&unique_term)),
                ))
            },

            StuckKind::Case { .. } => {
                // TODO
                None
            },

            StuckKind::ProjHead { .. } |
            StuckKind::ProjTail { .. } |
            StuckKind::App { .. } => None,

            StuckKind::Max { .. } |
            StuckKind::Add { .. } |
            StuckKind::Mul { .. } |
            StuckKind::PowConstant { .. } |
            StuckKind::TagsApart { .. } |
            StuckKind::EqualEqEqTyInjective { .. } |
            StuckKind::EqualEqEqTerm0Injective { .. } |
            StuckKind::EqualEqEqTerm1Injective { .. } |
            StuckKind::SumEqNameInjective { .. } |
            StuckKind::SumEqLhsInjective { .. } |
            StuckKind::SumEqRhsInjective { .. } |
            StuckKind::SigmaEqNameInjective { .. } |
            StuckKind::SigmaEqHeadInjective { .. } |
            StuckKind::SigmaEqTailInjective { .. } |
            StuckKind::PiEqNameInjective { .. } |
            StuckKind::PiEqArgInjective { .. } |
            StuckKind::PiEqResInjective { .. } => unreachable!(),
        }
    }

    fn constrains_var(
        &self,
        index: usize,
        var_name: &Name<S>,
    ) -> Option<(Tm<S>, Scope<S, Tm<S>>)> {
        assert!(matches!(self.ty().kind(), TyKind::Universe));

        match self.kind() {
            StuckKind::Var { .. } => (),

            StuckKind::ForLoop { .. } => {
                // TODO
            },

            StuckKind::Cong { .. } => {
                // TODO
            },

            StuckKind::UniqueIdentity { .. } => {
                // TODO
            },

            StuckKind::Explode { elim, motive: _ } => {
                let elim = elim.to_term().try_strengthen_to_index(index)?;
                let var_term = elim.explode(|_| self.ctx().var(index).ty());
                let proof = self.to_ty().scope(|_| {
                    elim.explode(|_| self.ctx().var(index).equals(&var_term))
                });
                return Some((var_term, proof));
            },

            StuckKind::Case { elim, motive: _, lhs_inhab, rhs_inhab } => {
                let (lhs_var_term, lhs_proof) = {
                    lhs_inhab
                    .map_out(|_, lhs_inhab| lhs_inhab.to_ty().constrains_var(index, var_name))?
                };
                let (rhs_var_term, rhs_proof) = {
                    rhs_inhab
                    .map_out(|_, rhs_inhab| rhs_inhab.to_ty().constrains_var(index, var_name))?
                };
                let var_term = as_equal(lhs_var_term, rhs_var_term)?;
                let lhs_proof = Scope::new(lhs_proof);
                let rhs_proof = Scope::new(rhs_proof);

                let proof = {
                    self
                    .to_ty()
                    .scope(|case_term| {
                        elim
                        .to_term()
                        .weaken_into(&case_term.ctx())
                        .case(
                            |elim| {
                                elim
                                .case(
                                    |elim| elim.ctx().universe(),
                                    |lhs_term| lhs_inhab.bind(&lhs_term),
                                    |rhs_term| rhs_inhab.bind(&rhs_term),
                                )
                                .to_ty()
                                .pi(var_name, |case_term| {
                                    case_term.ctx().var(index).equals(&var_term)
                                })
                            },
                            |lhs_term| {
                                lhs_inhab
                                .bind(&lhs_term)
                                .to_ty()
                                .func(var_name, |case_term| {
                                    lhs_proof.bind(&lhs_term).bind(&case_term)
                                })
                            },
                            |rhs_term| {
                                rhs_inhab
                                .bind(&rhs_term)
                                .to_ty()
                                .func(var_name, |case_term| {
                                    rhs_proof.bind(&rhs_term).bind(&case_term)
                                })
                            },
                        )
                        .app(&case_term)
                    })
                };

                return Some((var_term, proof));
            },

            StuckKind::ProjHead { .. } |
            StuckKind::ProjTail { .. } |
            StuckKind::App { .. } => (),

            StuckKind::Max { .. } |
            StuckKind::Add { .. } |
            StuckKind::Mul { .. } |
            StuckKind::PowConstant { .. } |
            StuckKind::TagsApart { .. } |
            StuckKind::EqualEqEqTyInjective { .. } |
            StuckKind::EqualEqEqTerm0Injective { .. } |
            StuckKind::EqualEqEqTerm1Injective { .. } |
            StuckKind::SumEqNameInjective { .. } |
            StuckKind::SumEqLhsInjective { .. } |
            StuckKind::SumEqRhsInjective { .. } |
            StuckKind::SigmaEqNameInjective { .. } |
            StuckKind::SigmaEqHeadInjective { .. } |
            StuckKind::SigmaEqTailInjective { .. } |
            StuckKind::PiEqNameInjective { .. } |
            StuckKind::PiEqArgInjective { .. } |
            StuckKind::PiEqResInjective { .. } => unreachable!(),
        }
        None
    }
}

