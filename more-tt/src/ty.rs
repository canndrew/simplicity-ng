use crate::priv_prelude::*;

#[extension(pub trait TyExt)]
impl<S: Scheme> Ty<S> {
    fn iso_refl(&self) -> Iso<S> {
        Iso::new(
            self,
            self,
            |term| term,
            |term| term,
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    fn try_find_arbitrary_term(&self) -> Option<Tm<S>> {
        let term_opt = match self.kind() {
            TyKind::User { .. } => None,
            TyKind::Stuck { stuck } => stuck.try_find_arbitrary_term(),
            TyKind::Universe => Some(self.ctx().universe().to_term()),
            TyKind::Nat => Some(self.ctx().zero()),
            TyKind::Equal { .. } => None,
            TyKind::Never => None,
            TyKind::Unit => Some(self.ctx().unit_term()),
            TyKind::Sum { lhs_ty, rhs_ty } => {
                match lhs_ty.try_find_arbitrary_term() {
                    Some(lhs_term) => {
                        Some(lhs_term.inj_lhs(&rhs_ty))
                    },
                    None => {
                        let rhs_term = rhs_ty.try_find_arbitrary_term()?;
                        Some(rhs_term.inj_rhs(&lhs_ty))
                    },
                }
            },
            TyKind::Sigma { tail_ty } => {
                let head_term = tail_ty.var_ty().try_find_arbitrary_term()?;
                let tail_term = tail_ty.bind(&head_term).try_find_arbitrary_term()?;
                Some(head_term.pair(
                    |head_term| tail_ty.bind(&head_term),
                    &tail_term,
                ))
            },
            TyKind::Pi { res_ty } => {
                let res_term = res_ty.try_map(|_, inner| inner.try_find_arbitrary_term())?;
                Some(res_term.to_term())
            },
        };
        match term_opt {
            Some(term) => Some(term),
            None => {
                for index in 0..self.ctx().len() {
                    let term = self.ctx().var(index);
                    if term.ty() == *self {
                        return Some(term);
                    }
                }
                None
            },
        }
    }

    fn try_prove_uninhabited(&self) -> Option<Uninhabited<S>> {
        match self.kind() {
            TyKind::User { .. } => None,
            TyKind::Stuck { stuck } => stuck.try_prove_uninhabited(),
            TyKind::Universe => None,
            TyKind::Nat => None,
            TyKind::Equal { eq_term_0, eq_term_1 } => {
                eq_term_0.try_prove_apart(&eq_term_1)
            },
            TyKind::Never => {
                Some(Uninhabited::new(
                    self,
                    |never| never,
                ))
            },
            TyKind::Unit => None,
            TyKind::Sum { lhs_ty, rhs_ty } => {
                let lhs_uninhabited = lhs_ty.try_prove_uninhabited()?;
                let rhs_uninhabited = rhs_ty.try_prove_uninhabited()?;
                Some(Uninhabited::new(
                    self,
                    |sum_term| sum_term.case(
                        |elim| elim.ctx().never(),
                        |lhs_term| lhs_uninhabited.contradiction(&lhs_term),
                        |rhs_term| rhs_uninhabited.contradiction(&rhs_term),
                    ),
                ))
            },
            TyKind::Sigma { tail_ty } => {
                match tail_ty.var_ty().try_prove_uninhabited() {
                    Some(head_uninhabited) => {
                        Some(Uninhabited::new(
                            self,
                            |sigma_term| head_uninhabited.contradiction(&sigma_term.proj_head()),
                        ))
                    },
                    None => {
                        let tail_uninhabited = tail_ty.try_map(|_, inner| {
                            Some(inner.try_prove_uninhabited()?.to_term())
                        })?;
                        Some(Uninhabited::new(
                            self,
                            |sigma_term| {
                                Uninhabited::from_term(&tail_uninhabited.bind(&sigma_term.proj_head()))
                                .contradiction(&sigma_term.proj_tail())
                            },
                        ))
                    },
                }
            },
            TyKind::Pi { res_ty } => {
                let arg_term = res_ty.var_ty().try_find_arbitrary_term()?;
                let res_uninhabited = res_ty.bind(&arg_term).try_prove_uninhabited()?;
                Some(Uninhabited::new(
                    self,
                    |pi_term| res_uninhabited.contradiction(&pi_term.app(&arg_term)),
                ))
            },
        }
    }

    fn try_prove_contractible(&self) -> Option<Contractible<S>> {
        match self.kind() {
            TyKind::User { .. } => None,
            TyKind::Stuck { stuck } => stuck.try_prove_contractible(),
            TyKind::Universe => None,
            TyKind::Nat => None,
            TyKind::Equal { eq_term_0, eq_term_1 } => {
                let eq_term = as_equal(eq_term_0, eq_term_1)?;
                Some(Contractible::new(
                    &eq_term.refl(),
                    |other| other.unique_identity(
                        |x, elim| elim.equals(&x.refl()),
                        |x| x.refl().refl(),
                    ),
                ))
            },
            TyKind::Never => None,
            TyKind::Unit => {
                Some(Contractible::new(
                    &self.ctx().unit_term(),
                    |unit_term| unit_term.refl(),
                ))
            },
            TyKind::Sum { lhs_ty, rhs_ty } => {
                match lhs_ty.try_prove_uninhabited() {
                    Some(lhs_uninhabited) => {
                        let rhs_contractible = rhs_ty.try_prove_contractible()?;
                        let unique_term = rhs_contractible.unique_term().inj_rhs(&lhs_ty);
                        Some(Contractible::new(
                            &unique_term,
                            |sum_term| sum_term.case(
                                |elim| elim.equals(&unique_term),
                                |lhs_term| {
                                    lhs_uninhabited
                                    .contradiction(&lhs_term)
                                    .explode(|_| lhs_term.inj_lhs(&rhs_ty).equals(&unique_term))
                                },
                                |rhs_term| {
                                    rhs_contractible
                                    .contract(&rhs_term)
                                    .map_eq(|rhs_term| rhs_term.inj_rhs(&lhs_ty))
                                },
                            ),
                        ))
                    },
                    None => {
                        let lhs_contractible = lhs_ty.try_prove_contractible()?;
                        let rhs_uninhabited = rhs_ty.try_prove_uninhabited()?;
                        let unique_term = lhs_contractible.unique_term().inj_lhs(&rhs_ty);
                        Some(Contractible::new(
                            &unique_term,
                            |sum_term| sum_term.case(
                                |elim| elim.equals(&unique_term),
                                |lhs_term| {
                                    lhs_contractible
                                    .contract(&lhs_term)
                                    .map_eq(|lhs_term| lhs_term.inj_lhs(&rhs_ty))
                                },
                                |rhs_term| {
                                    rhs_uninhabited
                                    .contradiction(&rhs_term)
                                    .explode(|_| rhs_term.inj_rhs(&lhs_ty).equals(&unique_term))
                                },
                            ),
                        ))
                    },
                }
            },
            TyKind::Sigma { tail_ty } => {
                let head_contractible = tail_ty.var_ty().try_prove_contractible()?;
                let tail_contractible = tail_ty.bind(&head_contractible.unique_term()).try_prove_contractible()?;
                let unique_term = {
                    head_contractible
                    .unique_term()
                    .pair(
                        |head_term| tail_ty.bind(&head_term),
                        &tail_contractible.unique_term(),
                    )
                };
                Some(Contractible::new(
                    &unique_term,
                    |sigma_term| {
                        head_contractible
                        .contract(&sigma_term.proj_head())
                        .pair_eq(
                            |head_term| tail_ty.bind(&head_term),
                            &sigma_term.proj_tail(),
                            &tail_contractible.unique_term(),
                            // TODO: need hetero_eq here...
                            &tail_contractible.contract(&sigma_term.proj_tail()),
                        )
                    },
                ))
            },
            TyKind::Pi { .. } => {
                // TODO
                None
            },
        }
    }

    fn simplify(&self) -> Scope<S, Tm<S>> {
        let impossible = || self.ctx().never().scope(|never| never.explode(|_| self.clone()));
        let irreducible = || self.scope(|term| term);

        match self.kind() {
            TyKind::Stuck { stuck } => stuck.simplify(),
            TyKind::User { .. } => irreducible(),
            TyKind::Universe => self.ctx().unit_ty().scope(|unit| unit.ctx().never().to_term()),
            TyKind::Nat => self.ctx().unit_ty().scope(|unit| unit.ctx().zero()),

            TyKind::Equal { eq_term_0, eq_term_1 } => {
                if let Some(eq_term) = as_equal(&eq_term_0, &eq_term_1) {
                    self.ctx().unit_ty().scope(|_| eq_term.refl())
                } else {
                    match eq_term_0.ty().kind() {
                        TyKind::Stuck { .. } => irreducible(),
                        TyKind::User { .. } => irreducible(),
                        TyKind::Universe => {
                            match (eq_term_0.to_ty().kind(), eq_term_1.to_ty().kind()) {
                                (TyKind::Stuck { .. }, _) |
                                (_, TyKind::Stuck { .. }) => irreducible(),

                                (TyKind::User { .. }, _) |
                                (_, TyKind::User { .. }) => irreducible(),

                                (TyKind::Equal { .. }, TyKind::Equal { .. }) => irreducible(),

                                (TyKind::Universe, TyKind::Universe) |
                                (TyKind::Nat, TyKind::Nat) |
                                (TyKind::Never, TyKind::Never) |
                                (TyKind::Unit, TyKind::Unit) => unreachable!(),

                                (
                                    TyKind::Sum { lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 },
                                    TyKind::Sum { lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 },
                                ) => {
                                    let lhs_ty_eq = lhs_ty_0.to_term().equals(&lhs_ty_1.to_term());
                                    let rhs_ty_eq = rhs_ty_0.to_term().equals(&rhs_ty_1.to_term());

                                    let simple_ty = lhs_ty_eq.sigma(|_| rhs_ty_eq);

                                    simple_ty
                                    .scope(|term| {
                                        term
                                        .proj_head()
                                        .cong(
                                            |lhs_ty_0, lhs_ty_1, _| {
                                                Ty::sum(&lhs_ty_0.to_ty(), &rhs_ty_0)
                                                .to_term()
                                                .equals(
                                                    &Ty::sum(&lhs_ty_1.to_ty(), &rhs_ty_1)
                                                    .to_term()
                                                )
                                            },
                                            |lhs_ty| {
                                                term
                                                .proj_tail()
                                                .cong(
                                                    |rhs_ty_0, rhs_ty_1, _| {
                                                        Ty::sum(&lhs_ty.to_ty(), &rhs_ty_0.to_ty())
                                                        .to_term()
                                                        .equals(
                                                            &Ty::sum(&lhs_ty.to_ty(), &rhs_ty_1.to_ty())
                                                            .to_term()
                                                        )
                                                    },
                                                    |rhs_ty| {
                                                        Ty::sum(&lhs_ty.to_ty(), &rhs_ty.to_ty())
                                                        .to_term()
                                                        .refl()
                                                    },
                                                )
                                            },
                                        )
                                    })
                                    .simplify_further()
                                },

                                (
                                    TyKind::Sigma { tail_ty: tail_ty_0 },
                                    TyKind::Sigma { tail_ty: tail_ty_1 },
                                ) => {
                                    let head_ty_0 = tail_ty_0.var_ty();
                                    let head_ty_1 = tail_ty_1.var_ty();

                                    let simple_ty = {
                                        head_ty_0
                                        .to_term()
                                        .equals(&head_ty_1.to_term())
                                        .sigma(|head_ty_eq| {
                                            head_ty_eq
                                            .ctx()
                                            .universe()
                                            .scope(|head_ty| head_ty.to_ty().pi(|head| head.ctx().universe()))
                                            .bind_eq(&head_ty_eq)
                                            .heterogeneous_equal(
                                                &tail_ty_0.map(|_, tail_ty| tail_ty.to_term()).to_func(),
                                                &tail_ty_1.map(|_, tail_ty| tail_ty.to_term()).to_func(),
                                            )
                                        })
                                    };

                                    simple_ty
                                    .scope(|both_eq| {
                                        both_eq
                                        .proj_head()
                                        .cong(
                                            |head_ty_0, head_ty_1, head_ty_eq| {
                                                head_ty_0
                                                .to_ty()
                                                .pi(|head| head.ctx().universe())
                                                .pi(|tail_ty_0| {
                                                    head_ty_1
                                                    .weaken_into(&tail_ty_0.ctx())
                                                    .to_ty()
                                                    .pi(|head| head.ctx().universe())
                                                    .pi(|tail_ty_1| {
                                                        tail_ty_0
                                                        .ctx()
                                                        .universe()
                                                        .scope(|head_ty| {
                                                            head_ty.to_ty().pi(|head| head.ctx().universe())
                                                        })
                                                        .bind_eq(&head_ty_eq)
                                                        .heterogeneous_equal(&tail_ty_0, &tail_ty_1)
                                                        .pi(|_| {
                                                            tail_ty_0
                                                            .to_scope()
                                                            .map(|_, tail_ty| tail_ty.to_ty())
                                                            .to_sigma()
                                                            .to_term()
                                                            .equals(
                                                                &tail_ty_1
                                                                .to_scope()
                                                                .map(|_, tail_ty| tail_ty.to_ty())
                                                                .to_sigma()
                                                                .to_term()
                                                            )
                                                        })
                                                    })
                                                })
                                            },
                                            |head_ty| {
                                                head_ty
                                                .to_ty()
                                                .pi(|head| head.ctx().universe())
                                                .func(|tail_ty_0| {
                                                    head_ty
                                                    .weaken_into(&tail_ty_0.ctx())
                                                    .to_ty()
                                                    .pi(|head| head.ctx().universe())
                                                    .func(|tail_ty_1| {
                                                        tail_ty_0
                                                        .equals(&tail_ty_1)
                                                        .func(|tail_ty_eq| {
                                                            tail_ty_eq
                                                            .cong(
                                                                |tail_ty_0, tail_ty_1, _| {
                                                                    tail_ty_0
                                                                    .to_scope()
                                                                    .map(|_, tail_ty| tail_ty.to_ty())
                                                                    .to_sigma()
                                                                    .to_term()
                                                                    .equals(
                                                                        &tail_ty_1
                                                                        .to_scope()
                                                                        .map(|_, tail_ty| tail_ty.to_ty())
                                                                        .to_sigma()
                                                                        .to_term(),
                                                                    )
                                                                },
                                                                |tail_ty| {
                                                                    tail_ty
                                                                    .to_scope()
                                                                    .map(|_, tail_ty| tail_ty.to_ty())
                                                                    .to_sigma()
                                                                    .to_term()
                                                                    .refl()
                                                                },
                                                            )
                                                        })
                                                    })
                                                })
                                            },
                                        )
                                        .app(&tail_ty_0.map(|_, tail_ty| tail_ty.to_term()).to_func())
                                        .app(&tail_ty_1.map(|_, tail_ty| tail_ty.to_term()).to_func())
                                        .app(&both_eq.proj_tail())
                                    })
                                },

                                (
                                    TyKind::Pi { res_ty: res_ty_0 },
                                    TyKind::Pi { res_ty: res_ty_1 },
                                ) => {
                                    let arg_ty_0 = res_ty_0.var_ty();
                                    let arg_ty_1 = res_ty_1.var_ty();

                                    let simple_ty = {
                                        arg_ty_0
                                        .to_term()
                                        .equals(&arg_ty_1.to_term())
                                        .sigma(|arg_ty_eq| {
                                            arg_ty_eq
                                            .ctx()
                                            .universe()
                                            .scope(|arg_ty| arg_ty.to_ty().pi(|arg| arg.ctx().universe()))
                                            .bind_eq(&arg_ty_eq)
                                            .heterogeneous_equal(
                                                &res_ty_0.map(|_, res_ty| res_ty.to_term()).to_func(),
                                                &res_ty_1.map(|_, res_ty| res_ty.to_term()).to_func(),
                                            )
                                        })
                                    };

                                    simple_ty
                                    .scope(|both_eq| {
                                        both_eq
                                        .proj_head()
                                        .cong(
                                            |arg_ty_0, arg_ty_1, arg_ty_eq| {
                                                arg_ty_0
                                                .to_ty()
                                                .pi(|arg| arg.ctx().universe())
                                                .pi(|res_ty_0| {
                                                    arg_ty_1
                                                    .weaken_into(&res_ty_0.ctx())
                                                    .to_ty()
                                                    .pi(|arg| arg.ctx().universe())
                                                    .pi(|res_ty_1| {
                                                        res_ty_0
                                                        .ctx()
                                                        .universe()
                                                        .scope(|arg_ty| {
                                                            arg_ty.to_ty().pi(|arg| arg.ctx().universe())
                                                        })
                                                        .bind_eq(&arg_ty_eq)
                                                        .heterogeneous_equal(&res_ty_0, &res_ty_1)
                                                        .pi(|_| {
                                                            res_ty_0
                                                            .to_scope()
                                                            .map(|_, res_ty| res_ty.to_ty())
                                                            .to_pi()
                                                            .to_term()
                                                            .equals(
                                                                &res_ty_1
                                                                .to_scope()
                                                                .map(|_, res_ty| res_ty.to_ty())
                                                                .to_pi()
                                                                .to_term()
                                                            )
                                                        })
                                                    })
                                                })
                                            },
                                            |arg_ty| {
                                                arg_ty
                                                .to_ty()
                                                .pi(|arg| arg.ctx().universe())
                                                .func(|res_ty_0| {
                                                    arg_ty
                                                    .weaken_into(&res_ty_0.ctx())
                                                    .to_ty()
                                                    .pi(|arg| arg.ctx().universe())
                                                    .func(|res_ty_1| {
                                                        res_ty_0
                                                        .equals(&res_ty_1)
                                                        .func(|res_ty_eq| {
                                                            res_ty_eq
                                                            .cong(
                                                                |res_ty_0, res_ty_1, _| {
                                                                    res_ty_0
                                                                    .to_scope()
                                                                    .map(|_, res_ty| res_ty.to_ty())
                                                                    .to_pi()
                                                                    .to_term()
                                                                    .equals(
                                                                        &res_ty_1
                                                                        .to_scope()
                                                                        .map(|_, res_ty| res_ty.to_ty())
                                                                        .to_pi()
                                                                        .to_term(),
                                                                    )
                                                                },
                                                                |res_ty| {
                                                                    res_ty
                                                                    .to_scope()
                                                                    .map(|_, res_ty| res_ty.to_ty())
                                                                    .to_pi()
                                                                    .to_term()
                                                                    .refl()
                                                                },
                                                            )
                                                        })
                                                    })
                                                })
                                            },
                                        )
                                        .app(&res_ty_0.map(|_, res_ty| res_ty.to_term()).to_func())
                                        .app(&res_ty_1.map(|_, res_ty| res_ty.to_term()).to_func())
                                        .app(&both_eq.proj_tail())
                                    })
                                },

                                (
                                    TyKind::Universe,
                                    TyKind::Nat |
                                    TyKind::Equal { .. } |
                                    TyKind::Never |
                                    TyKind::Unit |
                                    TyKind::Sum { .. } |
                                    TyKind::Sigma { .. } |
                                    TyKind::Pi { .. }
                                ) |
                                (
                                    TyKind::Nat,
                                    TyKind::Universe |
                                    TyKind::Equal { .. } |
                                    TyKind::Never |
                                    TyKind::Unit |
                                    TyKind::Sum { .. } |
                                    TyKind::Sigma { .. } |
                                    TyKind::Pi { .. }
                                ) |
                                (
                                    TyKind::Equal { .. },
                                    TyKind::Universe |
                                    TyKind::Nat |
                                    TyKind::Never |
                                    TyKind::Unit |
                                    TyKind::Sum { .. } |
                                    TyKind::Sigma { .. } |
                                    TyKind::Pi { .. }
                                ) |
                                (
                                    TyKind::Never,
                                    TyKind::Universe |
                                    TyKind::Nat |
                                    TyKind::Equal { .. } |
                                    TyKind::Unit |
                                    TyKind::Sum { .. } |
                                    TyKind::Sigma { .. } |
                                    TyKind::Pi { .. }
                                ) |
                                (
                                    TyKind::Unit,
                                    TyKind::Universe |
                                    TyKind::Nat |
                                    TyKind::Equal { .. } |
                                    TyKind::Never |
                                    TyKind::Sum { .. } |
                                    TyKind::Sigma { .. } |
                                    TyKind::Pi { .. }
                                ) |
                                (
                                    TyKind::Sum { .. },
                                    TyKind::Universe |
                                    TyKind::Nat |
                                    TyKind::Equal { .. } |
                                    TyKind::Never |
                                    TyKind::Unit |
                                    TyKind::Sigma { .. } |
                                    TyKind::Pi { .. }
                                ) |
                                (
                                    TyKind::Sigma { .. },
                                    TyKind::Universe |
                                    TyKind::Nat |
                                    TyKind::Equal { .. } |
                                    TyKind::Never |
                                    TyKind::Unit |
                                    TyKind::Sum { .. } |
                                    TyKind::Pi { .. }
                                ) |
                                (
                                    TyKind::Pi { .. },
                                    TyKind::Universe |
                                    TyKind::Nat |
                                    TyKind::Equal { .. } |
                                    TyKind::Never |
                                    TyKind::Unit |
                                    TyKind::Sum { .. } |
                                    TyKind::Sigma { .. }
                                ) => {
                                    impossible()
                                },
                            }
                        },

                        TyKind::Nat => {
                            match (eq_term_0.kind(), eq_term_1.kind()) {
                                (
                                    TmKind::Succs { count: count_0, pred_term: pred_term_0 },
                                    TmKind::Succs { count: count_1, pred_term: pred_term_1 },
                                ) => {
                                    let count = cmp::min(&count_0, &count_1);
                                    let diff_0 = count_0.strict_sub(&count);
                                    let diff_1 = count_1.strict_sub(&count);
                                    let term_0 = match NonZeroBigUint::new(diff_0) {
                                        None => pred_term_0,
                                        Some(count) => pred_term_0.succs(count),
                                    };
                                    let term_1 = match NonZeroBigUint::new(diff_1) {
                                        None => pred_term_1,
                                        Some(count) => pred_term_1.succs(count),
                                    };

                                    term_0
                                    .equals(&term_1)
                                    .scope(|eq| {
                                        eq
                                        .map_eq(|val| val.succs(count.clone()))
                                    })
                                },

                                (TmKind::Zero, TmKind::Succs { .. }) |
                                (TmKind::Succs { .. }, TmKind::Zero) => {
                                    impossible()
                                },
                                _ => irreducible(),
                            }
                        },

                        TyKind::Equal { .. } => {
                            self.ctx().unit_ty().scope(|_| {
                                eq_term_0.equality_contractible(&eq_term_1)
                            })
                        },

                        TyKind::Unit => unreachable!(),
                        TyKind::Never => {
                            self.ctx().unit_ty().scope(|_| {
                                eq_term_0.explode(|elim| elim.equals(&eq_term_1))
                            })
                        },
                        TyKind::Sum { lhs_ty, rhs_ty } => {
                            match (eq_term_0.kind(), eq_term_1.kind()) {
                                (
                                    TmKind::InjLhs { lhs_term: lhs_term_0, rhs_ty: _ },
                                    TmKind::InjLhs { lhs_term: lhs_term_1, rhs_ty: _ },
                                ) => {
                                    lhs_term_0
                                    .equals(&lhs_term_1)
                                    .scope(|lhs_term_eq| {
                                        lhs_term_eq.cong(
                                            |lhs_term_0, lhs_term_1, _| {
                                                lhs_term_0
                                                .inj_lhs(&rhs_ty)
                                                .equals(&lhs_term_1.inj_lhs(&rhs_ty))
                                            },
                                            |lhs_term| lhs_term.inj_lhs(&rhs_ty).refl(),
                                        )
                                    })
                                    .simplify_further()
                                },

                                (
                                    TmKind::InjRhs { rhs_term: rhs_term_0, lhs_ty: _ },
                                    TmKind::InjRhs { rhs_term: rhs_term_1, lhs_ty: _ },
                                ) => {
                                    rhs_term_0
                                    .equals(&rhs_term_1)
                                    .scope(|rhs_term_eq| {
                                        rhs_term_eq.cong(
                                            |rhs_term_0, rhs_term_1, _| {
                                                rhs_term_0
                                                .inj_rhs(&lhs_ty)
                                                .equals(&rhs_term_1.inj_rhs(&lhs_ty))
                                            },
                                            |rhs_term| rhs_term.inj_rhs(&lhs_ty).refl(),
                                        )
                                    })
                                    .simplify_further()
                                },

                                (TmKind::InjLhs { .. }, TmKind::InjRhs { .. }) |
                                (TmKind::InjRhs { .. }, TmKind::InjLhs { .. }) => {
                                    impossible()
                                },

                                _ => irreducible(),
                            }
                        },
                        TyKind::Sigma { tail_ty } => {
                            match (eq_term_0.kind(), eq_term_1.kind()) {
                                (
                                    TmKind::Pair { head_term: head_term_0, tail_term: tail_term_0, tail_ty: _ },
                                    TmKind::Pair { head_term: head_term_1, tail_term: tail_term_1, tail_ty: _ },
                                ) => {
                                    head_term_0
                                    .equals(&head_term_1)
                                    .sigma(|head_eq| {
                                        tail_ty
                                        .bind_eq(&head_eq)
                                        .heterogeneous_equal(&tail_term_0, &tail_term_1)
                                    })
                                    .scope(|both_eq| {
                                        both_eq
                                        .proj_head()
                                        .cong(
                                            |head_term_0, head_term_1, head_eq| {
                                                tail_ty
                                                .bind(&head_term_0)
                                                .pi(|tail_term_0| {
                                                    tail_ty
                                                    .weaken_into(&tail_term_0.ctx())
                                                    .bind(&head_term_1)
                                                    .pi(|tail_term_1| {
                                                        tail_ty
                                                        .weaken_into(&tail_term_1.ctx())
                                                        .bind_eq(&head_eq)
                                                        .heterogeneous_equal(&tail_term_0, &tail_term_1)
                                                        .pi(|tail_eq| {
                                                            head_term_0
                                                            .weaken_into(&tail_eq.ctx())
                                                            .pair(
                                                                |head_term_0| tail_ty.bind(&head_term_0),
                                                                &tail_term_0,
                                                            )
                                                            .equals(
                                                                &head_term_1
                                                                .weaken_into(&tail_eq.ctx())
                                                                .pair(
                                                                    |head_term_1| tail_ty.bind(&head_term_1),
                                                                    &tail_term_1,
                                                                )
                                                            )
                                                        })
                                                    })
                                                })
                                            },
                                            |head_term| {
                                                tail_ty
                                                .bind(&head_term)
                                                .func(|tail_term_0| {
                                                    tail_ty
                                                    .weaken_into(&tail_term_0.ctx())
                                                    .bind(&head_term)
                                                    .func(|tail_term_1| {
                                                        tail_term_0
                                                        .equals(&tail_term_1)
                                                        .func(|tail_eq| {
                                                            tail_eq
                                                            .cong(
                                                                |tail_term_0, tail_term_1, _| {
                                                                    head_term
                                                                    .pair(
                                                                        |head_term| tail_ty.bind(&head_term),
                                                                        &tail_term_0,
                                                                    )
                                                                    .equals(
                                                                        &head_term
                                                                        .pair(
                                                                            |head_term| tail_ty.bind(&head_term),
                                                                            &tail_term_1,
                                                                        )
                                                                    )
                                                                },
                                                                |tail_term| {
                                                                    head_term
                                                                    .pair(
                                                                        |head_term| tail_ty.bind(&head_term),
                                                                        &tail_term,
                                                                    )
                                                                    .refl()
                                                                },
                                                            )
                                                        })
                                                    })
                                                })
                                            },
                                        )
                                        .app(&tail_term_0)
                                        .app(&tail_term_1)
                                        .app(&both_eq.proj_tail())
                                    })
                                    .simplify_further()
                                },
                                _ => irreducible(),
                            }
                        },
                        TyKind::Pi { res_ty } => {
                            if let Some(res_term_0) = eq_term_0.to_scope().try_strengthen()
                            && let Some(res_term_1) = eq_term_1.to_scope().try_strengthen()
                            {
                                res_term_0
                                .equals(&res_term_1)
                                .scope(|eq| {
                                    eq
                                    .map_eq(|res_term| {
                                        res_ty
                                        .var_ty()
                                        .weaken_into(&res_term.ctx())
                                        .func(|_| res_term)
                                    })
                                })
                            } else {
                                irreducible()
                            }
                        },
                    }
                }
            },

            TyKind::Never => irreducible(),
            TyKind::Unit => irreducible(),

            TyKind::Sum { lhs_ty, rhs_ty } => {
                let lhs_scope = lhs_ty.simplify();
                let rhs_scope = rhs_ty.simplify();

                let scope = Ty::sum(&lhs_scope.var_ty(), &rhs_scope.var_ty()).scope(|sum_term| {
                    sum_term.case(
                        |_| self.clone(),
                        |lhs_term| lhs_scope.bind(&lhs_term).inj_lhs(&rhs_ty),
                        |rhs_term| rhs_scope.bind(&rhs_term).inj_rhs(&lhs_ty),
                    )
                });
                if let TyKind::Never = lhs_scope.var_ty().kind() {
                    rhs_scope
                    .var_ty()
                    .scope(|rhs_term| {
                        scope.bind(&rhs_term.inj_rhs(&rhs_term.ctx().never()))
                    })
                } else if let TyKind::Never = rhs_scope.var_ty().kind() {
                    lhs_scope
                    .var_ty()
                    .scope(|lhs_term| {
                        scope.bind(&lhs_term.inj_lhs(&lhs_term.ctx().never()))
                    })
                } else {
                    scope
                }
            },

            TyKind::Sigma { tail_ty } => {
                let head_ty = tail_ty.var_ty();
                let head_iso = head_ty.simplify_iso();
                let tail_ty = head_iso.output_ty().scope(|head| {
                    tail_ty.bind(&head_iso.rev(&head))
                });
                let scope = {
                    let iso = Iso::sigma_head_congruence(&head_iso, |head| tail_ty.bind(&head));
                    iso.output_ty().scope(|term| iso.rev(&term))
                };

                let tail_scope = tail_ty.map(|_, tail_ty| tail_ty.simplify());
                let scope = {
                    head_iso
                    .output_ty()
                    .sigma(|head| tail_scope.bind(&head).var_ty())
                    .scope(|pair_term| {
                        scope.bind(
                            &pair_term
                            .proj_head()
                            .pair(
                                |head| tail_ty.bind(&head),
                                &tail_scope.bind(&pair_term.proj_head()).bind(&pair_term.proj_tail()),
                            )
                        )
                    })
                };

                let tail_ty = tail_scope.map(|_, tail_scope| tail_scope.var_ty());
                match tail_ty.try_strengthen() {
                    Some(tail_ty) => {
                        if let TyKind::Never = tail_ty.kind() {
                            return impossible();
                        }

                        let head_scope = head_iso.output_ty().simplify();

                        if let TyKind::Never = head_scope.var_ty().kind() {
                            return impossible();
                        }

                        let scope = {
                            head_scope
                            .var_ty()
                            .sigma(|_| tail_ty.clone())
                            .scope(|pair_term| {
                                scope.bind(
                                    &head_scope
                                    .bind(&pair_term.proj_head())
                                    .pair(|_| tail_ty.clone(), &pair_term.proj_tail())
                                )
                            })
                        };

                        if let TyKind::Unit = head_scope.var_ty().kind() {
                            return tail_ty.scope(|tail_term| {
                                scope.bind(&tail_term.ctx().unit_term().pair(|_| tail_ty.clone(), &tail_term))
                            });
                        }
                        if let TyKind::Unit = tail_ty.kind() {
                            return head_scope.var_ty().scope(|head_term| {
                                scope.bind(&head_term.pair(|head| head.ctx().unit_ty(), &head_term.ctx().unit_term()))
                            });
                        }
                        scope
                    },
                    None => {
                        if let TyKind::Never = head_iso.output_ty().kind() {
                            return impossible();
                        }
                        if let Some((head_term, _proof)) = tail_ty.constrains_own_var() {
                            let scope = tail_ty.bind(&head_term).scope(|tail_term| {
                                scope.bind(&head_term.pair(|head_term| tail_ty.bind(&head_term), &tail_term))
                            });
                            return scope.simplify_further();
                        }
                        if let TyKind::Sigma { tail_ty: head_tail_ty } = head_iso.output_ty().kind() {
                            let iso = Iso::sigma_reassociate_to_tail(
                                &head_tail_ty.var_ty(),
                                |head_head| head_tail_ty.bind(&head_head),
                                |pair_term| tail_ty.bind(&pair_term),
                            );
                            let scope = iso.output_ty().scope(|term| scope.bind(&iso.rev(&term)));
                            return scope.simplify_further();
                        }
                        scope
                    },
                }
            },

            TyKind::Pi { res_ty } => {
                let arg_ty = res_ty.var_ty();
                let arg_iso = arg_ty.simplify_iso();

                let scope = {
                    arg_iso
                    .output_ty()
                    .pi(|arg_term| res_ty.bind(&arg_iso.rev(&arg_term)))
                    .scope(|pi_term| {
                        arg_iso
                        .input_ty()
                        .func(|arg_term| {
                            res_ty
                            .bind_eq(&arg_iso.fwd_rev(&arg_term))
                            .transport(
                                &pi_term.app(&arg_iso.fwd(&arg_term))
                            )
                        })
                    })
                };
                let res_ty = arg_iso.output_ty().scope(|arg_term| res_ty.bind(&arg_iso.rev(&arg_term)));

                if let TyKind::Never = arg_iso.output_ty().kind() {
                    return {
                        self
                        .ctx()
                        .unit_ty()
                        .scope(|unit| {
                            scope.bind(
                                &res_ty
                                .weaken_into(&unit.ctx())
                                .map(|arg_term, res_ty| {
                                    arg_term.explode(|_| res_ty)
                                })
                                .to_func()
                            )
                        })
                    };
                }

                let res_scope = res_ty.map(|_, res_ty| res_ty.simplify());
                let res_ty = res_scope.map(|_, res_scope| res_scope.var_ty());
                let scope = {
                    res_ty
                    .to_pi()
                    .scope(|pi_term| {
                        scope.bind(
                            &arg_iso
                            .output_ty()
                            .weaken_into(&pi_term.ctx())
                            .func(|arg_term| {
                                res_scope.bind(&arg_term).bind(&pi_term.app(&arg_term))
                            })
                        )
                    })
                };

                if let Some(res_ty) = res_ty.try_strengthen() {
                    if let TyKind::Never = res_ty.kind()
                    && let Some(_arg_term) = arg_iso.output_ty().try_find_arbitrary_term()
                    {
                        return impossible();
                    }

                    if let TyKind::Unit = res_ty.kind() {
                        return res_ty.scope(|unit| {
                            scope.bind(
                                &arg_iso
                                .output_ty()
                                .weaken_into(&unit.ctx())
                                .func(|_| unit.clone())
                            )
                        });
                    }

                    if let TyKind::Unit = arg_iso.output_ty().kind() {
                        return res_ty.scope(|term| {
                            scope.bind(
                                &term
                                .ctx()
                                .unit_ty()
                                .func(|_| term)
                            )
                        });
                    }
                } else {
                    if let Some((arg_term_0, _eq_scope)) = res_ty.constrains_own_var()
                    && let Some((_arg_term_1, _apart_scope)) = arg_term_0.try_find_alternate_term()
                    {
                        return impossible();
                    }
                }

                scope
            },
        }
    }

    fn simplify_iso(&self) -> Iso<S> {
        match self.kind() {
            TyKind::Stuck { stuck } => stuck.simplify_iso(),
            TyKind::User { .. } => self.iso_refl(),
            TyKind::Universe => self.iso_refl(),
            TyKind::Nat => self.iso_refl(),

            TyKind::Equal { eq_term_0, eq_term_1 } => {
                if let Some(eq_term) = as_equal(&eq_term_0, &eq_term_1) {
                    Iso::new(
                        self,
                        &self.ctx().unit_ty(),
                        |eq| eq.ctx().unit_term(),
                        |_| eq_term.refl(),
                        |eq| eq_term.refl().equality_contractible(&eq),
                        |unit| unit.refl(),
                    )
                } else {
                    match eq_term_0.ty().kind() {
                        TyKind::Stuck { .. } => {
                            // TODO
                            self.iso_refl()
                        },

                        TyKind::User { .. } => self.iso_refl(),

                        TyKind::Universe => {
                            let iso_0 = eq_term_0.to_ty().simplify_iso();
                            let iso_1 = eq_term_1.to_ty().simplify_iso();

                            if let TyKind::Never = iso_0.output_ty().kind()
                            && let Some(term) = iso_1.output_ty().try_find_arbitrary_term() {
                                return {
                                    self
                                    .scope(|tys_eq| {
                                        iso_0.fwd(&tys_eq.symmetry().transport(&iso_1.rev(&term)))
                                    })
                                    .scope_never_to_iso_never()
                                };
                            }

                            if let TyKind::Never = iso_1.output_ty().kind()
                            && let Some(term) = iso_0.output_ty().try_find_arbitrary_term() {
                                return {
                                    self
                                    .scope(|tys_eq| {
                                        iso_1.fwd(&tys_eq.transport(&iso_0.rev(&term)))
                                    })
                                    .scope_never_to_iso_never()
                                };
                            }

                            self.iso_refl()
                        },

                        TyKind::Nat => {
                            match (eq_term_0.kind(), eq_term_1.kind()) {
                                (
                                    TmKind::Succs { count: count_0, pred_term: pred_term_0 },
                                    TmKind::Succs { count: count_1, pred_term: pred_term_1 },
                                ) => {

                                    let count = cmp::min(&count_0, &count_1);
                                    let diff_0 = count_0.strict_sub(&count);
                                    let diff_1 = count_1.strict_sub(&count);
                                    let term_0 = match NonZeroBigUint::new(diff_0) {
                                        None => pred_term_0,
                                        Some(count) => pred_term_0.succs(count),
                                    };
                                    let term_1 = match NonZeroBigUint::new(diff_1) {
                                        None => pred_term_1,
                                        Some(count) => pred_term_1.succs(count),
                                    };

                                    Iso::new(
                                        self,
                                        &term_0.equals(&term_1),
                                        |big_eq| big_eq.nat_succs_injective(count.clone()),
                                        |small_eq| {
                                            small_eq
                                            .map_eq(|nat| nat.succs(count.clone()))
                                        },
                                        |big_eq| {
                                            big_eq
                                            .nat_succs_injective(count.clone())
                                            .map_eq(|nat| nat.succs(count.clone()))
                                            .equality_contractible(&big_eq)
                                        },
                                        |small_eq| {
                                            small_eq
                                            .map_eq(|nat| nat.succs(count.clone()))
                                            .nat_succs_injective(count.clone())
                                            .equality_contractible(&small_eq)
                                        },
                                    )
                                },

                                (TmKind::Zero, TmKind::Succs { .. }) => {
                                    self
                                    .scope(|eq| {
                                        eq
                                        .map_eq(|nat| {
                                            nat
                                            .for_loop(
                                                |elim| elim.ctx().universe(),
                                                &nat.ctx().unit_ty().to_term(),
                                                |elim, _| elim.ctx().never().to_term(),
                                            )
                                        })
                                        .transport(&eq.ctx().unit_term())
                                    })
                                    .scope_never_to_iso_never()
                                },

                                (TmKind::Succs { .. }, TmKind::Zero) => {
                                    self
                                    .scope(|eq| {
                                        eq
                                        .map_eq(|nat| {
                                            nat
                                            .for_loop(
                                                |elim| elim.ctx().universe(),
                                                &nat.ctx().never().to_term(),
                                                |elim, _| elim.ctx().unit_ty().to_term(),
                                            )
                                        })
                                        .transport(&eq.ctx().unit_term())
                                    })
                                    .scope_never_to_iso_never()
                                },

                                _ => self.iso_refl(),
                            }
                        },

                        TyKind::Equal { .. } => {
                            Iso::new(
                                self,
                                &self.ctx().unit_ty(),
                                |eqs_eq| eqs_eq.ctx().unit_term(),
                                |_| eq_term_0.equality_contractible(&eq_term_1),
                                |eqs_eq| {
                                    eq_term_0
                                    .equality_contractible(&eq_term_1)
                                    .equality_contractible(&eqs_eq)
                                },
                                |unit| unit.refl(),
                            )
                        },

                        TyKind::Never => {
                            Iso::new(
                                self,
                                &self.ctx().unit_ty(),
                                |nevers_eq| nevers_eq.ctx().unit_term(),
                                |_| eq_term_0.explode(|_| self.clone()),
                                |nevers_eq| eq_term_0.explode(|_| self.clone()).equality_contractible(&nevers_eq),
                                |unit| unit.refl(),
                            )
                        },

                        TyKind::Unit => unreachable!(),

                        TyKind::Sum { lhs_ty, rhs_ty } => {
                            match (eq_term_0.kind(), eq_term_1.kind()) {
                                (
                                    TmKind::InjLhs { lhs_term: lhs_term_0, rhs_ty: _ },
                                    TmKind::InjLhs { lhs_term: lhs_term_1, rhs_ty: _ },
                                ) => {
                                    Iso::new(
                                        self,
                                        &lhs_term_0.equals(&lhs_term_1),
                                        |sum_eq| sum_eq.case_eq(),
                                        |lhs_eq| {
                                            lhs_eq
                                            .map_eq(|lhs_term| {
                                                lhs_term.inj_lhs(&rhs_ty)
                                            })
                                        },
                                        |sum_eq| {
                                            sum_eq
                                            .case_eq()
                                            .map_eq(|lhs_term| {
                                                lhs_term.inj_lhs(&rhs_ty)
                                            })
                                            .equality_contractible(&sum_eq)
                                        },
                                        |lhs_eq| {
                                            lhs_eq
                                            .map_eq(|lhs_term| {
                                                lhs_term.inj_lhs(&rhs_ty)
                                            })
                                            .case_eq()
                                            .equality_contractible(&lhs_eq)
                                        },
                                    )
                                },
                                (
                                    TmKind::InjRhs { rhs_term: rhs_term_0, lhs_ty: _ },
                                    TmKind::InjRhs { rhs_term: rhs_term_1, lhs_ty: _ },
                                ) => {
                                    Iso::new(
                                        self,
                                        &rhs_term_0.equals(&rhs_term_1),
                                        |sum_eq| sum_eq.case_eq(),
                                        |rhs_eq| {
                                            rhs_eq
                                            .map_eq(|rhs_term| {
                                                rhs_term.inj_lhs(&lhs_ty)
                                            })
                                        },
                                        |sum_eq| {
                                            sum_eq
                                            .case_eq()
                                            .map_eq(|rhs_term| {
                                                rhs_term.inj_lhs(&lhs_ty)
                                            })
                                            .equality_contractible(&sum_eq)
                                        },
                                        |rhs_eq| {
                                            rhs_eq
                                            .map_eq(|rhs_term| {
                                                rhs_term.inj_lhs(&lhs_ty)
                                            })
                                            .case_eq()
                                            .equality_contractible(&rhs_eq)
                                        },
                                    )
                                },

                                (TmKind::InjLhs { .. }, TmKind::InjRhs { .. }) |
                                (TmKind::InjRhs { .. }, TmKind::InjLhs { .. }) => {
                                    self.scope(|sum_eq| sum_eq.case_eq()).scope_never_to_iso_never()
                                },

                                _ => self.iso_refl(),
                            }
                        },

                        TyKind::Sigma { .. } => {
                            // TODO
                            self.iso_refl()
                        },

                        TyKind::Pi { .. } => {
                            // TODO
                            self.iso_refl()
                        },
                    }
                }
            },

            TyKind::Never => self.iso_refl(),
            TyKind::Unit => self.iso_refl(),

            TyKind::Sum { lhs_ty, rhs_ty } => {
                let lhs_iso = lhs_ty.simplify_iso();
                let rhs_iso = rhs_ty.simplify_iso();

                let iso = Iso::sum_congruence(&lhs_iso, &rhs_iso);

                if let TyKind::Never = lhs_iso.output_ty().kind() {
                    return iso.transitivity(&Iso::sum_never_lhs_identity(&rhs_iso.output_ty()));
                }
                if let TyKind::Never = rhs_iso.output_ty().kind() {
                    return iso.transitivity(&Iso::sum_never_rhs_identity(&lhs_iso.output_ty()));
                }
                iso
            },

            TyKind::Sigma { tail_ty } => {
                let head_iso = tail_ty.var_ty().simplify_iso();
                let head_ty = head_iso.output_ty();
                let iso = Iso::sigma_head_congruence(&head_iso, |head| tail_ty.bind(&head));

                let tail_ty = head_ty.scope(|head| tail_ty.bind(&head_iso.rev(&head)));
                let tail_iso = tail_ty.map(|_, tail_ty| tail_ty.simplify_iso());
                let tail_ty = tail_iso.map(|_, tail_iso| tail_iso.output_ty());
                let iso = iso.transitivity(&tail_iso.sigma_tail_congruence());

                if let TyKind::Never = head_ty.kind() {
                    return iso.transitivity(
                        &Iso::sigma_never_head_annihilate(&self.ctx(), |head| tail_iso.bind(&head).output_ty()),
                    );
                }

                if let Some(strong_tail_ty) = tail_ty.try_strengthen() {
                    if let TyKind::Never = strong_tail_ty.kind() {
                        return iso.transitivity(
                            &Iso::sigma_never_tail_annihilate(&head_ty),
                        );
                    }

                    if let TyKind::Unit = head_ty.kind() {
                        return iso.transitivity(
                            &Iso::sigma_unit_head_identity(&self.ctx(), |head| tail_ty.bind(&head)),
                        );
                    }

                    if let TyKind::Unit = strong_tail_ty.kind() {
                        return iso.transitivity(
                            &Iso::sigma_unit_tail_identity(&head_ty),
                        );
                    }

                    iso
                } else {
                    if let Some((head_term, proof)) = tail_ty.constrains_own_var() {
                        return {
                            iso
                            .transitivity(&Iso::new(
                                &tail_ty.to_sigma(),
                                &tail_ty.bind(&head_term),
                                |sigma_term| {
                                    tail_ty
                                    .bind_eq(&proof.bind(&sigma_term.proj_head()).bind(&sigma_term.proj_tail()))
                                    .transport(&sigma_term.proj_tail())
                                },
                                |tail_term| head_term.pair(|head| tail_ty.bind(&head), &tail_term),
                                |sigma_term| {
                                    proof
                                    .bind(&sigma_term.proj_head())
                                    .bind(&sigma_term.proj_tail())
                                    .cong(
                                        |head_0, head_1, head_eq| {
                                            tail_ty
                                            .bind(&head_0)
                                            .pi(|tail_term| {
                                                head_1
                                                .pair(
                                                    |head| tail_ty.bind(&head),
                                                    &tail_ty.bind_eq(&head_eq).transport(&tail_term),
                                                )
                                                .equals(
                                                    &head_0
                                                    .pair(
                                                        |head| tail_ty.bind(&head),
                                                        &tail_term,
                                                    ),
                                                )
                                            })
                                        },
                                        |head| {
                                            tail_ty
                                            .bind(&head)
                                            .func(|tail_term| {
                                                head.pair(|head| tail_ty.bind(&head), &tail_term).refl()
                                            })
                                        },
                                    )
                                    .app(&sigma_term.proj_tail())
                                },
                                |tail_term| {
                                    proof
                                    .bind(&head_term)
                                    .bind(&tail_term)
                                    .unique_identity(
                                        |head, head_eq| {
                                            tail_ty
                                            .bind(&head)
                                            .pi(|tail_term| {
                                                tail_ty
                                                .bind_eq(&head_eq)
                                                .transport(&tail_term)
                                                .equals(&tail_term)
                                            })
                                        },
                                        |head| {
                                            tail_ty
                                            .bind(&head)
                                            .func(|tail_term| tail_term.refl())
                                        },
                                    )
                                    .app(&tail_term)
                                },
                            ))
                            .simplify_iso_further()
                        };
                    }

                    if tail_ty.map_out(|_, tail_ty| tail_ty.eliminates_var(self.ctx().len())) {
                        if let TyKind::Sigma { tail_ty: head_tail_ty } = head_ty.kind() {
                            return {
                                iso
                                .transitivity(&Iso::sigma_reassociate_to_tail(
                                    &head_tail_ty.var_ty(),
                                    |head_head| head_tail_ty.bind(&head_head),
                                    |head| tail_ty.bind(&head),
                                ))
                                .simplify_iso_further()
                            };
                        }
                    }

                    iso
                }
            },

            TyKind::Pi { res_ty } => {
                let arg_ty = res_ty.var_ty();
                let arg_iso = arg_ty.simplify_iso();

                let res_ty = arg_iso.output_ty().scope(|arg_term| res_ty.bind(&arg_iso.rev(&arg_term)));
                let res_iso = res_ty.map(|_, res_ty| res_ty.simplify_iso());
                
                let res_ty = res_iso.map(|_, res_iso| res_iso.output_ty());

                if let Some(res_ty) = res_ty.try_strengthen() {
                    if let TyKind::Never = res_ty.kind()
                    && let Some(arg_term) = arg_iso.output_ty().try_find_arbitrary_term()
                    {
                        return {
                            self
                            .scope(|func| {
                                res_iso.bind(&arg_term).fwd(&func.app(&arg_iso.rev(&arg_term)))
                            })
                            .scope_never_to_iso_never()
                        };
                    }
                } else {
                    if let Some((arg_term_0, eq_proof)) = res_ty.constrains_own_var()
                    && let Some((arg_term_1, apart_proof)) = arg_term_0.try_find_alternate_term()
                    {
                        return {
                            self
                            .scope(|func| {
                                apart_proof.bind(
                                    &eq_proof
                                    .bind(&arg_term_1)
                                    .bind(&res_iso.bind(&arg_term_1).fwd(&func.app(&arg_iso.rev(&arg_term_1))))
                                    .symmetry()
                                )
                            })
                            .scope_never_to_iso_never()
                        };
                    }
                }

                self.iso_refl()
            },
        }
    }

    fn constrains_var(&self, index: usize) -> Option<(Tm<S>, Scope<S, Tm<S>>)> {
        match self.kind() {
            TyKind::Stuck { stuck } => return stuck.constrains_var(index),
            TyKind::User { .. } => (),
            TyKind::Universe => (),
            TyKind::Nat => (),
            TyKind::Equal { eq_term_0, eq_term_1 } => {
                if let Some(var_index) = eq_term_0.as_var()
                && let Some(index) = as_equal(var_index, index)
                && let Some(var_term) = eq_term_1.try_strengthen_to_index(index)
                {
                    return Some((var_term, self.scope(|eq| eq)));
                }

                if let Some(var_index) = eq_term_1.as_var()
                && let Some(index) = as_equal(var_index, index)
                && let Some(var_term) = eq_term_0.try_strengthen_to_index(index)
                {
                    return Some((var_term, self.scope(|eq| eq.symmetry())));
                }
            },
            TyKind::Never => (),
            TyKind::Unit => (),
            TyKind::Sum { lhs_ty, rhs_ty } => {
                if let Some((lhs_var_term, lhs_proof)) = lhs_ty.constrains_var(index)
                && let Some((rhs_var_term, rhs_proof)) = rhs_ty.constrains_var(index)
                && let Some(var_term) = as_equal(lhs_var_term, rhs_var_term)
                {
                    let proof = self.scope(|sum_term| {
                        sum_term.case(
                            |elim| elim.ctx().var(index).equals(&var_term),
                            |lhs_term| lhs_proof.bind(&lhs_term),
                            |rhs_term| rhs_proof.bind(&rhs_term),
                        )
                    });
                    return Some((var_term, proof));
                }
            },
            TyKind::Sigma { tail_ty } => {
                if let Some((var_term, proof)) = tail_ty.var_ty().constrains_var(index) {
                    let proof = self.scope(|sigma_term| {
                        proof.bind(&sigma_term.proj_head())
                    });
                    return Some((var_term, proof));
                }

                if let Some((var_term, proof)) = tail_ty.map_out(|_, tail_ty| tail_ty.constrains_var(index)) {
                    let proof = Scope::new(proof);
                    let proof = self.scope(|sigma_term| {
                        proof.bind(&sigma_term.proj_head()).bind(&sigma_term.proj_tail())
                    });
                    return Some((var_term, proof));
                }
            },
            TyKind::Pi { res_ty } => {
                if let Some((var_term, proof)) = res_ty.map_out(|_, res_ty| res_ty.constrains_var(index)) {
                    let proof = Scope::new(proof);
                    if let Some(arg_term) = res_ty.var_ty().try_find_arbitrary_term() {
                        let proof = self.scope(|pi_term| {
                            proof.bind(&arg_term).bind(&pi_term.app(&arg_term))
                        });
                        return Some((var_term, proof));
                    }
                }
            },
        }
        None
    }
}

