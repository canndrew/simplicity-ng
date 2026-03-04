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
            TyKind::Stuck { stuck } => stuck.try_find_arbitrary_term(),
            TyKind::Name => {
                let name = S::name_from_str("arbitrary");
                Some(name.weaken_into(&self.ctx()).to_term())
            },
            TyKind::Universe => Some(self.ctx().universe().to_term()),
            TyKind::Nat => Some(self.ctx().zero()),
            TyKind::Equal { .. } => None,
            TyKind::Never => None,
            TyKind::Unit => Some(self.ctx().unit_term()),
            TyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                match lhs_ty.try_find_arbitrary_term() {
                    Some(lhs_term) => {
                        Some(lhs_term.inj_lhs(&lhs_name, &rhs_ty))
                    },
                    None => {
                        let rhs_term = rhs_ty.try_find_arbitrary_term()?;
                        Some(rhs_term.inj_rhs(&lhs_name, &lhs_ty))
                    },
                }
            },
            TyKind::Sigma { head_name, tail_ty } => {
                let head_term = tail_ty.var_ty().try_find_arbitrary_term()?;
                let tail_term = tail_ty.bind(&head_term).try_find_arbitrary_term()?;
                Some(head_term.pair(
                    &head_name,
                    |head_term| tail_ty.bind(&head_term),
                    &tail_term,
                ))
            },
            TyKind::Pi { arg_name, res_ty } => {
                let res_term = res_ty.try_map(|_, inner| inner.try_find_arbitrary_term())?;
                Some(res_term.to_func(&arg_name))
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
            TyKind::Stuck { stuck } => stuck.try_prove_uninhabited(),
            TyKind::Name => None,
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
            TyKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
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
            TyKind::Sigma { head_name: _, tail_ty } => {
                match tail_ty.var_ty().try_prove_uninhabited() {
                    Some(head_uninhabited) => {
                        Some(Uninhabited::new(
                            self,
                            |sigma_term| head_uninhabited.contradiction(&sigma_term.proj_head()),
                        ))
                    },
                    None => {
                        let tail_uninhabited = tail_ty.try_map(|_, inner| {
                            Some(inner.try_prove_uninhabited()?)
                        })?;
                        Some(Uninhabited::new(
                            self,
                            |sigma_term| {
                                tail_uninhabited
                                .bind(&sigma_term.proj_head())
                                .contradiction(&sigma_term.proj_tail())
                            },
                        ))
                    },
                }
            },
            TyKind::Pi { arg_name: _, res_ty } => {
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
            TyKind::Stuck { stuck } => stuck.try_prove_contractible(),
            TyKind::Name => None,
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
            TyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                match lhs_ty.try_prove_uninhabited() {
                    Some(lhs_uninhabited) => {
                        let rhs_contractible = rhs_ty.try_prove_contractible()?;
                        let unique_term = rhs_contractible.unique_term().inj_rhs(&lhs_name, &lhs_ty);
                        Some(Contractible::new(
                            &unique_term,
                            |sum_term| sum_term.case(
                                |elim| elim.equals(&unique_term),
                                |lhs_term| {
                                    lhs_uninhabited
                                    .contradiction(&lhs_term)
                                    .explode(|_| lhs_term.inj_lhs(&lhs_name, &rhs_ty).equals(&unique_term))
                                },
                                |rhs_term| {
                                    rhs_contractible
                                    .contract(&rhs_term)
                                    .map_eq(|rhs_term| rhs_term.inj_rhs(&lhs_name, &lhs_ty))
                                },
                            ),
                        ))
                    },
                    None => {
                        let lhs_contractible = lhs_ty.try_prove_contractible()?;
                        let rhs_uninhabited = rhs_ty.try_prove_uninhabited()?;
                        let unique_term = lhs_contractible.unique_term().inj_lhs(&lhs_name, &rhs_ty);
                        Some(Contractible::new(
                            &unique_term,
                            |sum_term| sum_term.case(
                                |elim| elim.equals(&unique_term),
                                |lhs_term| {
                                    lhs_contractible
                                    .contract(&lhs_term)
                                    .map_eq(|lhs_term| lhs_term.inj_lhs(&lhs_name, &rhs_ty))
                                },
                                |rhs_term| {
                                    rhs_uninhabited
                                    .contradiction(&rhs_term)
                                    .explode(|_| rhs_term.inj_rhs(&lhs_name, &lhs_ty).equals(&unique_term))
                                },
                            ),
                        ))
                    },
                }
            },
            TyKind::Sigma { head_name: _, tail_ty: _ } => {
                // TODO: fix this
                None
                /*
                let head_contractible = tail_ty.var_ty().try_prove_contractible()?;
                let tail_contractible = tail_ty.bind(&head_contractible.unique_term()).try_prove_contractible()?;
                let unique_term = {
                    head_contractible
                    .unique_term()
                    .pair(
                        &head_name,
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
                */
            },
            TyKind::Pi { .. } => {
                // TODO
                None
            },
        }
    }

    fn constrains_var(
        &self,
        index: usize,
        var_name: &Name<S>,
    ) -> Option<(Tm<S>, Scope<S, Tm<S>>)> {
        match self.kind() {
            TyKind::Stuck { stuck } => return stuck.constrains_var(index, var_name),
            TyKind::Name => (),
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
            TyKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                if let Some((lhs_var_term, lhs_proof)) = lhs_ty.constrains_var(index, var_name)
                && let Some((rhs_var_term, rhs_proof)) = rhs_ty.constrains_var(index, var_name)
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
            TyKind::Sigma { head_name: _, tail_ty } => {
                if let Some((var_term, proof)) = tail_ty.var_ty().constrains_var(index, var_name) {
                    let proof = self.scope(|sigma_term| {
                        proof.bind(&sigma_term.proj_head())
                    });
                    return Some((var_term, proof));
                }

                if let Some((var_term, proof)) = tail_ty.map_out(|_, tail_ty| tail_ty.constrains_var(index, var_name)) {
                    let proof = Scope::new(proof);
                    let proof = self.scope(|sigma_term| {
                        proof.bind(&sigma_term.proj_head()).bind(&sigma_term.proj_tail())
                    });
                    return Some((var_term, proof));
                }
            },
            TyKind::Pi { arg_name: _, res_ty } => {
                if let Some((var_term, proof)) = res_ty.map_out(|_, res_ty| res_ty.constrains_var(index, var_name)) {
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

    fn scoped_tys_equal(
        var_names_eq: &Tm<S>,
        var_tys_eq: &Tm<S>,
        body_ty_0: impl FnOnce(Tm<S>) -> Ty<S>,
        body_ty_1: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Ty<S> {
        same_ctx!(var_names_eq, var_tys_eq);

        let (var_name_0, var_name_1) = var_names_eq.ty().unwrap_equal();
        let var_name_0 = var_name_0.to_name();
        let var_name_1 = var_name_1.to_name();

        let (var_ty_0, var_ty_1) = var_tys_eq.ty().unwrap_equal();
        let var_ty_0 = var_ty_0.to_ty();
        let var_ty_1 = var_ty_1.to_ty();

        let body_ty_0 = var_ty_0.scope(body_ty_0);
        let body_ty_1 = var_ty_1.scope(body_ty_1);

        let body_name_0 = S::name_from_str("Body0");
        let body_name_1 = S::name_from_str("Body1");

        var_names_eq
        .cong(
            |var_name_0, var_name_1, _| {
                let var_name_0 = var_name_0.to_name();
                let var_name_1 = var_name_1.to_name();

                var_ty_0
                .pi(&var_name_0, |var_0| var_0.ctx().universe())
                .pi(&body_name_0, |body_ty_0| {
                    var_ty_1
                    .weaken_into(&body_ty_0.ctx())
                    .pi(&var_name_1, |var_1| var_1.ctx().universe())
                    .pi(&body_name_1, |body_ty_1| {
                        body_ty_1.ctx().universe()
                    })
                })
            },
            |var_name| {
                let var_name = var_name.to_name();

                var_tys_eq
                .weaken_into(&var_name.ctx())
                .cong(
                    |var_ty_0, var_ty_1, _| {
                        let var_ty_0 = var_ty_0.to_ty();
                        let var_ty_1 = var_ty_1.to_ty();

                        var_ty_0
                        .pi(&var_name, |var_0| var_0.ctx().universe())
                        .pi(&body_name_0, |body_ty_0| {
                            var_ty_1
                            .weaken_into(&body_ty_0.ctx())
                            .pi(&var_name, |var_1| var_1.ctx().universe())
                            .pi(&body_name_1, |body_ty_1| {
                                body_ty_1.ctx().universe()
                            })
                        })
                    },
                    |var_ty| {
                        let var_ty = var_ty.to_ty();

                        var_ty
                        .pi(&var_name, |var| var.ctx().universe())
                        .func(&body_name_0, |body_ty_0| {
                            var_ty
                            .weaken_into(&body_ty_0.ctx())
                            .pi(&var_name, |var| var.ctx().universe())
                            .func(&body_name_1, |body_ty_1| {
                                body_ty_0.equals(&body_ty_1).to_term()
                            })
                        })
                    },
                )
            },
        )
        .app(&var_ty_0.func(&var_name_0, |var_0| body_ty_0.bind(&var_0).to_term()))
        .app(&var_ty_1.func(&var_name_1, |var_1| body_ty_1.bind(&var_1).to_term()))
        .to_ty()
    }

    /*
    fn try_map_functor(
        &self,
        var_ty_index: usize,
    */

}

