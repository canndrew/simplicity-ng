use crate::priv_prelude::*;

#[extension(pub trait ScopeTmExt)]
impl<S: Scheme> Scope<S, Tm<S>> {
    fn bind_eq(&self, eq: &Tm<S>) -> Tm<S> {
        eq.map_eq(|term| self.bind(&term))
    }

    fn bind_eq_dependent(&self, eq: &Tm<S>) -> Tm<S> {
        eq.map_eq_dependent(|term| self.bind(&term))
    }

    fn scope_never_to_iso_never(&self) -> Iso<S> {
        assert!(matches!(self.map_out(|_, term| term.ty()).kind(), TyKind::Never));

        Iso::new(
            &self.var_ty(),
            &self.ctx().never(),
            |term| self.bind(&term),
            |never| never.explode(|_| self.var_ty()),
            |term| {
                self
                .bind(&term)
                .explode(|never| never.explode(|_| self.var_ty()).equals(&term))
            },
            |never| {
                never
                .explode(|never| self.bind(&never.explode(|_| self.var_ty())).equals(&never))
            },
        )
    }
}

#[extension(pub trait ScopeTyExt)]
impl<S: Scheme> Scope<S, Ty<S>> {
    fn bind_eq(&self, eq: &Tm<S>) -> Tm<S> {
        let (scope, eq) = Ctx::into_common_ctx((self, eq));
        eq
        .cong(
            |x0, x1, _| {
                scope.bind(&x0).to_term().equals(&scope.bind(&x1).to_term())
            },
            |x| scope.bind(&x).to_term().refl(),
        )
    }

    fn constrains_own_var(
        &self,
        var_name: &Name<S>,
    ) -> Option<(Tm<S>, Scope<S, Scope<S, Tm<S>>>)> {
        let (var_term, proof) = {
            self.map_out(|_, ty| ty.constrains_var(self.ctx().len(), var_name))?
        };
        let proof = Scope::new(proof);
        Some((var_term, proof))
    }

    fn try_map_functor(
        &self,
        mapping: &Scope<S, Tm<S>>,
    ) -> Option<Scope<S, Tm<S>>> {
        assert!(matches!(self.var_ty().kind(), TyKind::Universe));
        let (functor, mapping) = Ctx::into_common_ctx((self, mapping));

        let input_var_ty = mapping.var_ty();
        let output_var_ty = {
            mapping
            .map(|_, mapped| mapped.ty())
            .try_strengthen()
            .expect("mapping cannot be dependent")
        };

        if let Some(weak_ty) = functor.try_strengthen() {
            return Some(weak_ty.scope(|val| val));
        }

        match functor.map_out(|_, inner| inner.kind()) {
            TyKind::Stuck { stuck } => match stuck.kind() {
                StuckKind::Var { index } => {
                    debug_assert_eq!(index, functor.ctx().len());
                    Some(mapping.clone())
                },
                _ => {
                    // TODO
                    None
                },
            },

            TyKind::Equal { .. } => {
                // TODO
                None
            },

            TyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_name = Scope::new(lhs_name).try_strengthen()?;
                let lhs_ty = Scope::new(lhs_ty);
                let rhs_ty = Scope::new(rhs_ty);

                let lhs_scope = lhs_ty.try_map_functor(&mapping)?;
                let rhs_scope = rhs_ty.try_map_functor(&mapping)?;

                let scope = {
                    functor
                    .bind(&input_var_ty.to_term())
                    .scope(|sum_input| {
                        sum_input
                        .case(
                            |_| functor.bind(&output_var_ty.to_term()),
                            |lhs| {
                                lhs_scope
                                .bind(&lhs)
                                .inj_lhs(&lhs_name, &rhs_ty.bind(&output_var_ty.to_term()))
                            },
                            |rhs| {
                                rhs_scope
                                .bind(&rhs)
                                .inj_rhs(&lhs_name, &lhs_ty.bind(&output_var_ty.to_term()))
                            },
                        )
                    })
                };
                Some(scope)
            },

            TyKind::Sigma { head_name, tail_ty } => {
                let head_name = Scope::new(head_name).try_strengthen()?;
                let head_ty = Scope::new(tail_ty.var_ty());
                let tail_ty = Scope::new(tail_ty.try_strengthen()?);

                let head_scope = head_ty.try_map_functor(&mapping)?;
                let tail_scope = tail_ty.try_map_functor(&mapping)?;

                let scope = {
                    functor
                    .bind(&input_var_ty.to_term())
                    .scope(|pair_input| {
                        let head_input = pair_input.proj_head();
                        let tail_input = pair_input.proj_tail();

                        let head_output = head_scope.bind(&head_input);
                        let tail_output = tail_scope.bind(&tail_input);

                        head_output
                        .pair(
                            &head_name,
                            |_| tail_ty.bind(&output_var_ty.to_term()),
                            &tail_output
                        )
                    })
                };
                Some(scope)
            },

            TyKind::Pi { arg_name, res_ty } => {
                let arg_name = Scope::new(arg_name).try_strengthen()?;
                let arg_ty = Scope::new(res_ty.var_ty()).try_strengthen()?;
                let res_ty = Scope::new(res_ty.try_strengthen()?);

                let res_scope = res_ty.try_map_functor(&mapping)?;

                let scope = {
                    functor
                    .bind(&input_var_ty.to_term())
                    .scope(|func_input| {
                        arg_ty
                        .weaken_into(&func_input.ctx())
                        .func(&arg_name, |arg| {
                            res_scope.bind(&func_input.app(&arg))
                        })
                    })
                };
                Some(scope)
            },

            TyKind::Name |
            TyKind::Universe |
            TyKind::Nat |
            TyKind::Never |
            TyKind::Unit => unreachable!(),
        }
    }

    // TODO: this shouldn't need to return an option.
    fn try_map_functor_over_iso(
        &self,
        var_iso: &Iso<S>,
    ) -> Option<Iso<S>> {
        assert!(matches!(self.var_ty().kind(), TyKind::Universe));
        let (functor, var_iso) = Ctx::into_common_ctx((self, var_iso));

        if let Some(weak_ty) = functor.try_strengthen() {
            return Some(weak_ty.iso_refl());
        }

        let input_var_ty = var_iso.input_ty();
        let output_var_ty = var_iso.output_ty();

        match functor.map_out(|_, inner| inner.kind()) {
            TyKind::Stuck { stuck } => match stuck.kind() {
                StuckKind::Var { index } => {
                    debug_assert_eq!(index, functor.ctx().len());
                    Some(var_iso.clone())
                },
                _ => {
                    // TODO
                    None
                },
            },
            TyKind::Equal { .. } => {
                // TODO
                None
            },

            TyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_name = Scope::new(lhs_name);
                let lhs_ty = Scope::new(lhs_ty);
                let rhs_ty = Scope::new(rhs_ty);

                let lhs_iso = lhs_ty.try_map_functor_over_iso(&var_iso)?;
                let rhs_iso = rhs_ty.try_map_functor_over_iso(&var_iso)?;

                let input_ty = {
                    let lhs_name = lhs_name.bind(&input_var_ty.to_term());
                    let lhs_ty = lhs_ty.bind(&input_var_ty.to_term());
                    let rhs_ty = rhs_ty.bind(&input_var_ty.to_term());
                    lhs_ty.sum(&lhs_name, &rhs_ty)
                };
                let output_ty = {
                    let lhs_name = lhs_name.bind(&output_var_ty.to_term());
                    let lhs_ty = lhs_ty.bind(&output_var_ty.to_term());
                    let rhs_ty = rhs_ty.bind(&output_var_ty.to_term());
                    lhs_ty.sum(&lhs_name, &rhs_ty)
                };

                let fwd = {
                    input_ty
                    .scope(|input| {
                        input
                        .case(
                            |_| output_ty.clone(),
                            |lhs| {
                                lhs_iso
                                .fwd(&lhs)
                                .inj_lhs(
                                    &lhs_name.bind(&output_var_ty.to_term()),
                                    &rhs_ty.bind(&output_var_ty.to_term()),
                                )
                            },
                            |rhs| {
                                rhs_iso
                                .fwd(&rhs)
                                .inj_rhs(
                                    &lhs_name.bind(&output_var_ty.to_term()),
                                    &lhs_ty.bind(&output_var_ty.to_term()),
                                )
                            },
                        )
                    })
                };
                let rev = {
                    output_ty
                    .scope(|output| {
                        output
                        .case(
                            |_| input_ty.clone(),
                            |lhs| {
                                lhs_iso
                                .rev(&lhs)
                                .inj_lhs(
                                    &lhs_name.bind(&input_var_ty.to_term()),
                                    &rhs_ty.bind(&input_var_ty.to_term()),
                                )
                            },
                            |rhs| {
                                rhs_iso
                                .rev(&rhs)
                                .inj_rhs(
                                    &lhs_name.bind(&input_var_ty.to_term()),
                                    &lhs_ty.bind(&input_var_ty.to_term()),
                                )
                            },
                        )
                    })
                };

                let fwd_rev = {
                    input_ty
                    .scope(|input| {
                        input
                        .case(
                            |input| {
                                rev.bind(&fwd.bind(&input)).equals(&input)
                            },
                            |lhs| {
                                lhs_iso
                                .fwd_rev(&lhs)
                                .map_eq(|lhs| {
                                    lhs.inj_lhs(
                                        &lhs_name.bind(&input_var_ty.to_term()),
                                        &rhs_ty.bind(&input_var_ty.to_term()),
                                    )
                                })
                            },
                            |rhs| {
                                rhs_iso
                                .fwd_rev(&rhs)
                                .map_eq(|rhs| {
                                    rhs.inj_rhs(
                                        &lhs_name.bind(&input_var_ty.to_term()),
                                        &lhs_ty.bind(&input_var_ty.to_term()),
                                    )
                                })
                            },
                        )
                    })
                };

                let rev_fwd = {
                    output_ty
                    .scope(|output| {
                        output
                        .case(
                            |output| {
                                fwd.bind(&rev.bind(&output)).equals(&output)
                            },
                            |lhs| {
                                lhs_iso
                                .rev_fwd(&lhs)
                                .map_eq(|lhs| {
                                    lhs.inj_lhs(
                                        &lhs_name.bind(&output_var_ty.to_term()),
                                        &rhs_ty.bind(&output_var_ty.to_term()),
                                    )
                                })
                            },
                            |rhs| {
                                rhs_iso
                                .rev_fwd(&rhs)
                                .map_eq(|rhs| {
                                    rhs.inj_rhs(
                                        &lhs_name.bind(&output_var_ty.to_term()),
                                        &lhs_ty.bind(&output_var_ty.to_term()),
                                    )
                                })
                            },
                        )
                    })
                };

                Some(Iso::new(
                    &input_ty,
                    &output_ty,
                    fwd.unbind(),
                    rev.unbind(),
                    fwd_rev.unbind(),
                    rev_fwd.unbind(),
                ))
            },

            _ => {
                // TODO
                None
            },
        }
    }
}

