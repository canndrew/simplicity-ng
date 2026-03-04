use crate::priv_prelude::*;

#[extension(trait CtxTestExt)]
impl Ctx<StringScheme> {
    fn with_funext<T>(
        &self,
        func: impl FnOnce(Tm<StringScheme>) -> T,
    ) -> T {
        self
        .function_extensionality_ty()
        .with_cons(func)
    }

    fn with_iso<T>(
        &self,
        func: impl FnOnce(Iso<StringScheme>) -> T,
    ) -> T {
        self
        .with_names(|[input_name, output_name]| {
            input_name
            .ctx()
            .with_tys(|[input_ty, output_ty]| {
                input_ty
                .ctx()
                .with_iso_between(
                    &input_name,
                    &output_name,
                    &input_ty,
                    &output_ty,
                    func,
                )
            })
        })
    }

    fn with_iso_between<T>(
        &self,
        input_name: &Name<StringScheme>,
        output_name: &Name<StringScheme>,
        input_ty: &Ty<StringScheme>,
        output_ty: &Ty<StringScheme>,
        func: impl FnOnce(Iso<StringScheme>) -> T,
    ) -> T {
        let input_name = input_name.weaken_into(self);
        let output_name = output_name.weaken_into(self);
        let input_ty = input_ty.weaken_into(self);
        let output_ty = output_ty.weaken_into(self);

        input_ty
        .pi(&input_name, |_| output_ty.clone())
        .with_cons(|fwd| {
            same_ctx!(&output_ty, &fwd);

            output_ty
            .pi(&output_name, |_| input_ty.clone())
            .with_cons(|rev| {
                same_ctx!(&input_ty, &rev);

                input_ty
                .pi(&input_name, |input| {
                    rev.app(&fwd.app(&input)).equals(&input)
                })
                .with_cons(|fwd_rev| {
                    same_ctx!(&output_ty, &fwd_rev);

                    output_ty
                    .pi(&output_name, |output| {
                        fwd.app(&rev.app(&output)).equals(&output)
                    })
                    .with_cons(|rev_fwd| {
                        same_ctx!(&input_ty, &output_ty, &fwd, &rev, &fwd_rev, &rev_fwd);

                        let iso = Iso::new(
                            &input_ty,
                            &output_ty,
                            |input| fwd.app(&input),
                            |output| rev.app(&output),
                            |input| fwd_rev.app(&input),
                            |output| rev_fwd.app(&output),
                        );
                        func(iso)
                    })
                })
            })
        })
    }

    fn with_dependent_iso_between<T>(
        &self,
        var_name: &Name<StringScheme>,
        var_ty: &Ty<StringScheme>,
        input_name: &Name<StringScheme>,
        output_name: &Name<StringScheme>,
        input_ty: impl FnOnce(Tm<StringScheme>) -> Ty<StringScheme>,
        output_ty: impl FnOnce(Tm<StringScheme>) -> Ty<StringScheme>,
        func: impl FnOnce(Scope<StringScheme, Iso<StringScheme>>) -> T,
    ) -> T {
        let var_name = var_name.weaken_into(self);
        let var_ty = var_ty.weaken_into(self);
        let input_name = input_name.weaken_into(self);
        let output_name = output_name.weaken_into(self);

        let input_ty = var_ty.scope(input_ty);
        let output_ty = var_ty.scope(output_ty);

        var_ty
        .pi(&var_name, |var| {
            input_ty
            .bind(&var)
            .pi(&input_name, |_| {
                output_ty.bind(&var)
            })
        })
        .with_cons(|fwd| {
            same_ctx!(&var_ty, &fwd);

            var_ty
            .pi(&var_name, |var| {
                output_ty
                .bind(&var)
                .pi(&output_name, |_| {
                    input_ty.bind(&var)
                })
            })
            .with_cons(|rev| {
                same_ctx!(&var_ty, &fwd, &rev);

                var_ty
                .pi(&var_name, |var| {
                    input_ty
                    .bind(&var)
                    .pi(&input_name, |input| {
                        rev
                        .app(&var)
                        .app(&fwd.app(&var).app(&input))
                        .equals(&input)
                    })
                })
                .with_cons(|fwd_rev| {
                    same_ctx!(&var_ty, &fwd, &rev, &fwd_rev);

                    var_ty
                    .pi(&var_name, |var| {
                        output_ty
                        .bind(&var)
                        .pi(&output_name, |output| {
                            fwd
                            .app(&var)
                            .app(&rev.app(&var).app(&output))
                            .equals(&output)
                        })
                    })
                    .with_cons(|rev_fwd| {
                        same_ctx!(&var_ty, &fwd, &rev, &fwd_rev, &rev_fwd);
                        
                        let iso = var_ty.scope(|var| {
                            Iso::new(
                                &input_ty.bind(&var),
                                &output_ty.bind(&var),
                                |input| fwd.app(&var).app(&input),
                                |output| rev.app(&var).app(&output),
                                |input| fwd_rev.app(&var).app(&input),
                                |output| rev_fwd.app(&var).app(&output),
                            )
                        });
                        func(iso)
                    })
                })
            })
        })
    }
}

#[test]
fn symmetry() {
    Ctx::root()
    .with_iso(|iso| {
        let new_iso = iso.symmetry();
        assert_eq!(new_iso.input_ty(), iso.output_ty());
        assert_eq!(new_iso.output_ty(), iso.input_ty());
    });
}

#[test]
fn transitivity() {
    Ctx::root()
    .with_names(|[input_name, middle_name, output_name]| {
        input_name
        .ctx()
        .with_tys(|[input_ty, middle_ty, output_ty]| {
            input_ty
            .ctx()
            .with_iso_between(
                &input_name, &middle_name, &input_ty, &middle_ty,
                |iso_0| {
                    iso_0
                    .ctx()
                    .with_iso_between(
                        &middle_name, &output_name, &middle_ty, &output_ty,
                        |iso_1| {
                            let new_iso = iso_0.transitivity(&iso_1);
                            assert_eq!(new_iso.input_ty(), iso_0.input_ty());
                            assert_eq!(new_iso.output_ty(), iso_1.output_ty());
                        },
                    )
                },
            )
        })
    })
}

#[test]
fn sum_congruence() {
    Ctx::root()
    .with_names(|[input_lhs_name, output_lhs_name, input_name, output_name]| {
        input_lhs_name
        .ctx()
        .with_tys(|[input_lhs_ty, input_rhs_ty, output_lhs_ty, output_rhs_ty]| {
            input_lhs_ty
            .ctx()
            .with_iso_between(
                &input_lhs_name, &output_lhs_name, &input_lhs_ty, &output_lhs_ty,
                |lhs_iso| {
                    lhs_iso
                    .ctx()
                    .with_iso_between(
                        &input_name, &output_name, &input_rhs_ty, &output_rhs_ty,
                        |rhs_iso| {
                            let new_iso = Iso::sum_congruence(
                                &input_lhs_name, &output_lhs_name, &lhs_iso, &rhs_iso,
                            );
                            assert_eq!(
                                new_iso.input_ty(),
                                input_lhs_ty.sum(&input_lhs_name, &input_rhs_ty),
                            );
                            assert_eq!(
                                new_iso.output_ty(),
                                output_lhs_ty.sum(&output_lhs_name, &output_rhs_ty),
                            );
                        },
                    )
                },
            )
        })
    })
}

#[test]
fn sigma_head_congruence() {
    Ctx::root()
    .with_names(|[input_head_name, output_head_name, tail_name]| {
        input_head_name
        .ctx()
        .with_tys(|[input_head_ty, output_head_ty]| {
            input_head_ty
            .pi(&input_head_name, |head| head.ctx().universe())
            .with_cons(|tail_ty| {
                let input_head_ty = input_head_ty.weaken_into(&tail_ty.ctx());
                let tail_ty = input_head_ty.scope(|head| tail_ty.app(&head).to_ty());
                tail_ty
                .ctx()
                .with_iso_between(
                    &input_head_name, &output_head_name, &input_head_ty, &output_head_ty,
                    |head_iso| {
                        same_ctx!(&input_head_ty, &output_head_ty, &head_iso, &tail_ty);
                        let new_iso = Iso::sigma_head_congruence(
                            &input_head_name,
                            &output_head_name,
                            &head_iso,
                            tail_ty.unbind(),
                            &tail_name,
                        );
                        assert_eq!(
                            new_iso.input_ty(),
                            input_head_ty.sigma(&input_head_name, tail_ty.unbind()),
                        );
                        assert_eq!(
                            new_iso.output_ty(),
                            output_head_ty.sigma(
                                &output_head_name,
                                |head| tail_ty.bind(&head_iso.rev(&head)),
                            ),
                        );
                    },
                )
            })
        })
    })
}

#[test]
fn sigma_tail_congruence() {
    let ctx = Ctx::<StringScheme>::root();
    
    ctx
    .with_names(|[head_name, input_name, output_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            head_ty
            .pi(&head_name, |head| head.ctx().universe())
            .with_cons(|input_tail_ty| {
                same_ctx!(&head_ty, &input_tail_ty);
                let input_tail_ty = head_ty.scope(|head| input_tail_ty.app(&head).to_ty());

                head_ty
                .pi(&head_name, |head| head.ctx().universe())
                .with_cons(|output_tail_ty| {
                    same_ctx!(&head_ty, &output_tail_ty);
                    let output_tail_ty = head_ty.scope(|head| output_tail_ty.app(&head).to_ty());

                    output_tail_ty
                    .ctx()
                    .with_dependent_iso_between(
                        &head_name,
                        &head_ty,
                        &input_name,
                        &output_name,
                        input_tail_ty.unbind(),
                        output_tail_ty.unbind(),
                        |tail_iso| {
                            same_ctx!(&head_name, &head_ty, &tail_iso);

                            let iso = Iso::sigma_tail_congruence(
                                &head_name,
                                &head_ty,
                                tail_iso.unbind(),
                            );

                            assert_eq!(
                                iso.input_ty(),
                                head_ty.sigma(&head_name, input_tail_ty.unbind()),
                            );
                            assert_eq!(
                                iso.output_ty(),
                                head_ty.sigma(&head_name, output_tail_ty.unbind()),
                            );
                        },
                    )
                })
            })
        })
    })
}

#[test]
fn sum_never_lhs() {
    Ctx::<StringScheme>::root()
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[rhs_ty]| {
            let iso = Iso::sum_never_lhs(&lhs_name, &rhs_ty);
            assert_eq!(iso.input_ty(), rhs_ty.ctx().never().sum(&lhs_name, &rhs_ty));
            assert_eq!(iso.output_ty(), rhs_ty);
        })
    })
}


#[test]
fn sum_never_rhs() {
    Ctx::<StringScheme>::root()
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty]| {
            let iso = Iso::sum_never_rhs(&lhs_name, &lhs_ty);
            assert_eq!(iso.input_ty(), lhs_ty.sum(&lhs_name, &lhs_ty.ctx().never()));
            assert_eq!(iso.output_ty(), lhs_ty);
        })
    })
}

#[test]
fn sigma_unit_head() {
    Ctx::<StringScheme>::root()
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .unit_ty()
        .pi(&head_name, |head| head.ctx().universe())
        .with_cons(|tail_ty| {
            same_ctx!(&head_name, &tail_ty);
            let tail_ty = tail_ty.ctx().unit_ty().scope(|head| tail_ty.app(&head).to_ty());
            let iso = Iso::sigma_unit_head(&head_name, tail_ty.unbind());
            assert_eq!(
                iso.input_ty(),
                tail_ty.ctx().unit_ty().sigma(&head_name, tail_ty.unbind()),
            );
            assert_eq!(
                iso.output_ty(),
                tail_ty.bind(&tail_ty.ctx().unit_term()),
            );
        })
    })
}

#[test]
fn sigma_unit_tail() {
    Ctx::<StringScheme>::root()
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            same_ctx!(&head_name, &head_ty);
            let iso = Iso::sigma_unit_tail(&head_name, &head_ty);
            assert_eq!(
                iso.input_ty(),
                head_ty.sigma(&head_name, |head| head.ctx().unit_ty()),
            );
            assert_eq!(
                iso.output_ty(),
                head_ty,
            );
        })
    })
}

#[test]
fn sigma_never_head() {
    Ctx::<StringScheme>::root()
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .never()
        .pi(&head_name, |head| head.ctx().universe())
        .with_cons(|tail_ty| {
            same_ctx!(&head_name, &tail_ty);
            let tail_ty = tail_ty.ctx().never().scope(|head| tail_ty.app(&head).to_ty());
            let iso = Iso::sigma_never_head(&head_name, tail_ty.unbind());
            assert_eq!(
                iso.input_ty(),
                tail_ty.ctx().never().sigma(&head_name, tail_ty.unbind()),
            );
            assert_eq!(
                iso.output_ty(),
                tail_ty.ctx().never(),
            );
        })
    })
}

#[test]
fn sigma_never_tail() {
    Ctx::<StringScheme>::root()
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            same_ctx!(&head_name, &head_ty);
            let iso = Iso::sigma_never_tail(&head_name, &head_ty);
            assert_eq!(
                iso.input_ty(),
                head_ty.sigma(&head_name, |head| head.ctx().never()),
            );
            assert_eq!(
                iso.output_ty(),
                head_ty.ctx().never(),
            );
        })
    })
}

#[test]
fn sigma_reassociate_to_tail() {
    Ctx::<StringScheme>::root()
    .with_names(|[head_name, head_head_name]| {
        head_head_name
        .ctx()
        .with_tys(|[head_head_ty]| {
            head_head_ty
            .pi(&head_head_name, |head_head| head_head.ctx().universe())
            .with_cons(|head_tail_ty| {
                same_ctx!(&head_head_ty, &head_tail_ty);
                let head_tail_ty = {
                    head_head_ty
                    .scope(|head_head| head_tail_ty.app(&head_head).to_ty())
                };
                let head_ty = head_tail_ty.to_sigma(&head_head_name);
                
                head_ty
                .pi(&head_name, |head| head.ctx().universe())
                .with_cons(|tail_ty| {
                    same_ctx!(&head_head_ty, &head_tail_ty, &head_ty, &tail_ty);
                    let tail_ty = head_ty.scope(|head| tail_ty.app(&head).to_ty());
                    let iso = Iso::sigma_reassociate_to_tail(
                        &head_name,
                        &head_head_name,
                        &head_head_ty,
                        head_tail_ty.unbind(),
                        tail_ty.unbind(),
                    );
                    assert_eq!(
                        iso.input_ty(),
                        tail_ty.to_sigma(&head_name),
                    );
                    assert_eq!(
                        iso.output_ty(),
                        head_head_ty
                        .sigma(&head_head_name, |head_head| {
                            same_ctx!(&head_tail_ty, &head_head);
                            head_tail_ty
                            .bind(&head_head)
                            .sigma(&head_name, |head_tail| {
                                tail_ty
                                .bind(
                                    &head_head
                                    .pair(&head_head_name, head_tail_ty.unbind(), &head_tail)
                                )
                            })
                        })
                    );
                })
            })
        })
    })
}

#[test]
fn sigma_tail_ty_constrains_head_ty() {
    Ctx::<StringScheme>::root()
    .with_names(|[head_name, tail_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            head_ty
            .pi(&head_name, |head| head.ctx().universe())
            .with_cons(|tail_ty| {
                same_ctx!(&head_ty, &tail_ty);
                let tail_ty = head_ty.scope(|head| tail_ty.app(&head).to_ty());
                head_ty
                .with_cons(|unique_head| {
                    same_ctx!(&head_ty, &unique_head);
                    head_ty
                    .pi(&head_name, |head| {
                        tail_ty
                        .bind(&head)
                        .pi(&tail_name, |_| head.equals(&unique_head))
                    })
                    .with_cons(|proof| {
                        same_ctx!(&head_name, &tail_ty, &unique_head, &proof, &tail_name);
                        let iso = Iso::sigma_tail_ty_constrains_head_ty(
                            &head_name,
                            tail_ty.unbind(),
                            &unique_head,
                            |head, tail| proof.app(&head).app(&tail),
                            &tail_name,
                        );
                        assert_eq!(
                            iso.input_ty(),
                            head_ty.sigma(&head_name, tail_ty.unbind()),
                        );
                        assert_eq!(
                            iso.output_ty(),
                            tail_ty.bind(&unique_head),
                        );
                    })
                })
            })
        })
    })
}

#[test]
fn nat_is_zero_or_succ() {
    let zero_name = StringScheme::name_from_str("zero");
    let ctx = Ctx::root();
    let iso = Iso::nat_is_zero_or_succ(&ctx);
    assert_eq!(
        iso.input_ty(),
        ctx.nat(),
    );
    assert_eq!(
        iso.output_ty(),
        ctx.unit_ty().sum(&zero_name, &ctx.nat()),
    );
}

#[test]
fn pi_sigma_arg() {
    Ctx::<StringScheme>::root()
    .with_names(|[arg_name, head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            head_ty
            .pi(&head_name, |head| head.ctx().universe())
            .with_cons(|tail_ty| {
                let head_ty = head_ty.weaken_into(&tail_ty.ctx());
                let tail_ty = head_ty.scope(|head| tail_ty.app(&head).to_ty());
                let sigma_ty = tail_ty.to_sigma(&head_name);

                sigma_ty
                .pi(&arg_name, |pair| pair.ctx().universe())
                .with_cons(|res_ty| {
                    same_ctx!(&arg_name, &head_name, &head_ty, &tail_ty, &sigma_ty, &res_ty);
                    let res_ty = sigma_ty.scope(|pair| res_ty.app(&pair).to_ty());

                    let iso = Iso::pi_sigma_arg(
                        &arg_name,
                        &head_name,
                        &head_ty,
                        tail_ty.unbind(),
                        res_ty.unbind(),
                    );
                    assert_eq!(
                        iso.input_ty(),
                        res_ty.to_pi(&arg_name),
                    );
                    assert_eq!(
                        iso.output_ty(),
                        head_ty.pi(&head_name, |head| {
                            tail_ty
                            .bind(&head)
                            .pi(&arg_name, |tail| {
                                res_ty
                                .bind(&head.pair(&head_name, tail_ty.unbind(), &tail))
                            })
                        }),
                    );
                })
            })
        })
    })
}

#[test]
fn pi_unit_arg() {
    Ctx::<StringScheme>::root()
    .with_names(|[arg_name]| {
        arg_name
        .ctx()
        .unit_ty()
        .pi(&arg_name, |unit| unit.ctx().universe())
        .with_cons(|res_ty| {
            same_ctx!(&arg_name, &res_ty);
            let res_ty = res_ty.ctx().unit_ty().scope(|unit| res_ty.app(&unit).to_ty());

            let iso = Iso::pi_unit_arg(&arg_name, res_ty.unbind());
            assert_eq!(
                iso.input_ty(),
                res_ty.to_pi(&arg_name),
            );
            assert_eq!(
                iso.output_ty(),
                res_ty.bind(&res_ty.ctx().unit_term()),
            );
        })
    })
}

#[test]
fn pi_unit_res() {
    Ctx::<StringScheme>::root()
    .with_names(|[arg_name]| {
        arg_name
        .ctx()
        .with_tys(|[arg_ty]| {
            same_ctx!(&arg_name, &arg_ty);
            let iso = Iso::pi_unit_res(&arg_name, &arg_ty);
            assert_eq!(
                iso.input_ty(),
                arg_ty.pi(&arg_name, |arg| arg.ctx().unit_ty()),
            );
            assert_eq!(
                iso.output_ty(),
                arg_ty.ctx().unit_ty(),
            );
        })
    })
}

#[test]
fn pi_never_arg() {
    Ctx::<StringScheme>::root()
    .with_funext(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name]| {
            arg_name
            .ctx()
            .never()
            .pi(&arg_name, |never| never.ctx().universe())
            .with_cons(|res_ty| {
                same_ctx!(&arg_name, &res_ty);
                let res_ty = res_ty.ctx().never().scope(|unit| res_ty.app(&unit).to_ty());

                let iso = Iso::pi_never_arg(&arg_name, res_ty.unbind(), &funext);
                assert_eq!(
                    iso.input_ty(),
                    res_ty.to_pi(&arg_name),
                );
                assert_eq!(
                    iso.output_ty(),
                    res_ty.ctx().unit_ty(),
                );
            })
        })
    })
}

#[test]
fn pi_arg_congruence() {
    Ctx::root()
    .with_funext(|funext| {
        funext
        .ctx()
        .with_names(|[input_arg_name, output_arg_name]| {
            input_arg_name
            .ctx()
            .with_tys(|[input_arg_ty, output_arg_ty]| {
                input_arg_ty
                .pi(&input_arg_name, |arg| arg.ctx().universe())
                .with_cons(|res_ty| {
                    let input_arg_ty = input_arg_ty.weaken_into(&res_ty.ctx());
                    let res_ty = input_arg_ty.scope(|arg| res_ty.app(&arg).to_ty());
                    res_ty
                    .ctx()
                    .with_iso_between(
                        &input_arg_name, &output_arg_name, &input_arg_ty, &output_arg_ty,
                        |arg_iso| {
                            same_ctx!(&input_arg_ty, &output_arg_ty, &arg_iso, &res_ty);
                            let new_iso = Iso::pi_arg_congruence(
                                &input_arg_name,
                                &output_arg_name,
                                &arg_iso,
                                res_ty.unbind(),
                                &funext,
                            );
                            assert_eq!(
                                new_iso.input_ty(),
                                input_arg_ty.pi(&input_arg_name, res_ty.unbind()),
                            );
                            assert_eq!(
                                new_iso.output_ty(),
                                output_arg_ty.pi(
                                    &output_arg_name,
                                    |arg| res_ty.bind(&arg_iso.rev(&arg)),
                                ),
                            );
                        },
                    )
                })
            })
        })
    })
}

#[test]
fn pi_res_congruence() {
    let ctx = Ctx::<StringScheme>::root();
    
    ctx
    .with_funext(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name, input_name, output_name]| {
            arg_name
            .ctx()
            .with_tys(|[arg_ty]| {
                arg_ty
                .pi(&arg_name, |arg| arg.ctx().universe())
                .with_cons(|input_res_ty| {
                    same_ctx!(&arg_ty, &input_res_ty);
                    let input_res_ty = arg_ty.scope(|arg| input_res_ty.app(&arg).to_ty());

                    arg_ty
                    .pi(&arg_name, |arg| arg.ctx().universe())
                    .with_cons(|output_res_ty| {
                        same_ctx!(&arg_ty, &input_res_ty, &output_res_ty);
                        let output_res_ty = arg_ty.scope(|arg| output_res_ty.app(&arg).to_ty());

                        output_res_ty
                        .ctx()
                        .with_dependent_iso_between(
                            &arg_name,
                            &arg_ty,
                            &input_name,
                            &output_name,
                            input_res_ty.unbind(),
                            output_res_ty.unbind(),
                            |res_iso| {
                                same_ctx!(&arg_ty, &arg_name, &res_iso);

                                let iso = Iso::pi_res_congruence(
                                    &arg_name,
                                    &arg_ty,
                                    res_iso.unbind(),
                                    &funext,
                                );
                                assert_eq!(
                                    iso.input_ty(),
                                    arg_ty.pi(&arg_name, input_res_ty.unbind()),
                                );
                                assert_eq!(
                                    iso.output_ty(),
                                    arg_ty.pi(&arg_name, output_res_ty.unbind()),
                                );
                            },
                        )
                    })
                })
            })
        })
    })
}

#[test]
fn cong_congruence() {
    let ctx = Ctx::<StringScheme>::root();

    ctx
    .with_names(|[eq_term_name, input_name, output_name]| {
        output_name
        .ctx()
        .with_tys(|[eq_ty]| {
            eq_ty
            .with_cons(|eq_term_0| {
                eq_ty
                .weaken_into(&eq_term_0.ctx())
                .with_cons(|eq_term_1| {
                    eq_term_0
                    .equals(&eq_term_1)
                    .with_cons(|elim| {
                        eq_ty
                        .weaken_into(&elim.ctx())
                        .pi(&eq_term_name, |eq_term| eq_term.ctx().universe())
                        .with_cons(|input_inhab_ty| {
                            same_ctx!(&eq_ty, &input_inhab_ty);

                            let input_inhab_ty = eq_ty.scope(|eq_term| {
                                input_inhab_ty.app(&eq_term).to_ty()
                            });

                            eq_ty
                            .weaken_into(&input_inhab_ty.ctx())
                            .pi(&eq_term_name, |eq_term| eq_term.ctx().universe())
                            .with_cons(|output_inhab_ty| {
                                same_ctx!(&eq_ty, &output_inhab_ty);

                                let output_inhab_ty = eq_ty.scope(|eq_term| {
                                    output_inhab_ty.app(&eq_term).to_ty()
                                });

                                output_inhab_ty
                                .ctx()
                                .with_dependent_iso_between(
                                    &eq_term_name,
                                    &eq_ty,
                                    &input_name,
                                    &output_name,
                                    input_inhab_ty.unbind(),
                                    output_inhab_ty.unbind(),
                                    |inhab_iso| {
                                        same_ctx!(&elim, &inhab_iso);

                                        let iso = Iso::cong_congruence(
                                            &elim,
                                            inhab_iso.unbind(),
                                        );
                                        assert_eq!(
                                            iso.input_ty(),
                                            elim
                                            .cong(
                                                |_, _, _| elim.ctx().universe(),
                                                |eq_term| input_inhab_ty.bind(&eq_term).to_term(),
                                            )
                                            .to_ty(),
                                        );
                                        assert_eq!(
                                            iso.output_ty(),
                                            elim
                                            .cong(
                                                |_, _, _| elim.ctx().universe(),
                                                |eq_term| output_inhab_ty.bind(&eq_term).to_term(),
                                            )
                                            .to_ty(),
                                        );
                                    },
                                )
                            })
                        })
                    })
                })
            })
        })
    })
}

#[test]
fn cong_ty_lift() {
    let ctx = Ctx::<StringScheme>::root();

    ctx
    .with_tys(|[eq_ty, inhab]| {
        eq_ty
        .with_cons(|eq_term_0| {
            eq_ty
            .weaken_into(&eq_term_0.ctx())
            .with_cons(|eq_term_1| {
                eq_term_0
                .equals(&eq_term_1)
                .with_cons(|elim| {
                    same_ctx!(&elim, &inhab);

                    let iso = Iso::cong_ty_lift(&elim, &inhab);
                    assert_eq!(
                        iso.input_ty(),
                        elim
                        .cong(
                            |_, _, _| elim.ctx().universe(),
                            |_| inhab.to_term(),
                        )
                        .to_ty()
                    );
                    assert_eq!(
                        iso.output_ty(),
                        inhab,
                    );
                })
            })
        })
    })
}

#[test]
fn unique_identity_congruence() {
    let ctx = Ctx::<StringScheme>::root();

    ctx
    .with_names(|[eq_term_name, input_name, output_name]| {
        output_name
        .ctx()
        .with_tys(|[eq_ty]| {
            eq_ty
            .with_cons(|eq_term| {
                eq_term
                .equals(&eq_term)
                .with_cons(|elim| {
                    eq_ty
                    .weaken_into(&elim.ctx())
                    .pi(&eq_term_name, |eq_term| eq_term.ctx().universe())
                    .with_cons(|input_inhab_ty| {
                        same_ctx!(&eq_ty, &input_inhab_ty);

                        let input_inhab_ty = eq_ty.scope(|eq_term| {
                            input_inhab_ty.app(&eq_term).to_ty()
                        });

                        eq_ty
                        .weaken_into(&input_inhab_ty.ctx())
                        .pi(&eq_term_name, |eq_term| eq_term.ctx().universe())
                        .with_cons(|output_inhab_ty| {
                            same_ctx!(&eq_ty, &output_inhab_ty);

                            let output_inhab_ty = eq_ty.scope(|eq_term| {
                                output_inhab_ty.app(&eq_term).to_ty()
                            });

                            output_inhab_ty
                            .ctx()
                            .with_dependent_iso_between(
                                &eq_term_name,
                                &eq_ty,
                                &input_name,
                                &output_name,
                                input_inhab_ty.unbind(),
                                output_inhab_ty.unbind(),
                                |inhab_iso| {
                                    same_ctx!(&elim, &inhab_iso);

                                    let iso = Iso::unique_identity_congruence(
                                        &elim,
                                        inhab_iso.unbind(),
                                    );
                                    assert_eq!(
                                        iso.input_ty(),
                                        elim
                                        .unique_identity(
                                            |_, _| elim.ctx().universe(),
                                            |eq_term| input_inhab_ty.bind(&eq_term).to_term(),
                                        )
                                        .to_ty(),
                                    );
                                    assert_eq!(
                                        iso.output_ty(),
                                        elim
                                        .unique_identity(
                                            |_, _| elim.ctx().universe(),
                                            |eq_term| output_inhab_ty.bind(&eq_term).to_term(),
                                        )
                                        .to_ty(),
                                    );
                                },
                            )
                        })
                    })
                })
            })
        })
    })
}

#[test]
fn unique_identity_ty_lift() {
    let ctx = Ctx::<StringScheme>::root();

    ctx
    .with_tys(|[eq_ty, inhab]| {
        eq_ty
        .with_cons(|eq_term| {
            eq_term
            .equals(&eq_term)
            .with_cons(|elim| {
                same_ctx!(&elim, &inhab);

                let iso = Iso::unique_identity_ty_lift(&elim, &inhab);
                assert_eq!(
                    iso.input_ty(),
                    elim
                    .unique_identity(
                        |_, _| elim.ctx().universe(),
                        |_| inhab.to_term(),
                    )
                    .to_ty()
                );
                assert_eq!(
                    iso.output_ty(),
                    inhab,
                );
            })
        })
    })
}

#[test]
fn case_congruence() {
    let ctx = Ctx::<StringScheme>::root();

    ctx
    .with_names(|[
        lhs_name, rhs_name, lhs_input_name, lhs_output_name, rhs_input_name, rhs_output_name,
    ]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty]| {
            Ty::sum(&lhs_ty, &lhs_name, &rhs_ty)
            .with_cons(|elim| {
                same_ctx!(&lhs_ty, &elim);

                lhs_ty
                .pi(&lhs_name, |lhs| lhs.ctx().universe())
                .with_cons(|input_lhs_inhab| {
                    same_ctx!(&lhs_ty, &rhs_ty, &input_lhs_inhab);
                    let input_lhs_inhab = lhs_ty.scope(|lhs| {
                        input_lhs_inhab.app(&lhs).to_ty()
                    });

                    rhs_ty
                    .pi(&rhs_name, |rhs| rhs.ctx().universe())
                    .with_cons(|input_rhs_inhab| {
                        same_ctx!(&lhs_ty, &rhs_ty, &input_rhs_inhab);
                        let input_rhs_inhab = rhs_ty.scope(|rhs| {
                            input_rhs_inhab.app(&rhs).to_ty()
                        });

                        lhs_ty
                        .pi(&lhs_name, |lhs| lhs.ctx().universe())
                        .with_cons(|output_lhs_inhab| {
                            same_ctx!(&lhs_ty, &rhs_ty, &output_lhs_inhab);
                            let output_lhs_inhab = lhs_ty.scope(|lhs| {
                                output_lhs_inhab.app(&lhs).to_ty()
                            });

                            rhs_ty
                            .pi(&rhs_name, |rhs| rhs.ctx().universe())
                            .with_cons(|output_rhs_inhab| {
                                same_ctx!(&lhs_ty, &rhs_ty, &output_rhs_inhab);

                                let output_rhs_inhab = rhs_ty.scope(|rhs| {
                                    output_rhs_inhab.app(&rhs).to_ty()
                                });

                                output_rhs_inhab
                                .ctx()
                                .with_dependent_iso_between(
                                    &lhs_name,
                                    &lhs_ty,
                                    &lhs_input_name,
                                    &lhs_output_name,
                                    input_lhs_inhab.unbind(),
                                    output_lhs_inhab.unbind(),
                                    |lhs_inhab_iso| {
                                        lhs_inhab_iso
                                        .ctx()
                                        .with_dependent_iso_between(
                                            &rhs_name,
                                            &rhs_ty,
                                            &rhs_input_name,
                                            &rhs_output_name,
                                            input_rhs_inhab.unbind(),
                                            output_rhs_inhab.unbind(),
                                            |rhs_inhab_iso| {
                                                same_ctx!(
                                                    &elim,
                                                    &input_lhs_inhab,
                                                    &output_lhs_inhab,
                                                    &input_rhs_inhab,
                                                    &output_rhs_inhab,
                                                    &lhs_inhab_iso,
                                                    &rhs_inhab_iso,
                                                );

                                                let iso = Iso::case_congruence(
                                                    &elim,
                                                    lhs_inhab_iso.unbind(),
                                                    rhs_inhab_iso.unbind(),
                                                );
                                                assert_eq!(
                                                    iso.input_ty(),
                                                    elim
                                                    .case(
                                                        |_| elim.ctx().universe(),
                                                        |lhs| {
                                                            input_lhs_inhab
                                                            .bind(&lhs)
                                                            .to_term()
                                                        },
                                                        |rhs| {
                                                            input_rhs_inhab
                                                            .bind(&rhs)
                                                            .to_term()
                                                        },
                                                    )
                                                    .to_ty()
                                                );
                                                assert_eq!(
                                                    iso.output_ty(),
                                                    elim
                                                    .case(
                                                        |_| elim.ctx().universe(),
                                                        |lhs| {
                                                            output_lhs_inhab
                                                            .bind(&lhs)
                                                            .to_term()
                                                        },
                                                        |rhs| {
                                                            output_rhs_inhab
                                                            .bind(&rhs)
                                                            .to_term()
                                                        },
                                                    )
                                                    .to_ty()
                                                );
                                            },
                                        )
                                    },
                                )
                            })
                        })
                    })
                })
            })
        })
    })
}

#[test]
fn case_ty_lift() {
    let ctx = Ctx::<StringScheme>::root();

    ctx
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty, inhab]| {
            lhs_ty
            .sum(&lhs_name, &rhs_ty)
            .with_cons(|elim| {
                let iso = Iso::case_ty_lift(&elim, &inhab);

                assert_eq!(
                    iso.input_ty(),
                    elim
                    .case(
                        |_| elim.ctx().universe(),
                        |_| inhab.to_term(),
                        |_| inhab.to_term(),
                    )
                    .to_ty(),
                );
                assert_eq!(
                    iso.output_ty(),
                    inhab,
                );
            })
        })
    })
}

#[test]
fn equality_of_equality_types() {
    let ctx = Ctx::<StringScheme>::root();

    let eq_term_0_0_name = StringScheme::name_from_str("val_0_0");
    let eq_term_1_0_name = StringScheme::name_from_str("val_1_0");
    let eq_term_0_1_name = StringScheme::name_from_str("val_0_1");
    let eq_term_1_1_name = StringScheme::name_from_str("val_1_1");

    let tys_eq_name = StringScheme::name_from_str("tys_eq");
    let eq_term_0_eq_name = StringScheme::name_from_str("val_0_eq");

    ctx
    .with_tys(|[eq_ty_0, eq_ty_1]| {
        eq_ty_0
        .with_cons(|eq_term_0_0| {
            same_ctx!(&eq_ty_0, &eq_term_0_0);

            eq_ty_0
            .with_cons(|eq_term_1_0| {
                same_ctx!(&eq_ty_1, &eq_term_1_0);

                eq_ty_1
                .with_cons(|eq_term_0_1| {
                    same_ctx!(&eq_ty_1, &eq_term_0_1);

                    eq_ty_1
                    .with_cons(|eq_term_1_1| {
                        same_ctx!(&eq_ty_1, &eq_term_1_1);

                        let iso = Iso::equality_of_equality_types(
                            &eq_term_0_0,
                            &eq_term_1_0,
                            &eq_term_0_1,
                            &eq_term_1_1,
                        );

                        assert_eq!(
                            iso.input_ty(),
                            eq_term_0_0
                            .equals(&eq_term_1_0)
                            .to_term()
                            .equals(
                                &eq_term_0_1
                                .equals(&eq_term_1_1)
                                .to_term()
                            )
                        );
                        assert_eq!(
                            iso.output_ty(),
                            eq_ty_0
                            .to_term()
                            .equals(&eq_ty_1.to_term())
                            .sigma(
                                &tys_eq_name,
                                |tys_eq| {
                                    tys_eq
                                    .cong(
                                        |eq_ty_0, eq_ty_1, _tys_eq| {
                                            let eq_ty_0 = eq_ty_0.to_ty();
                                            let eq_ty_1 = eq_ty_1.to_ty();

                                            eq_ty_0
                                            .pi(&eq_term_0_0_name, |eq_term_0_0| {

                                                eq_ty_0
                                                .weaken_into(&eq_term_0_0.ctx())
                                                .pi(&eq_term_1_0_name, |eq_term_1_0| {

                                                    eq_ty_1
                                                    .weaken_into(&eq_term_1_0.ctx())
                                                    .pi(&eq_term_0_1_name, |eq_term_0_1| {

                                                        eq_ty_1
                                                        .weaken_into(&eq_term_0_1.ctx())
                                                        .pi(&eq_term_1_1_name, |eq_term_1_1| {
                                                            eq_term_1_1
                                                            .ctx()
                                                            .universe()
                                                        })
                                                    })
                                                })
                                            })
                                        },
                                        |eq_ty| {
                                            let eq_ty = eq_ty.to_ty();

                                            eq_ty
                                            .func(&eq_term_0_0_name, |eq_term_0_0| {
                                                same_ctx!(&eq_ty, &eq_term_0_0);

                                                eq_ty
                                                .func(&eq_term_1_0_name, |eq_term_1_0| {
                                                    same_ctx!(&eq_ty, &eq_term_1_0);

                                                    eq_ty
                                                    .func(&eq_term_0_1_name, |eq_term_0_1| {
                                                        same_ctx!(&eq_ty, &eq_term_0_1);

                                                        eq_ty
                                                        .func(&eq_term_1_1_name, |eq_term_1_1| {
                                                            same_ctx!(&eq_term_0_0, &eq_term_1_1);

                                                            eq_term_0_0
                                                            .equals(&eq_term_0_1)
                                                            .sigma(
                                                                &eq_term_0_eq_name,
                                                                |_| {
                                                                    eq_term_1_0
                                                                    .equals(&eq_term_1_1)
                                                                },
                                                            )
                                                            .to_term()
                                                        })
                                                    })
                                                })
                                            })
                                        },
                                    )
                                    .app(&eq_term_0_0)
                                    .app(&eq_term_1_0)
                                    .app(&eq_term_0_1)
                                    .app(&eq_term_1_1)
                                    .to_ty()
                                },
                            ),
                        );
                    })
                })
            })
        })
    })
}

#[test]
fn equality_of_sum_types_to_equality_of_type_parameters() {
    let ctx = Ctx::<StringScheme>::root();

    let lhs_name_eq_name = StringScheme::name_from_str("lhs_name_eq");
    let lhs_ty_eq_name = StringScheme::name_from_str("lhs_ty_eq");

    ctx
    .with_names(|[lhs_name_0, lhs_name_1]| {
        lhs_name_0
        .ctx()
        .with_tys(|[lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1]| {
            same_ctx!(&lhs_name_0, &lhs_name_1, &lhs_ty_0, &lhs_ty_1, &rhs_ty_0, &rhs_ty_1);

            let iso = Iso::equality_of_sum_types_to_equality_of_type_parameters(
                &lhs_name_0, &lhs_name_1, &lhs_ty_0, &lhs_ty_1, &rhs_ty_0, &rhs_ty_1,
            );
            assert_eq!(
                iso.input_ty(),
                lhs_ty_0
                .sum(&lhs_name_0, &rhs_ty_0)
                .to_term()
                .equals(
                    &lhs_ty_1
                    .sum(&lhs_name_1, &rhs_ty_1)
                    .to_term()
                ),
            );
            assert_eq!(
                iso.output_ty(),
                lhs_name_0
                .to_term()
                .equals(&lhs_name_1.to_term())
                .sigma(
                    &lhs_name_eq_name,
                    |_| {
                        lhs_ty_0
                        .to_term()
                        .equals(&lhs_ty_1.to_term())
                        .sigma(
                            &lhs_ty_eq_name,
                            |_| {
                                rhs_ty_0.to_term().equals(&rhs_ty_1.to_term())
                            },
                        )
                    },
                )
            );
        })
    })
}

#[test]
fn equality_of_sigma_types_to_equality_of_type_parameters() {
    let ctx = Ctx::<StringScheme>::root();

    let head_name_eq_name = StringScheme::name_from_str("head_names_eq");
    let head_ty_eq_name = StringScheme::name_from_str("head_tys_eq");

    ctx
    .with_funext(|funext| {
        funext
        .ctx()
        .with_names(|[head_name_0, head_name_1]| {
            head_name_0
            .ctx()
            .with_tys(|[head_ty_0, head_ty_1]| {
                head_ty_0
                .pi(&head_name_0, |head| head.ctx().universe())
                .with_cons(|tail_ty_0| {
                    same_ctx!(&head_ty_0, &head_ty_1, &tail_ty_0);
                    let tail_ty_0 = head_ty_0.scope(|head| tail_ty_0.app(&head).to_ty());

                    head_ty_1
                    .pi(&head_name_1, |head| head.ctx().universe())
                    .with_cons(|tail_ty_1| {
                        same_ctx!(
                            &head_name_0, &head_name_1,
                            &head_ty_0, &head_ty_1,
                            &tail_ty_0, &tail_ty_1,
                        );
                        let tail_ty_1 = head_ty_1.scope(|head| tail_ty_1.app(&head).to_ty());

                        let iso = Iso::equality_of_sigma_types_to_equality_of_type_parameters(
                            &head_name_0,
                            &head_name_1,
                            &head_ty_0,
                            &head_ty_1,
                            tail_ty_0.unbind(),
                            tail_ty_1.unbind(),
                        );
                        assert_eq!(
                            iso.input_ty(),
                            tail_ty_0
                            .to_sigma(&head_name_0)
                            .to_term()
                            .equals(
                                &tail_ty_1
                                .to_sigma(&head_name_1)
                                .to_term()
                            ),
                        );
                        assert_eq!(
                            iso.output_ty(),
                            head_name_0
                            .to_term()
                            .equals(&head_name_1.to_term())
                            .sigma(
                                &head_name_eq_name,
                                |head_name_eq| {
                                    same_ctx!(&head_ty_0, &head_name_eq);

                                    head_ty_0
                                    .to_term()
                                    .equals(&head_ty_1.to_term())
                                    .sigma(
                                        &head_ty_eq_name,
                                        |head_ty_eq| {
                                            Ty::scoped_tys_equal(
                                                &head_name_eq,
                                                &head_ty_eq,
                                                tail_ty_0.unbind(),
                                                tail_ty_1.unbind(),
                                            )
                                        },
                                    )
                                },
                            )
                        );
                    })
                })
            })
        })
    })
}

#[test]
fn equality_of_pi_types_to_equality_of_type_parameters() {
    let ctx = Ctx::<StringScheme>::root();

    let arg_name_eq_name = StringScheme::name_from_str("arg_names_eq");
    let arg_ty_eq_name = StringScheme::name_from_str("arg_tys_eq");

    ctx
    .with_funext(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name_0, arg_name_1]| {
            arg_name_0
            .ctx()
            .with_tys(|[arg_ty_0, arg_ty_1]| {
                arg_ty_0
                .pi(&arg_name_0, |arg| arg.ctx().universe())
                .with_cons(|res_ty_0| {
                    same_ctx!(&arg_ty_0, &arg_ty_1, &res_ty_0);
                    let res_ty_0 = arg_ty_0.scope(|arg| res_ty_0.app(&arg).to_ty());

                    arg_ty_1
                    .pi(&arg_name_1, |arg| arg.ctx().universe())
                    .with_cons(|res_ty_1| {
                        same_ctx!(
                            &arg_name_0, &arg_name_1,
                            &arg_ty_0, &arg_ty_1,
                            &res_ty_0, &res_ty_1,
                        );
                        let res_ty_1 = arg_ty_1.scope(|arg| res_ty_1.app(&arg).to_ty());

                        let iso = Iso::equality_of_pi_types_to_equality_of_type_parameters(
                            &arg_name_0,
                            &arg_name_1,
                            &arg_ty_0,
                            &arg_ty_1,
                            res_ty_0.unbind(),
                            res_ty_1.unbind(),
                        );
                        assert_eq!(
                            iso.input_ty(),
                            res_ty_0
                            .to_pi(&arg_name_0)
                            .to_term()
                            .equals(
                                &res_ty_1
                                .to_pi(&arg_name_1)
                                .to_term()
                            ),
                        );
                        assert_eq!(
                            iso.output_ty(),
                            arg_name_0
                            .to_term()
                            .equals(&arg_name_1.to_term())
                            .sigma(
                                &arg_name_eq_name,
                                |arg_name_eq| {
                                    same_ctx!(&arg_ty_0, &arg_name_eq);

                                    arg_ty_0
                                    .to_term()
                                    .equals(&arg_ty_1.to_term())
                                    .sigma(
                                        &arg_ty_eq_name,
                                        |arg_ty_eq| {
                                            Ty::scoped_tys_equal(
                                                &arg_name_eq,
                                                &arg_ty_eq,
                                                res_ty_0.unbind(),
                                                res_ty_1.unbind(),
                                            )
                                        },
                                    )
                                },
                            )
                        );
                    })
                })
            })
        })
    })
}

#[test]
fn function_extensionality() {
    let ctx = Ctx::<StringScheme>::root();

    ctx
    .with_funext(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name]| {
            arg_name
            .ctx()
            .with_tys(|[arg_ty]| {
                arg_ty
                .pi(&arg_name, |arg| arg.ctx().universe())
                .with_cons(|res_ty| {
                    same_ctx!(&arg_ty, &res_ty);
                    let res_ty = arg_ty.scope(|arg| res_ty.app(&arg).to_ty());

                    arg_ty
                    .pi(&arg_name, res_ty.unbind())
                    .with_cons(|func_0| {
                        same_ctx!(&arg_ty, &func_0);

                        arg_ty
                        .pi(&arg_name, res_ty.unbind())
                        .with_cons(|func_1| {
                            same_ctx!(&arg_ty, &func_1);

                            let iso = Iso::function_extensionality(
                                &arg_name,
                                &arg_ty,
                                |arg| func_0.app(&arg).equals(&func_1.app(&arg)),
                                &funext,
                            );
                            assert_eq!(
                                iso.input_ty(),
                                arg_ty.pi(&arg_name, |arg| {
                                    func_0.app(&arg).equals(&func_1.app(&arg))
                                }),
                            );
                            assert_eq!(
                                iso.output_ty(),
                                func_0.equals(&func_1),
                            );
                        })
                    })
                })
            })
        })
    })
}


