use crate::priv_prelude::*;

pub fn symmetry<S: Scheme>() -> Tm<S> {
    let ty_name = S::name_from_str("Ty");
    let val_0_name = S::name_from_str("val_0");
    let val_1_name = S::name_from_str("val_1");
    let val_eq_name = S::name_from_str("val_eq");
    Ctx::root()
    .universe()
    .func(&ty_name, |ty| {
        let ty = ty.to_ty();
        ty
        .func(&val_0_name, |val_0| {
            ty
            .weaken_into(&val_0.ctx())
            .func(&val_1_name, |val_1| {
                val_0
                .equals(&val_1)
                .func(&val_eq_name, |val_eq| {
                    val_eq
                    .cong(
                        |val_0, val_1, _| val_1.equals(&val_0),
                        |val| val.refl(),
                    )
                })
            })
        })
    })
}

pub fn transitivity<S: Scheme>() -> Tm<S> {
    let ty_name = S::name_from_str("Ty");
    let val_0_name = S::name_from_str("val_0");
    let val_1_name = S::name_from_str("val_1");
    let val_2_name = S::name_from_str("val_2");
    let val_eq_0_name = S::name_from_str("val_eq_0");
    let val_eq_1_name = S::name_from_str("val_eq_1");

    Ctx::root()
    .universe()
    .func(&ty_name, |ty| {
        let ty = ty.to_ty();

        ty
        .func(&val_0_name, |val_0| {
            ty
            .weaken_into(&val_0.ctx())
            .func(&val_1_name, |val_1| {
                ty
                .weaken_into(&val_1.ctx())
                .func(&val_2_name, |val_2| {
                    val_0
                    .equals(&val_1)
                    .weaken_into(&val_2.ctx())
                    .func(&val_eq_0_name, |val_eq_0| {
                        val_eq_0
                        .cong(
                            |val_0, val_1, _| {
                                val_1
                                .equals(&val_2)
                                .pi(&val_eq_1_name, |_| {
                                    val_0.equals(&val_2)
                                })
                            },
                            |val| {
                                val
                                .equals(&val_2)
                                .func(&val_eq_1_name, |val_eq_1| val_eq_1)
                            },
                        )
                    })
                })
            })
        })
    })
}

pub fn transport<S: Scheme>() -> Tm<S> {
    let ty_0_name = S::name_from_str("Ty0");
    let ty_1_name = S::name_from_str("Ty1");
    let tys_eq_name = S::name_from_str("tys_eq");
    let val_name = S::name_from_str("val");

    Ctx::root()
    .universe()
    .func(&ty_0_name, |ty_0| {
        ty_0
        .ctx()
        .universe()
        .func(&ty_1_name, |ty_1| {
            ty_0
            .equals(&ty_1)
            .func(&tys_eq_name, |tys_eq| {
                tys_eq
                .cong(
                    |ty_0, ty_1, _| {
                        ty_0.to_ty().pi(&val_name, |_| ty_1.to_ty())
                    },
                    |ty| ty.to_ty().func(&val_name, |val| val),
                )
            })
        })
    })
}

pub fn heterogeneous_equal<S: Scheme>() -> Tm<S> {
    let ty_0_name = S::name_from_str("Ty0");
    let ty_1_name = S::name_from_str("Ty1");
    let tys_eq_name = S::name_from_str("tys_eq");
    let val_0_name = S::name_from_str("val_0");
    let val_1_name = S::name_from_str("val_1");

    Ctx::root()
    .universe()
    .func(&ty_0_name, |ty_0| {
        ty_0
        .ctx()
        .universe()
        .func(&ty_1_name, |ty_1| {
            ty_0
            .equals(&ty_1)
            .func(&tys_eq_name, |tys_eq| {
                tys_eq
                .cong(
                    |ty_0, ty_1, _| {
                        ty_0
                        .to_ty()
                        .pi(&val_0_name, |val_0| {
                            ty_1
                            .weaken_into(&val_0.ctx())
                            .to_ty()
                            .pi(&val_1_name, |val_1| {
                                val_1.ctx().universe()
                            })
                        })
                    },
                    |ty| {
                        ty
                        .to_ty()
                        .func(&val_0_name, |val_0| {
                            ty
                            .weaken_into(&val_0.ctx())
                            .to_ty()
                            .func(&val_1_name, |val_1| {
                                val_0.equals(&val_1).to_term()
                            })
                        })
                    },
                )
            })
        })
    })
}

pub fn heterogeneous_transitivity<S: Scheme>() -> Tm<S> {
    let ty_0_name = S::name_from_str("Ty0");
    let ty_1_name = S::name_from_str("Ty1");
    let ty_2_name = S::name_from_str("Ty2");
    let tys_eq_0_name = S::name_from_str("tys_eq_0");
    let tys_eq_1_name = S::name_from_str("tys_eq_1");
    let val_0_name = S::name_from_str("val_0");
    let val_1_name = S::name_from_str("val_1");
    let val_2_name = S::name_from_str("val_2");
    let val_eq_0_name = S::name_from_str("val_eq_0");
    let val_eq_1_name = S::name_from_str("val_eq_1");

    Ctx::root()
    .universe()
    .func(&ty_0_name, |ty_0| {
        ty_0
        .ctx()
        .universe()
        .func(&ty_1_name, |ty_1| {
            ty_1
            .ctx()
            .universe()
            .func(&ty_2_name, |ty_2| {
                ty_0
                .equals(&ty_1)
                .weaken_into(&ty_2.ctx())
                .func(&tys_eq_0_name, |tys_eq_0| {
                    tys_eq_0
                    .cong(
                        |ty_0, ty_1, tys_eq_0| {
                            ty_1
                            .equals(&ty_2)
                            .pi(&tys_eq_1_name, |tys_eq_1| {
                                ty_0
                                .to_ty()
                                .weaken_into(&tys_eq_1.ctx())
                                .pi(&val_0_name, |val_0| {
                                    ty_1
                                    .to_ty()
                                    .weaken_into(&val_0.ctx())
                                    .pi(&val_1_name, |val_1| {
                                        ty_2
                                        .to_ty()
                                        .weaken_into(&val_1.ctx())
                                        .pi(&val_2_name, |val_2| {
                                            tys_eq_0
                                            .weaken_into(&val_2.ctx())
                                            .heterogeneous_equal(&val_0, &val_1)
                                            .pi(&val_eq_0_name, |val_eq_0| {
                                                tys_eq_1
                                                .weaken_into(&val_eq_0.ctx())
                                                .heterogeneous_equal(&val_1, &val_2)
                                                .pi(&val_eq_1_name, |_| {
                                                    tys_eq_0
                                                    .transitivity(&tys_eq_1)
                                                    .heterogeneous_equal(&val_0, &val_2)
                                                })
                                            })
                                        })
                                    })
                                })
                            })
                        },
                        |ty| {
                            ty
                            .equals(&ty_2)
                            .func(&tys_eq_1_name, |tys_eq_1| {
                                tys_eq_1
                                .cong(
                                    |ty, ty_2, tys_eq_1| {
                                        ty
                                        .to_ty()
                                        .pi(&val_0_name, |val_0| {
                                            ty
                                            .to_ty()
                                            .weaken_into(&val_0.ctx())
                                            .pi(&val_1_name, |val_1| {
                                                ty_2
                                                .to_ty()
                                                .weaken_into(&val_1.ctx())
                                                .pi(&val_2_name, |val_2| {
                                                    val_0
                                                    .equals(&val_1)
                                                    .weaken_into(&val_2.ctx())
                                                    .pi(&val_eq_0_name, |val_eq_0| {
                                                        tys_eq_1
                                                        .weaken_into(&val_eq_0.ctx())
                                                        .heterogeneous_equal(&val_1, &val_2)
                                                        .pi(&val_eq_1_name, |_| {
                                                            tys_eq_1
                                                            .heterogeneous_equal(&val_0, &val_2)
                                                        })
                                                    })
                                                })
                                            })
                                        })
                                    },
                                    |ty| {
                                        ty
                                        .to_ty()
                                        .func(&val_0_name, |val_0| {
                                            ty
                                            .to_ty()
                                            .weaken_into(&val_0.ctx())
                                            .func(&val_1_name, |val_1| {
                                                ty
                                                .to_ty()
                                                .weaken_into(&val_1.ctx())
                                                .func(&val_2_name, |val_2| {
                                                    val_0
                                                    .equals(&val_1)
                                                    .weaken_into(&val_2.ctx())
                                                    .func(&val_eq_0_name, |val_eq_0| {
                                                        val_1
                                                        .equals(&val_2)
                                                        .weaken_into(&val_eq_0.ctx())
                                                        .func(&val_eq_1_name, |val_eq_1| {
                                                            val_eq_0.transitivity(&val_eq_1)
                                                        })
                                                    })
                                                })
                                            })
                                        })
                                    },
                                )
                            })
                        },
                    )
                })
            })
        })
    })
}

pub fn congruence<S: Scheme>() -> Tm<S> {
    let arg_name_name = S::name_from_str("arg_name");
    let arg_ty_name = S::name_from_str("Arg");
    let res_ty_name = S::name_from_str("Res");
    let func_name = S::name_from_str("func");
    let arg_0_name = S::name_from_str("arg_0");
    let arg_1_name = S::name_from_str("arg_1");
    let arg_eq_name = S::name_from_str("arg_eq");

    Ctx::root()
    .name()
    .func(&arg_name_name, |arg_name| {
        let arg_name = arg_name.to_name();
        arg_name
        .ctx()
        .universe()
        .func(&arg_ty_name, |arg_ty| {
            let arg_ty = arg_ty.to_ty();
            arg_ty
            .ctx()
            .universe()
            .func(&res_ty_name, |res_ty| {
                let res_ty = res_ty.to_ty();

                arg_ty
                .weaken_into(&res_ty.ctx())
                .pi(&arg_name, |_| res_ty.clone())
                .func(&func_name, |func| {
                    arg_ty
                    .weaken_into(&func.ctx())
                    .func(&arg_0_name, |arg_0| {
                        arg_ty
                        .weaken_into(&arg_0.ctx())
                        .func(&arg_1_name, |arg_1| {
                            arg_0
                            .equals(&arg_1)
                            .func(&arg_eq_name, |arg_eq| {
                                arg_eq
                                .cong(
                                    |arg_0, arg_1, _| {
                                        func.app(&arg_0).equals(&func.app(&arg_1))
                                    },
                                    |arg| func.app(&arg).refl(),
                                )
                            })
                        })
                    })
                })
            })
        })
    })
}

pub fn congruence_multi<S: Scheme>(len: usize) -> Tm<S> {
    fn congruence_multi_take_arg_names<S: Scheme>(
        ctx: &Ctx<S>,
        index: usize,
        len: usize,
        arg_names: &mut Vec<Name<S>>,
    ) -> Tm<S> {
        if index == len {
            return congruence_multi_take_arg_tys(
                ctx, 0, len, arg_names, &mut Vec::new(),
            );
        }

        let arg_name_name = S::name_from_str(&format!("arg_name_{}", index));
        ctx
        .name()
        .func(&arg_name_name, |arg_name| {
            let arg_name = arg_name.to_name();
            let ctx = arg_name.ctx();
            arg_names.push(arg_name);
            congruence_multi_take_arg_names(&ctx, index + 1, len, arg_names)
        })
    }

    fn congruence_multi_take_arg_tys<S: Scheme>(
        ctx: &Ctx<S>,
        index: usize,
        len: usize,
        arg_names: &[Name<S>],
        arg_tys: &mut Vec<Ty<S>>,
    ) -> Tm<S> {
        if index == len {
            let res_ty_name = S::name_from_str("Res");
            let func_name = S::name_from_str("func");
            return {
                ctx
                .universe()
                .func(&res_ty_name, |res_ty| {
                    let res_ty = res_ty.to_ty();
                    let ctx = res_ty.ctx();
                    let func_ty = congruence_multi_build_func_ty(
                        &ctx, 0, len, arg_names, arg_tys, &res_ty,
                    );

                    func_ty
                    .func(&func_name, |func| {
                        let ctx = func.ctx();
                        congruence_multi_take_args(
                            &ctx, 0, len, arg_names, arg_tys, &res_ty, &func, &mut Vec::new(),
                        )
                    })
                })

            };
        }

        let arg_ty_name = S::name_from_str(&format!("Arg{}", index));
        ctx
        .universe()
        .func(&arg_ty_name, |arg_ty| {
            let arg_ty = arg_ty.to_ty();
            let ctx = arg_ty.ctx();
            arg_tys.push(arg_ty);
            congruence_multi_take_arg_tys(&ctx, index + 1, len, arg_names, arg_tys)
        })
    }

    fn congruence_multi_build_func_ty<S: Scheme>(
        ctx: &Ctx<S>,
        index: usize,
        len: usize,
        arg_names: &[Name<S>],
        arg_tys: &[Ty<S>],
        res_ty: &Ty<S>,
    ) -> Ty<S> {
        if index == len {
            return res_ty.weaken_into(&ctx);
        }

        let arg_name = arg_names[index].weaken_into(ctx);
        let arg_ty = arg_tys[index].weaken_into(&ctx);

        arg_ty
        .pi(&arg_name, |arg| {
            let ctx = arg.ctx();
            congruence_multi_build_func_ty(
                &ctx, index + 1, len, arg_names, arg_tys, res_ty,
            )
        })
    }

    fn congruence_multi_take_args<S: Scheme>(
        ctx: &Ctx<S>,
        index: usize,
        len: usize,
        arg_names: &[Name<S>],
        arg_tys: &[Ty<S>],
        res_ty: &Ty<S>,
        func: &Tm<S>,
        arg_eqs: &mut Vec<(Tm<S>, Tm<S>, Tm<S>)>,
    ) -> Tm<S> {
        if index == len {
            return congruence_multi_build_res_term(
                ctx, 0, len, res_ty, func, arg_eqs,
            );
        }

        let arg_name = &arg_names[index];
        let prefix: String;
        let prefix = match S::try_name_as_string(arg_name) {
            Some(s) => {
                prefix = s;
                format_args!("{}", prefix)
            },
            None => format_args!("arg_{}", index),
        };
        let arg_0_name = S::name_from_str(&format!("{}_0", prefix));
        let arg_1_name = S::name_from_str(&format!("{}_1", prefix));
        let arg_eq_name = S::name_from_str(&format!("{}_eq", prefix));

        let arg_ty = arg_tys[index].weaken_into(&ctx);

        arg_ty
        .func(&arg_0_name, |arg_0| {
            arg_ty
            .weaken_into(&arg_0.ctx())
            .func(&arg_1_name, |arg_1| {
                arg_0
                .equals(&arg_1)
                .func(&arg_eq_name, |arg_eq| {
                    let ctx = arg_eq.ctx();
                    arg_eqs.push((arg_0, arg_1, arg_eq));
                    congruence_multi_take_args(
                        &ctx, index + 1, len, arg_names, arg_tys, res_ty, func, arg_eqs,
                    )
                })
            })
        })
    }

    fn congruence_multi_build_res_term<S: Scheme>(
        ctx: &Ctx<S>,
        index: usize,
        len: usize,
        res_ty: &Ty<S>,
        func: &Tm<S>,
        arg_eqs: &[(Tm<S>, Tm<S>, Tm<S>)],
    ) -> Tm<S> {
        if index == len {
            return func.refl();
        }

        let ((_, _, arg_eq), arg_eqs) = arg_eqs.split_first().unwrap();

        arg_eq
        .weaken_into(ctx)
        .cong(
            |arg_0, arg_1, _| {
                let mut apps_0 = func.app(&arg_0);
                let mut apps_1 = func.app(&arg_1);

                for (arg_0, arg_1, _) in arg_eqs.iter() {
                    apps_0 = apps_0.app(&arg_0);
                    apps_1 = apps_1.app(&arg_1);
                }

                apps_0.equals(&apps_1)
            },
            |arg| {
                let func = func.app(&arg);
                let ctx = func.ctx();
                congruence_multi_build_res_term(
                    &ctx, index + 1, len, res_ty, &func, arg_eqs,
                )
            },
        )
    }

    congruence_multi_take_arg_names(&Ctx::root(), 0, len, &mut Vec::new())
}

pub fn equality_contractible<S: Scheme>() -> Tm<S> {
    let ty_name = S::name_from_str("Ty");
    let val_0_name = S::name_from_str("val_0");
    let val_1_name = S::name_from_str("val_1");
    let val_eq_0_name = S::name_from_str("val_eq_0");
    let val_eq_1_name = S::name_from_str("val_eq_1");

    Ctx::root()
    .universe()
    .func(&ty_name, |ty| {
        let ty = ty.to_ty();
        ty
        .func(&val_0_name, |val_0| {
            ty
            .weaken_into(&val_0.ctx())
            .func(&val_1_name, |val_1| {
                val_0
                .equals(&val_1)
                .func(&val_eq_0_name, |val_eq_0| {
                    val_eq_0
                    .cong(
                        |val_0, val_1, val_eq_0| {
                            val_0
                            .equals(&val_1)
                            .pi(&val_eq_1_name, |val_eq_1| {
                                val_eq_0.equals(&val_eq_1)
                            })
                        },
                        |val| {
                            val
                            .equals(&val)
                            .func(&val_eq_1_name, |val_eq_1| {
                                val_eq_1
                                .unique_identity(
                                    |val, val_eq_1| val.refl().equals(&val_eq_1),
                                    |val| val.refl().refl(),
                                )
                            })
                        },
                    )
                })
            })
        })
    })
}

pub fn equals_refl<S: Scheme>() -> Tm<S> {
    let ty_name = S::name_from_str("Ty");
    let val_name = S::name_from_str("val");
    let val_eq_name = S::name_from_str("val_eq");

    Ctx::root()
    .universe()
    .func(&ty_name, |eq_ty| {
        let eq_ty = eq_ty.to_ty();
        eq_ty
        .func(&val_name, |eq_term| {
            eq_term
            .equals(&eq_term)
            .func(&val_eq_name, |elim| {
                elim
                .unique_identity(
                    |eq_term, elim| elim.equals(&eq_term.refl()),
                    |eq_term| eq_term.refl().refl(),
                )
            })
        })
    })
}

pub fn sigma_eq_cong<S: Scheme>() -> Tm<S> {
    let head_name_0_name = S::name_from_str("head_name_0");
    let head_name_1_name = S::name_from_str("head_name_1");
    let head_ty_0_name = S::name_from_str("Head0");
    let head_ty_1_name = S::name_from_str("Head1");
    let tail_ty_0_name = S::name_from_str("Tail0");
    let tail_ty_1_name = S::name_from_str("Tail1");
    let sigma_eq_name = S::name_from_str("sigma_eq");
    let motive_name = S::name_from_str("Motive");

    let head_name_name = S::name_from_str("head_name");
    let head_ty_name = S::name_from_str("Head");
    let tail_ty_name = S::name_from_str("Tail");
    let inhab_name = S::name_from_str("inhab");
    
    let sigma_eq_cong_same_name_same_head_ty_same_tail_ty = {
        |head_name: &Name<S>, tail_ty: &Scope<S, Ty<S>>| {
            tail_ty
            .to_sigma(&head_name)
            .to_term()
            .equals(&tail_ty.to_sigma(&head_name).to_term())
            .pi(&sigma_eq_name, |sigma_eq| sigma_eq.ctx().universe())
            .func(&motive_name, |motive| {
                let tail_ty = tail_ty.weaken_into(&motive.ctx());

                motive
                .app(&tail_ty.to_sigma(&head_name).to_term().refl())
                .to_ty()
                .func(&inhab_name, |inhab| {
                    let tail_ty = tail_ty.weaken_into(&inhab.ctx());

                    tail_ty
                    .to_sigma(&head_name)
                    .to_term()
                    .equals(
                        &tail_ty
                        .to_sigma(&head_name)
                        .to_term()
                    )
                    .func(&sigma_eq_name, |sigma_eq| {
                        tail_ty
                        .weaken_into(&sigma_eq.ctx())
                        .to_sigma(&head_name)
                        .to_term()
                        .refl()
                        .equality_contractible(&sigma_eq)
                        .map_eq(|sigma_eq| motive.app(&sigma_eq))
                        .transport(&inhab)
                    })
                })
            })
        }
    };

    let sigma_eq_cong_same_name_same_head_ty = |head_name: &Name<S>, head_ty: &Ty<S>| -> Tm<S> {
        head_ty
        .pi(&head_name, |head| head.ctx().universe())
        .pi(&tail_ty_0_name, |tail_ty_0| {
            let head_ty = head_ty.weaken_into(&tail_ty_0.ctx());
            let tail_ty_0 = head_ty.scope(|head| tail_ty_0.app(&head).to_ty());

            head_ty
            .pi(&head_name, |head| head.ctx().universe())
            .pi(&tail_ty_1_name, |tail_ty_1| {
                let head_ty = head_ty.weaken_into(&tail_ty_1.ctx());
                let tail_ty_1 = head_ty.scope(|head| tail_ty_1.app(&head).to_ty());

                tail_ty_0
                .to_sigma(&head_name)
                .to_term()
                .equals(&tail_ty_1.to_sigma(&head_name).to_term())
                .pi(&sigma_eq_name, |sigma_eq| {
                    sigma_eq.ctx().universe()
                })
            })
        })
        .func(&motive_name, |motive| {
            head_ty
            .weaken_into(&motive.ctx())
            .pi(&head_name, |head| head.ctx().universe())
            .pi(&tail_ty_name, |tail_ty| {
                let head_ty = head_ty.weaken_into(&tail_ty.ctx());

                motive
                .app(&tail_ty)
                .app(&tail_ty)
                .app(
                    &head_ty
                    .sigma(&head_name, |head| tail_ty.app(&head).to_ty())
                    .to_term()
                    .refl(),
                )
                .to_ty()
            })
            .func(&inhab_name, |inhab| {
                head_ty
                .weaken_into(&inhab.ctx())
                .pi(&head_name, |head| head.ctx().universe())
                .func(&tail_ty_0_name, |tail_ty_0| {
                    let head_ty = head_ty.weaken_into(&tail_ty_0.ctx());
                    let tail_ty_0 = head_ty.scope(|head| tail_ty_0.app(&head).to_ty());

                    head_ty
                    .weaken_into(&tail_ty_0.ctx())
                    .pi(&head_name, |head| head.ctx().universe())
                    .func(&tail_ty_1_name, |tail_ty_1| {
                        let head_ty = head_ty.weaken_into(&tail_ty_1.ctx());
                        let tail_ty_1 = head_ty.scope(|head| tail_ty_1.app(&head).to_ty());

                        tail_ty_0
                        .weaken_into(&tail_ty_1.ctx())
                        .to_sigma(&head_name)
                        .to_term()
                        .equals(
                            &tail_ty_1
                            .to_sigma(&head_name)
                            .to_term(),
                        )
                        .func(&sigma_eq_name, |sigma_eq| {
                            sigma_eq
                            .sigma_eq_tail_injective()
                            .cong(
                                |tail_ty_0, tail_ty_1, tail_ty_eq| {
                                    let head_ty = head_ty.weaken_into(&tail_ty_eq.ctx());

                                    head_ty
                                    .sigma(&head_name, |head| {
                                        tail_ty_0.app(&head).to_ty()
                                    })
                                    .to_term()
                                    .equals(
                                        &head_ty
                                        .sigma(&head_name, |head| {
                                            tail_ty_1.app(&head).to_ty()
                                        })
                                        .to_term()
                                    )
                                    .pi(&sigma_eq_name, |sigma_eq| {
                                        motive
                                        .app(&tail_ty_0)
                                        .app(&tail_ty_1)
                                        .app(&sigma_eq)
                                        .to_ty()
                                    })
                                },
                                |tail_ty| {
                                    let head_ty = head_ty.weaken_into(&tail_ty.ctx());
                                    sigma_eq_cong_same_name_same_head_ty_same_tail_ty(
                                        &head_name.weaken_into(&tail_ty.ctx()),
                                        &head_ty.scope(|head| tail_ty.app(&head).to_ty()),
                                    )
                                    .app(
                                        &motive
                                        .app(&tail_ty)
                                        .app(&tail_ty)
                                    )
                                    .app(
                                        &inhab
                                        .app(&tail_ty)
                                    )
                                },
                            )
                            .app(&sigma_eq)
                        })
                    })
                })
            })
        })
    };

    let sigma_eq_cong_same_name = |head_name: &Name<S>| -> Tm<S> {
        head_name
        .ctx()
        .universe()
        .pi(&head_ty_0_name, |head_ty_0| {
            let head_ty_0 = head_ty_0.to_ty();

            head_ty_0
            .ctx()
            .universe()
            .pi(&head_ty_1_name, |head_ty_1| {
                let head_ty_1 = head_ty_1.to_ty();

                head_ty_0
                .weaken_into(&head_ty_1.ctx())
                .pi(&head_name, |head_0| head_0.ctx().universe())
                .pi(&tail_ty_0_name, |tail_ty_0| {
                    let head_ty_0 = head_ty_0.weaken_into(&tail_ty_0.ctx());
                    let tail_ty_0 = head_ty_0.scope(|head_0| tail_ty_0.app(&head_0).to_ty());

                    head_ty_1
                    .weaken_into(&tail_ty_0.ctx())
                    .pi(&head_name, |head_1| head_1.ctx().universe())
                    .pi(&tail_ty_1_name, |tail_ty_1| {
                        let head_ty_1 = head_ty_1.weaken_into(&tail_ty_1.ctx());
                        let tail_ty_1 = head_ty_1.scope(|head_1| tail_ty_1.app(&head_1).to_ty());

                        tail_ty_0
                        .to_sigma(&head_name)
                        .to_term()
                        .equals(&tail_ty_1.to_sigma(&head_name).to_term())
                        .pi(&sigma_eq_name, |sigma_eq| {
                            sigma_eq.ctx().universe()
                        })
                    })
                })
            })
        })
        .func(&motive_name, |motive| {
            motive
            .ctx()
            .universe()
            .pi(&head_ty_name, |head_ty| {
                let head_ty = head_ty.to_ty();

                head_ty
                .pi(&head_name, |head| head.ctx().universe())
                .pi(&tail_ty_name, |tail_ty| {
                    let head_ty = head_ty.weaken_into(&tail_ty.ctx());

                    motive
                    .app(&head_ty.to_term())
                    .app(&head_ty.to_term())
                    .app(&tail_ty)
                    .app(&tail_ty)
                    .app(
                        &head_ty
                        .sigma(&head_name, |head| tail_ty.app(&head).to_ty())
                        .to_term()
                        .refl(),
                    )
                    .to_ty()
                })
            })
            .func(&inhab_name, |inhab| {
                inhab
                .ctx()
                .universe()
                .func(&head_ty_0_name, |head_ty_0| {
                    let head_ty_0 = head_ty_0.to_ty();

                    head_ty_0
                    .ctx()
                    .universe()
                    .func(&head_ty_1_name, |head_ty_1| {
                        let head_ty_1 = head_ty_1.to_ty();

                        head_ty_0
                        .weaken_into(&head_ty_1.ctx())
                        .pi(&head_name, |head_0| head_0.ctx().universe())
                        .func(&tail_ty_0_name, |tail_ty_0| {

                            head_ty_1
                            .weaken_into(&tail_ty_0.ctx())
                            .pi(&head_name, |head_1| head_1.ctx().universe())
                            .func(&tail_ty_1_name, |tail_ty_1| {
                                let head_ty_0 = head_ty_0.weaken_into(&tail_ty_1.ctx());
                                let head_ty_1 = head_ty_1.weaken_into(&tail_ty_1.ctx());

                                head_ty_0
                                .sigma(&head_name, |head_0| tail_ty_0.app(&head_0).to_ty())
                                .to_term()
                                .equals(
                                    &head_ty_1
                                    .sigma(&head_name, |head_1| tail_ty_1.app(&head_1).to_ty())
                                    .to_term()
                                )
                                .func(&sigma_eq_name, |sigma_eq| {
                                    sigma_eq
                                    .sigma_eq_head_injective()
                                    .cong(
                                        |head_ty_0, head_ty_1, _head_ty_eq| {
                                            let head_ty_0 = head_ty_0.to_ty();
                                            let head_ty_1 = head_ty_1.to_ty();

                                            head_ty_0
                                            .pi(&head_name, |head| head.ctx().universe())
                                            .pi(&tail_ty_0_name, |tail_ty_0| {
                                                head_ty_1
                                                .weaken_into(&tail_ty_0.ctx())
                                                .pi(&head_name, |head| head.ctx().universe())
                                                .pi(&tail_ty_1_name, |tail_ty_1| {
                                                    head_ty_0
                                                    .weaken_into(&tail_ty_1.ctx())
                                                    .sigma(&head_name, |head| {
                                                        tail_ty_0.app(&head).to_ty()
                                                    })
                                                    .to_term()
                                                    .equals(
                                                        &head_ty_1
                                                        .weaken_into(&tail_ty_1.ctx())
                                                        .sigma(&head_name, |head| {
                                                            tail_ty_1.app(&head).to_ty()
                                                        })
                                                        .to_term()
                                                    )
                                                    .pi(&sigma_eq_name, |sigma_eq| {
                                                        motive
                                                        .app(&head_ty_0.to_term())
                                                        .app(&head_ty_1.to_term())
                                                        .app(&tail_ty_0)
                                                        .app(&tail_ty_1)
                                                        .app(&sigma_eq)
                                                        .to_ty()
                                                    })
                                                })
                                            })
                                        },
                                        |head_ty| {
                                            sigma_eq_cong_same_name_same_head_ty(
                                                &head_name.weaken_into(&head_ty.ctx()),
                                                &head_ty.to_ty(),
                                            )
                                            .app(
                                                &motive
                                                .app(&head_ty)
                                                .app(&head_ty)
                                            )
                                            .app(
                                                &inhab
                                                .app(&head_ty)
                                            )
                                        },
                                    )
                                    .app(&tail_ty_0)
                                    .app(&tail_ty_1)
                                    .app(&sigma_eq)
                                })
                            })
                        })
                    })
                })
            })
        })
    };

    Ctx::root()
    .name()
    .pi(&head_name_0_name, |head_name_0| {
        let head_name_0 = head_name_0.to_name();

        head_name_0
        .ctx()
        .name()
        .pi(&head_name_1_name, |head_name_1| {
            let head_name_1 = head_name_1.to_name();

            head_name_1
            .ctx()
            .universe()
            .pi(&head_ty_0_name, |head_ty_0| {
                let head_ty_0 = head_ty_0.to_ty();

                head_ty_0
                .ctx()
                .universe()
                .pi(&head_ty_1_name, |head_ty_1| {
                    let head_ty_1 = head_ty_1.to_ty();

                    head_ty_0
                    .weaken_into(&head_ty_1.ctx())
                    .pi(&head_name_0, |head_0| head_0.ctx().universe())
                    .pi(&tail_ty_0_name, |tail_ty_0| {
                        let head_ty_0 = head_ty_0.weaken_into(&tail_ty_0.ctx());
                        let tail_ty_0 = head_ty_0.scope(|head_0| tail_ty_0.app(&head_0).to_ty());

                        head_ty_1
                        .weaken_into(&tail_ty_0.ctx())
                        .pi(&head_name_1, |head_1| head_1.ctx().universe())
                        .pi(&tail_ty_1_name, |tail_ty_1| {
                            let head_ty_1 = head_ty_1.weaken_into(&tail_ty_1.ctx());
                            let tail_ty_1 = head_ty_1.scope(|head_1| tail_ty_1.app(&head_1).to_ty());

                            tail_ty_0
                            .to_sigma(&head_name_0)
                            .to_term()
                            .equals(&tail_ty_1.to_sigma(&head_name_1).to_term())
                            .pi(&sigma_eq_name, |sigma_eq| {
                                sigma_eq.ctx().universe()
                            })
                        })
                    })
                })
            })
        })
    })
    .func(&motive_name, |motive| {
        motive
        .ctx()
        .name()
        .pi(&head_name_name, |head_name| {
            let head_name = head_name.to_name();

            head_name
            .ctx()
            .universe()
            .pi(&head_ty_name, |head_ty| {
                let head_ty = head_ty.to_ty();

                head_ty
                .pi(&head_name, |head| head.ctx().universe())
                .pi(&tail_ty_name, |tail_ty| {
                    let head_ty = head_ty.weaken_into(&tail_ty.ctx());

                    motive
                    .app(&head_name.to_term())
                    .app(&head_name.to_term())
                    .app(&head_ty.to_term())
                    .app(&head_ty.to_term())
                    .app(&tail_ty)
                    .app(&tail_ty)
                    .app(
                        &head_ty
                        .sigma(&head_name, |head| tail_ty.app(&head).to_ty())
                        .to_term()
                        .refl(),
                    )
                    .to_ty()
                })
            })
        })
        .func(&inhab_name, |inhab| {
            inhab
            .ctx()
            .name()
            .func(&head_name_0_name, |head_name_0| {
                let head_name_0 = head_name_0.to_name();

                head_name_0
                .ctx()
                .name()
                .func(&head_name_1_name, |head_name_1| {
                    let head_name_1 = head_name_1.to_name();

                    head_name_1
                    .ctx()
                    .universe()
                    .func(&head_ty_0_name, |head_ty_0| {
                        let head_ty_0 = head_ty_0.to_ty();

                        head_ty_0
                        .ctx()
                        .universe()
                        .func(&head_ty_1_name, |head_ty_1| {
                            let head_ty_1 = head_ty_1.to_ty();

                            head_ty_0
                            .weaken_into(&head_ty_1.ctx())
                            .pi(&head_name_0, |head_0| head_0.ctx().universe())
                            .func(&tail_ty_0_name, |tail_ty_0| {

                                head_ty_1
                                .weaken_into(&tail_ty_0.ctx())
                                .pi(&head_name_1, |head_1| head_1.ctx().universe())
                                .func(&tail_ty_1_name, |tail_ty_1| {
                                    let head_ty_0 = head_ty_0.weaken_into(&tail_ty_1.ctx());
                                    let head_ty_1 = head_ty_1.weaken_into(&tail_ty_1.ctx());

                                    head_ty_0
                                    .sigma(&head_name_0, |head_0| tail_ty_0.app(&head_0).to_ty())
                                    .to_term()
                                    .equals(
                                        &head_ty_1
                                        .sigma(&head_name_1, |head_1| tail_ty_1.app(&head_1).to_ty())
                                        .to_term()
                                    )
                                    .func(&sigma_eq_name, |sigma_eq| {
                                        sigma_eq
                                        .sigma_eq_name_injective()
                                        .cong(
                                            |head_name_0, head_name_1, head_name_eq| {
                                                let head_name_0 = head_name_0.to_name();
                                                let head_name_1 = head_name_1.to_name();

                                                head_ty_0
                                                .weaken_into(&head_name_eq.ctx())
                                                .pi(&head_name_0, |head| head.ctx().universe())
                                                .pi(&tail_ty_0_name, |tail_ty_0| {
                                                    head_ty_1
                                                    .weaken_into(&tail_ty_0.ctx())
                                                    .pi(&head_name_1, |head| head.ctx().universe())
                                                    .pi(&tail_ty_1_name, |tail_ty_1| {
                                                        head_ty_0
                                                        .weaken_into(&tail_ty_1.ctx())
                                                        .sigma(&head_name_0, |head| {
                                                            tail_ty_0.app(&head).to_ty()
                                                        })
                                                        .to_term()
                                                        .equals(
                                                            &head_ty_1
                                                            .weaken_into(&tail_ty_1.ctx())
                                                            .sigma(&head_name_1, |head| {
                                                                tail_ty_1.app(&head).to_ty()
                                                            })
                                                            .to_term()
                                                        )
                                                        .pi(&sigma_eq_name, |sigma_eq| {
                                                            motive
                                                            .app(&head_name_0.to_term())
                                                            .app(&head_name_1.to_term())
                                                            .app(&head_ty_0.to_term())
                                                            .app(&head_ty_1.to_term())
                                                            .app(&tail_ty_0)
                                                            .app(&tail_ty_1)
                                                            .app(&sigma_eq)
                                                            .to_ty()
                                                        })
                                                    })
                                                })
                                            },
                                            |head_name| {
                                                sigma_eq_cong_same_name(&head_name.to_name())
                                                .app(
                                                    &motive
                                                    .app(&head_name)
                                                    .app(&head_name)
                                                )
                                                .app(
                                                    &inhab
                                                    .app(&head_name)
                                                )
                                                .app(&head_ty_0.to_term())
                                                .app(&head_ty_1.to_term())
                                            },
                                        )
                                        .app(&tail_ty_0)
                                        .app(&tail_ty_1)
                                        .app(&sigma_eq)
                                    })
                                })
                            })
                        })
                    })
                })
            })
        })
    })
}

pub fn pi_eq_cong<S: Scheme>() -> Tm<S> {
    let arg_name_0_name = S::name_from_str("arg_name_0");
    let arg_name_1_name = S::name_from_str("arg_name_1");
    let arg_ty_0_name = S::name_from_str("Arg0");
    let arg_ty_1_name = S::name_from_str("Arg1");
    let res_ty_0_name = S::name_from_str("Res0");
    let res_ty_1_name = S::name_from_str("Res1");
    let pi_eq_name = S::name_from_str("pi_eq");
    let motive_name = S::name_from_str("Motive");

    let arg_name_name = S::name_from_str("arg_name");
    let arg_ty_name = S::name_from_str("Arg");
    let res_ty_name = S::name_from_str("Res");
    let inhab_name = S::name_from_str("inhab");
    
    let pi_eq_cong_same_name_same_arg_ty_same_res_ty = {
        |arg_name: &Name<S>, res_ty: &Scope<S, Ty<S>>| {
            res_ty
            .to_pi(&arg_name)
            .to_term()
            .equals(&res_ty.to_pi(&arg_name).to_term())
            .pi(&pi_eq_name, |pi_eq| pi_eq.ctx().universe())
            .func(&motive_name, |motive| {
                let res_ty = res_ty.weaken_into(&motive.ctx());

                motive
                .app(&res_ty.to_pi(&arg_name).to_term().refl())
                .to_ty()
                .func(&inhab_name, |inhab| {
                    let res_ty = res_ty.weaken_into(&inhab.ctx());

                    res_ty
                    .to_pi(&arg_name)
                    .to_term()
                    .equals(
                        &res_ty
                        .to_pi(&arg_name)
                        .to_term()
                    )
                    .func(&pi_eq_name, |pi_eq| {
                        res_ty
                        .weaken_into(&pi_eq.ctx())
                        .to_pi(&arg_name)
                        .to_term()
                        .refl()
                        .equality_contractible(&pi_eq)
                        .map_eq(|pi_eq| motive.app(&pi_eq))
                        .transport(&inhab)
                    })
                })
            })
        }
    };

    let pi_eq_cong_same_name_same_arg_ty = |arg_name: &Name<S>, arg_ty: &Ty<S>| -> Tm<S> {
        arg_ty
        .pi(&arg_name, |arg| arg.ctx().universe())
        .pi(&res_ty_0_name, |res_ty_0| {
            let arg_ty = arg_ty.weaken_into(&res_ty_0.ctx());
            let res_ty_0 = arg_ty.scope(|arg| res_ty_0.app(&arg).to_ty());

            arg_ty
            .pi(&arg_name, |arg| arg.ctx().universe())
            .pi(&res_ty_1_name, |res_ty_1| {
                let arg_ty = arg_ty.weaken_into(&res_ty_1.ctx());
                let res_ty_1 = arg_ty.scope(|arg| res_ty_1.app(&arg).to_ty());

                res_ty_0
                .to_pi(&arg_name)
                .to_term()
                .equals(&res_ty_1.to_pi(&arg_name).to_term())
                .pi(&pi_eq_name, |pi_eq| {
                    pi_eq.ctx().universe()
                })
            })
        })
        .func(&motive_name, |motive| {
            arg_ty
            .weaken_into(&motive.ctx())
            .pi(&arg_name, |arg| arg.ctx().universe())
            .pi(&res_ty_name, |res_ty| {
                let arg_ty = arg_ty.weaken_into(&res_ty.ctx());

                motive
                .app(&res_ty)
                .app(&res_ty)
                .app(
                    &arg_ty
                    .pi(&arg_name, |arg| res_ty.app(&arg).to_ty())
                    .to_term()
                    .refl(),
                )
                .to_ty()
            })
            .func(&inhab_name, |inhab| {
                arg_ty
                .weaken_into(&inhab.ctx())
                .pi(&arg_name, |arg| arg.ctx().universe())
                .func(&res_ty_0_name, |res_ty_0| {
                    let arg_ty = arg_ty.weaken_into(&res_ty_0.ctx());
                    let res_ty_0 = arg_ty.scope(|arg| res_ty_0.app(&arg).to_ty());

                    arg_ty
                    .weaken_into(&res_ty_0.ctx())
                    .pi(&arg_name, |arg| arg.ctx().universe())
                    .func(&res_ty_1_name, |res_ty_1| {
                        let arg_ty = arg_ty.weaken_into(&res_ty_1.ctx());
                        let res_ty_1 = arg_ty.scope(|arg| res_ty_1.app(&arg).to_ty());

                        res_ty_0
                        .weaken_into(&res_ty_1.ctx())
                        .to_pi(&arg_name)
                        .to_term()
                        .equals(
                            &res_ty_1
                            .to_pi(&arg_name)
                            .to_term(),
                        )
                        .func(&pi_eq_name, |pi_eq| {
                            pi_eq
                            .pi_eq_res_injective()
                            .cong(
                                |res_ty_0, res_ty_1, res_ty_eq| {
                                    let arg_ty = arg_ty.weaken_into(&res_ty_eq.ctx());

                                    arg_ty
                                    .pi(&arg_name, |arg| {
                                        res_ty_0.app(&arg).to_ty()
                                    })
                                    .to_term()
                                    .equals(
                                        &arg_ty
                                        .pi(&arg_name, |arg| {
                                            res_ty_1.app(&arg).to_ty()
                                        })
                                        .to_term()
                                    )
                                    .pi(&pi_eq_name, |pi_eq| {
                                        motive
                                        .app(&res_ty_0)
                                        .app(&res_ty_1)
                                        .app(&pi_eq)
                                        .to_ty()
                                    })
                                },
                                |res_ty| {
                                    let arg_ty = arg_ty.weaken_into(&res_ty.ctx());
                                    pi_eq_cong_same_name_same_arg_ty_same_res_ty(
                                        &arg_name.weaken_into(&res_ty.ctx()),
                                        &arg_ty.scope(|arg| res_ty.app(&arg).to_ty()),
                                    )
                                    .app(
                                        &motive
                                        .app(&res_ty)
                                        .app(&res_ty)
                                    )
                                    .app(
                                        &inhab
                                        .app(&res_ty)
                                    )
                                },
                            )
                            .app(&pi_eq)
                        })
                    })
                })
            })
        })
    };

    let pi_eq_cong_same_name = |arg_name: &Name<S>| -> Tm<S> {
        arg_name
        .ctx()
        .universe()
        .pi(&arg_ty_0_name, |arg_ty_0| {
            let arg_ty_0 = arg_ty_0.to_ty();

            arg_ty_0
            .ctx()
            .universe()
            .pi(&arg_ty_1_name, |arg_ty_1| {
                let arg_ty_1 = arg_ty_1.to_ty();

                arg_ty_0
                .weaken_into(&arg_ty_1.ctx())
                .pi(&arg_name, |arg_0| arg_0.ctx().universe())
                .pi(&res_ty_0_name, |res_ty_0| {
                    let arg_ty_0 = arg_ty_0.weaken_into(&res_ty_0.ctx());
                    let res_ty_0 = arg_ty_0.scope(|arg_0| res_ty_0.app(&arg_0).to_ty());

                    arg_ty_1
                    .weaken_into(&res_ty_0.ctx())
                    .pi(&arg_name, |arg_1| arg_1.ctx().universe())
                    .pi(&res_ty_1_name, |res_ty_1| {
                        let arg_ty_1 = arg_ty_1.weaken_into(&res_ty_1.ctx());
                        let res_ty_1 = arg_ty_1.scope(|arg_1| res_ty_1.app(&arg_1).to_ty());

                        res_ty_0
                        .to_pi(&arg_name)
                        .to_term()
                        .equals(&res_ty_1.to_pi(&arg_name).to_term())
                        .pi(&pi_eq_name, |pi_eq| {
                            pi_eq.ctx().universe()
                        })
                    })
                })
            })
        })
        .func(&motive_name, |motive| {
            motive
            .ctx()
            .universe()
            .pi(&arg_ty_name, |arg_ty| {
                let arg_ty = arg_ty.to_ty();

                arg_ty
                .pi(&arg_name, |arg| arg.ctx().universe())
                .pi(&res_ty_name, |res_ty| {
                    let arg_ty = arg_ty.weaken_into(&res_ty.ctx());

                    motive
                    .app(&arg_ty.to_term())
                    .app(&arg_ty.to_term())
                    .app(&res_ty)
                    .app(&res_ty)
                    .app(
                        &arg_ty
                        .pi(&arg_name, |arg| res_ty.app(&arg).to_ty())
                        .to_term()
                        .refl(),
                    )
                    .to_ty()
                })
            })
            .func(&inhab_name, |inhab| {
                inhab
                .ctx()
                .universe()
                .func(&arg_ty_0_name, |arg_ty_0| {
                    let arg_ty_0 = arg_ty_0.to_ty();

                    arg_ty_0
                    .ctx()
                    .universe()
                    .func(&arg_ty_1_name, |arg_ty_1| {
                        let arg_ty_1 = arg_ty_1.to_ty();

                        arg_ty_0
                        .weaken_into(&arg_ty_1.ctx())
                        .pi(&arg_name, |arg_0| arg_0.ctx().universe())
                        .func(&res_ty_0_name, |res_ty_0| {

                            arg_ty_1
                            .weaken_into(&res_ty_0.ctx())
                            .pi(&arg_name, |arg_1| arg_1.ctx().universe())
                            .func(&res_ty_1_name, |res_ty_1| {
                                let arg_ty_0 = arg_ty_0.weaken_into(&res_ty_1.ctx());
                                let arg_ty_1 = arg_ty_1.weaken_into(&res_ty_1.ctx());

                                arg_ty_0
                                .pi(&arg_name, |arg_0| res_ty_0.app(&arg_0).to_ty())
                                .to_term()
                                .equals(
                                    &arg_ty_1
                                    .pi(&arg_name, |arg_1| res_ty_1.app(&arg_1).to_ty())
                                    .to_term()
                                )
                                .func(&pi_eq_name, |pi_eq| {
                                    pi_eq
                                    .pi_eq_arg_injective()
                                    .cong(
                                        |arg_ty_0, arg_ty_1, _arg_ty_eq| {
                                            let arg_ty_0 = arg_ty_0.to_ty();
                                            let arg_ty_1 = arg_ty_1.to_ty();

                                            arg_ty_0
                                            .pi(&arg_name, |arg| arg.ctx().universe())
                                            .pi(&res_ty_0_name, |res_ty_0| {
                                                arg_ty_1
                                                .weaken_into(&res_ty_0.ctx())
                                                .pi(&arg_name, |arg| arg.ctx().universe())
                                                .pi(&res_ty_1_name, |res_ty_1| {
                                                    arg_ty_0
                                                    .weaken_into(&res_ty_1.ctx())
                                                    .pi(&arg_name, |arg| {
                                                        res_ty_0.app(&arg).to_ty()
                                                    })
                                                    .to_term()
                                                    .equals(
                                                        &arg_ty_1
                                                        .weaken_into(&res_ty_1.ctx())
                                                        .pi(&arg_name, |arg| {
                                                            res_ty_1.app(&arg).to_ty()
                                                        })
                                                        .to_term()
                                                    )
                                                    .pi(&pi_eq_name, |pi_eq| {
                                                        motive
                                                        .app(&arg_ty_0.to_term())
                                                        .app(&arg_ty_1.to_term())
                                                        .app(&res_ty_0)
                                                        .app(&res_ty_1)
                                                        .app(&pi_eq)
                                                        .to_ty()
                                                    })
                                                })
                                            })
                                        },
                                        |arg_ty| {
                                            pi_eq_cong_same_name_same_arg_ty(
                                                &arg_name.weaken_into(&arg_ty.ctx()),
                                                &arg_ty.to_ty(),
                                            )
                                            .app(
                                                &motive
                                                .app(&arg_ty)
                                                .app(&arg_ty)
                                            )
                                            .app(
                                                &inhab
                                                .app(&arg_ty)
                                            )
                                        },
                                    )
                                    .app(&res_ty_0)
                                    .app(&res_ty_1)
                                    .app(&pi_eq)
                                })
                            })
                        })
                    })
                })
            })
        })
    };

    Ctx::root()
    .name()
    .pi(&arg_name_0_name, |arg_name_0| {
        let arg_name_0 = arg_name_0.to_name();

        arg_name_0
        .ctx()
        .name()
        .pi(&arg_name_1_name, |arg_name_1| {
            let arg_name_1 = arg_name_1.to_name();

            arg_name_1
            .ctx()
            .universe()
            .pi(&arg_ty_0_name, |arg_ty_0| {
                let arg_ty_0 = arg_ty_0.to_ty();

                arg_ty_0
                .ctx()
                .universe()
                .pi(&arg_ty_1_name, |arg_ty_1| {
                    let arg_ty_1 = arg_ty_1.to_ty();

                    arg_ty_0
                    .weaken_into(&arg_ty_1.ctx())
                    .pi(&arg_name_0, |arg_0| arg_0.ctx().universe())
                    .pi(&res_ty_0_name, |res_ty_0| {
                        let arg_ty_0 = arg_ty_0.weaken_into(&res_ty_0.ctx());
                        let res_ty_0 = arg_ty_0.scope(|arg_0| res_ty_0.app(&arg_0).to_ty());

                        arg_ty_1
                        .weaken_into(&res_ty_0.ctx())
                        .pi(&arg_name_1, |arg_1| arg_1.ctx().universe())
                        .pi(&res_ty_1_name, |res_ty_1| {
                            let arg_ty_1 = arg_ty_1.weaken_into(&res_ty_1.ctx());
                            let res_ty_1 = arg_ty_1.scope(|arg_1| res_ty_1.app(&arg_1).to_ty());

                            res_ty_0
                            .to_pi(&arg_name_0)
                            .to_term()
                            .equals(&res_ty_1.to_pi(&arg_name_1).to_term())
                            .pi(&pi_eq_name, |pi_eq| {
                                pi_eq.ctx().universe()
                            })
                        })
                    })
                })
            })
        })
    })
    .func(&motive_name, |motive| {
        motive
        .ctx()
        .name()
        .pi(&arg_name_name, |arg_name| {
            let arg_name = arg_name.to_name();

            arg_name
            .ctx()
            .universe()
            .pi(&arg_ty_name, |arg_ty| {
                let arg_ty = arg_ty.to_ty();

                arg_ty
                .pi(&arg_name, |arg| arg.ctx().universe())
                .pi(&res_ty_name, |res_ty| {
                    let arg_ty = arg_ty.weaken_into(&res_ty.ctx());

                    motive
                    .app(&arg_name.to_term())
                    .app(&arg_name.to_term())
                    .app(&arg_ty.to_term())
                    .app(&arg_ty.to_term())
                    .app(&res_ty)
                    .app(&res_ty)
                    .app(
                        &arg_ty
                        .pi(&arg_name, |arg| res_ty.app(&arg).to_ty())
                        .to_term()
                        .refl(),
                    )
                    .to_ty()
                })
            })
        })
        .func(&inhab_name, |inhab| {
            inhab
            .ctx()
            .name()
            .func(&arg_name_0_name, |arg_name_0| {
                let arg_name_0 = arg_name_0.to_name();

                arg_name_0
                .ctx()
                .name()
                .func(&arg_name_1_name, |arg_name_1| {
                    let arg_name_1 = arg_name_1.to_name();

                    arg_name_1
                    .ctx()
                    .universe()
                    .func(&arg_ty_0_name, |arg_ty_0| {
                        let arg_ty_0 = arg_ty_0.to_ty();

                        arg_ty_0
                        .ctx()
                        .universe()
                        .func(&arg_ty_1_name, |arg_ty_1| {
                            let arg_ty_1 = arg_ty_1.to_ty();

                            arg_ty_0
                            .weaken_into(&arg_ty_1.ctx())
                            .pi(&arg_name_0, |arg_0| arg_0.ctx().universe())
                            .func(&res_ty_0_name, |res_ty_0| {

                                arg_ty_1
                                .weaken_into(&res_ty_0.ctx())
                                .pi(&arg_name_1, |arg_1| arg_1.ctx().universe())
                                .func(&res_ty_1_name, |res_ty_1| {
                                    let arg_ty_0 = arg_ty_0.weaken_into(&res_ty_1.ctx());
                                    let arg_ty_1 = arg_ty_1.weaken_into(&res_ty_1.ctx());

                                    arg_ty_0
                                    .pi(&arg_name_0, |arg_0| res_ty_0.app(&arg_0).to_ty())
                                    .to_term()
                                    .equals(
                                        &arg_ty_1
                                        .pi(&arg_name_1, |arg_1| res_ty_1.app(&arg_1).to_ty())
                                        .to_term()
                                    )
                                    .func(&pi_eq_name, |pi_eq| {
                                        pi_eq
                                        .pi_eq_name_injective()
                                        .cong(
                                            |arg_name_0, arg_name_1, arg_name_eq| {
                                                let arg_name_0 = arg_name_0.to_name();
                                                let arg_name_1 = arg_name_1.to_name();

                                                arg_ty_0
                                                .weaken_into(&arg_name_eq.ctx())
                                                .pi(&arg_name_0, |arg| arg.ctx().universe())
                                                .pi(&res_ty_0_name, |res_ty_0| {
                                                    arg_ty_1
                                                    .weaken_into(&res_ty_0.ctx())
                                                    .pi(&arg_name_1, |arg| arg.ctx().universe())
                                                    .pi(&res_ty_1_name, |res_ty_1| {
                                                        arg_ty_0
                                                        .weaken_into(&res_ty_1.ctx())
                                                        .pi(&arg_name_0, |arg| {
                                                            res_ty_0.app(&arg).to_ty()
                                                        })
                                                        .to_term()
                                                        .equals(
                                                            &arg_ty_1
                                                            .weaken_into(&res_ty_1.ctx())
                                                            .pi(&arg_name_1, |arg| {
                                                                res_ty_1.app(&arg).to_ty()
                                                            })
                                                            .to_term()
                                                        )
                                                        .pi(&pi_eq_name, |pi_eq| {
                                                            motive
                                                            .app(&arg_name_0.to_term())
                                                            .app(&arg_name_1.to_term())
                                                            .app(&arg_ty_0.to_term())
                                                            .app(&arg_ty_1.to_term())
                                                            .app(&res_ty_0)
                                                            .app(&res_ty_1)
                                                            .app(&pi_eq)
                                                            .to_ty()
                                                        })
                                                    })
                                                })
                                            },
                                            |arg_name| {
                                                pi_eq_cong_same_name(&arg_name.to_name())
                                                .app(
                                                    &motive
                                                    .app(&arg_name)
                                                    .app(&arg_name)
                                                )
                                                .app(
                                                    &inhab
                                                    .app(&arg_name)
                                                )
                                                .app(&arg_ty_0.to_term())
                                                .app(&arg_ty_1.to_term())
                                            },
                                        )
                                        .app(&res_ty_0)
                                        .app(&res_ty_1)
                                        .app(&pi_eq)
                                    })
                                })
                            })
                        })
                    })
                })
            })
        })
    })
}

pub fn case_eq<S: Scheme>() -> Tm<S> {
    let lhs_name_name = S::name_from_str("lhs_name");
    let lhs_ty_name = S::name_from_str("Lhs");
    let rhs_ty_name = S::name_from_str("Rhs");
    let sum_0_name = S::name_from_str("sum_0");
    let sum_1_name = S::name_from_str("sum_1");
    let sum_eq_name = S::name_from_str("sum_eq");

    Ctx::root()
    .name()
    .func(&lhs_name_name, |lhs_name| {
        let lhs_name = lhs_name.to_name();

        lhs_name
        .ctx()
        .universe()
        .func(&lhs_ty_name, |lhs_ty| {
            let lhs_ty = lhs_ty.to_ty();

            lhs_ty
            .ctx()
            .universe()
            .func(&rhs_ty_name, |rhs_ty| {
                let rhs_ty = rhs_ty.to_ty();
                let sum_ty = lhs_ty.sum(&lhs_name, &rhs_ty);

                sum_ty
                .func(&sum_0_name, |sum_0| {
                    sum_ty
                    .weaken_into(&sum_0.ctx())
                    .func(&sum_1_name, |sum_1| {
                        sum_0
                        .equals(&sum_1)
                        .func(&sum_eq_name, |sum_eq| {
                            sum_eq
                            .cong(
                                |sum_0, sum_1, _| {
                                    sum_0
                                    .case(
                                        |sum_0| sum_0.ctx().universe(),
                                        |lhs_0| {
                                            sum_1
                                            .weaken_into(&lhs_0.ctx())
                                            .case(
                                                |sum_1| sum_1.ctx().universe(),
                                                |lhs_1| lhs_0.equals(&lhs_1).to_term(),
                                                |rhs_1| rhs_1.ctx().never().to_term(),
                                            )
                                        },
                                        |rhs_0| {
                                            sum_1
                                            .weaken_into(&rhs_0.ctx())
                                            .case(
                                                |sum_1| sum_1.ctx().universe(),
                                                |lhs_1| lhs_1.ctx().never().to_term(),
                                                |rhs_1| rhs_0.equals(&rhs_1).to_term(),
                                            )
                                        },
                                    )
                                    .to_ty()
                                },
                                |sum| sum.case(
                                    |sum| {
                                        sum
                                        .case(
                                            |elim| elim.ctx().universe(),
                                            |lhs_0| {
                                                sum
                                                .weaken_into(&lhs_0.ctx())
                                                .case(
                                                    |elim| elim.ctx().universe(),
                                                    |lhs_1| lhs_0.equals(&lhs_1).to_term(),
                                                    |rhs_1| rhs_1.ctx().never().to_term(),
                                                )
                                            },
                                            |rhs_0| {
                                                sum
                                                .weaken_into(&rhs_0.ctx())
                                                .case(
                                                    |elim| elim.ctx().universe(),
                                                    |lhs_1| lhs_1.ctx().never().to_term(),
                                                    |rhs_1| rhs_0.equals(&rhs_1).to_term(),
                                                )
                                            },
                                        )
                                        .to_ty()
                                    },
                                    |lhs| lhs.refl(),
                                    |rhs| rhs.refl(),
                                )
                            )
                        })
                    })
                })
            })
        })
    })
}

pub fn pair_eq<S: Scheme>() -> Tm<S> {
    let head_name_name = S::name_from_str("head_name");
    let head_ty_name = S::name_from_str("Head");
    let tail_ty_name = S::name_from_str("Tail");
    let head_0_name = S::name_from_str("head_0");
    let head_1_name = S::name_from_str("head_1");
    let head_eq_name = S::name_from_str("head_eq");
    let tail_0_name = S::name_from_str("tail_0");
    let tail_1_name = S::name_from_str("tail_1");
    let tail_eq_name = S::name_from_str("tail_eq");

    Ctx::root()
    .name()
    .func(&head_name_name, |head_name| {
        let head_name = head_name.to_name();

        head_name
        .ctx()
        .universe()
        .func(&head_ty_name, |head_ty| {
            let head_ty = head_ty.to_ty();

            head_ty
            .pi(&head_name, |head| head.ctx().universe())
            .func(&tail_ty_name, |tail_ty| {
                let head_ty = head_ty.weaken_into(&tail_ty.ctx());
                let tail_ty = head_ty.scope(|head| tail_ty.app(&head).to_ty());

                head_ty
                .func(&head_0_name, |head_0| {
                    head_ty
                    .weaken_into(&head_0.ctx())
                    .func(&head_1_name, |head_1| {
                        head_0
                        .equals(&head_1)
                        .func(&head_eq_name, |head_eq| {
                            head_eq
                            .cong(
                                |head_0, head_1, head_eq| {
                                    tail_ty
                                    .bind(&head_0)
                                    .pi(&tail_0_name, |tail_0| {
                                        tail_ty
                                        .bind(&head_1)
                                        .weaken_into(&tail_0.ctx())
                                        .pi(&tail_1_name, |tail_1| {
                                            tail_ty
                                            .bind_eq(&head_eq)
                                            .heterogeneous_equal(&tail_0, &tail_1)
                                            .pi(&tail_eq_name, |_| {
                                                head_0
                                                .pair(&head_name, tail_ty.unbind(), &tail_0)
                                                .equals(
                                                    &head_1
                                                    .pair(&head_name, tail_ty.unbind(), &tail_1)
                                                )
                                            })
                                        })
                                    })
                                },
                                |head| {
                                    tail_ty
                                    .bind(&head)
                                    .func(&tail_0_name, |tail_0| {
                                        tail_ty
                                        .bind(&head)
                                        .weaken_into(&tail_0.ctx())
                                        .func(&tail_1_name, |tail_1| {
                                            tail_0
                                            .equals(&tail_1)
                                            .func(&tail_eq_name, |tail_eq| {
                                                tail_eq
                                                .cong(
                                                    |tail_0, tail_1, _| {
                                                        head
                                                        .pair(
                                                            &head_name,
                                                            tail_ty.unbind(),
                                                            &tail_0,
                                                        )
                                                        .equals(
                                                            &head
                                                            .pair(
                                                                &head_name,
                                                                tail_ty.unbind(),
                                                                &tail_1,
                                                            )
                                                        )
                                                    },
                                                    |tail| {
                                                        head
                                                        .pair(
                                                            &head_name,
                                                            tail_ty.unbind(),
                                                            &tail,
                                                        )
                                                        .refl()
                                                    },
                                                )
                                            })
                                        })
                                    })
                                },
                            )
                        })
                    })
                })
            })
        })
    })
}

/*
pub fn pair_eq<S: Scheme>() -> Tm<S> {
    let head_name_name = S::name_from_str("head_name");
    let head_ty_name = S::name_from_str("Head");
    let tail_ty_name = S::name_from_str("Tail");
    let pair_0_name = S::name_from_str("pair_0");
    let pair_1_name = S::name_from_str("pair_1");
    let pair_eq_name = S::name_from_str("pair_eq");

    Ctx::root()
    .name()
    .func(&head_name_name, |head_name| {
        let head_name = head_name.to_name();

        head_name
        .ctx()
        .universe()
        .func(&head_ty_name, |head_ty| {
            let head_ty = head_ty.to_ty();

            head_ty
            .pi(&head_name, |head| head.ctx().universe())
            .func(&tail_ty_name, |tail_ty| {
                let head_ty = head_ty.weaken_into(&tail_ty.ctx());
                let tail_ty = head_ty.scope(|head| tail_ty.app(&head).to_ty());

                let sigma_ty = tail_ty.to_sigma(&head_name);
                sigma_ty
                .func(&pair_0_name, |pair_0| {
                    sigma_ty
                    .weaken_into(&pair_0.ctx())
                    .func(&pair_1_name, |pair_1| {
                        pair_0
                        .equals(&pair_1)
                        .func(&pair_eq_name, |pair_eq| {
                            pair_eq
                            .cong(
                                |pair_0, pair_1, pair_eq| {
                                    pair_0
                                    .proj_head()
                                    .equals(&pair_1.p)
                                    .sigma(
                                },
                            )
                        })
                    })
                })
            })
        })
    })
}
*/

pub fn cong<S: Scheme>() -> Tm<S> {
    let ty_name = S::name_from_str("Ty");
    let val_0_name = S::name_from_str("val_0");
    let val_1_name = S::name_from_str("val_1");
    let val_eq_name = S::name_from_str("val_eq");
    let val_name = S::name_from_str("val");
    let motive_name = S::name_from_str("Motive");
    let inhab_name = S::name_from_str("inhab");

    Ctx::root()
    .universe()
    .func(&ty_name, |ty| {
        let ty = ty.to_ty();

        ty
        .pi(&val_0_name, |val_0| {
            ty
            .weaken_into(&val_0.ctx())
            .pi(&val_1_name, |val_1| {
                val_0
                .equals(&val_1)
                .pi(&val_eq_name, |val_eq| {
                    val_eq.ctx().universe()
                })
            })
        })
        .func(&motive_name, |motive| {
            ty
            .weaken_into(&motive.ctx())
            .pi(&val_name, |val| {
                motive
                .app(&val)
                .app(&val)
                .app(&val.refl())
                .to_ty()
            })
            .func(&inhab_name, |inhab| {
                ty
                .weaken_into(&inhab.ctx())
                .func(&val_0_name, |val_0| {
                    ty
                    .weaken_into(&val_0.ctx())
                    .func(&val_1_name, |val_1| {
                        val_0
                        .equals(&val_1)
                        .func(&val_eq_name, |val_eq| {
                            val_eq
                            .cong(
                                |val_0, val_1, val_eq| {
                                    motive
                                    .app(&val_0)
                                    .app(&val_1)
                                    .app(&val_eq)
                                    .to_ty()
                                },
                                |val| inhab.app(&val),
                            )
                        })
                    })
                })
            })
        })
    })
}

pub fn fold<S: Scheme>() -> Tm<S> {
    let elim_name = S::name_from_str("elim");
    let motive_name = S::name_from_str("Motive");
    let on_zero_name = S::name_from_str("on_zero");
    let on_succ_name = S::name_from_str("on_succ");
    let state_name = S::name_from_str("state");

    Ctx::root()
    .nat()
    .pi(&elim_name, |elim| elim.ctx().universe())
    .func(&motive_name, |motive| {
        motive
        .app(&motive.ctx().zero())
        .to_ty()
        .func(&on_zero_name, |on_zero| {
            on_zero
            .ctx()
            .nat()
            .pi(&elim_name, |elim| {
                motive
                .app(&elim)
                .to_ty()
                .pi(&state_name, |_state| {
                    motive
                    .app(&elim.succs(1u32))
                    .to_ty()
                })
            })
            .func(&on_succ_name, |on_succ| {
                on_succ
                .ctx()
                .nat()
                .func(&elim_name, |elim| {
                    elim
                    .for_loop(
                        |elim| motive.app(&elim).to_ty(),
                        &on_zero,
                        |elim, state| on_succ.app(&elim).app(&state),
                    )
                })
            })
        })
    })
}

