use crate::priv_prelude::*;

fn under_init_ctx<T>(func: impl FnOnce(&Ctx, &mut VarNames) -> T) -> T {
    let ctx = Ctx::root();
    let mut var_names = VarNames::new();

    let funext_ty = ctx.function_extensionality_ty();
    funext_ty
    .with_cons(|term| {
        func(&term.ctx(), &mut var_names)
    })
}

fn check_and_solve_infer_scope(infer_scope: InferScope<Tm>, max_recursion_depth: u32) -> Tm {
    let solution = {
        let mut infer_scope = infer_scope.clone();
        match infer_scope.try_solve(max_recursion_depth) {
            Some(solution) => solution,
            None => {
                let constraint_ty = infer_scope.constraint_ty();
                panic!("failed to solve constraint: {:?}", constraint_ty);
            },
        }
    };
    let Some(recursion_depth) = max_recursion_depth.checked_sub(2) else {
        return solution;
    };

    for depth in 0..recursion_depth {
        let depth = depth + 1;
        let mut infer_scope = infer_scope.clone();
        let constraint_ty = infer_scope.constraint_ty();
        if infer_scope.try_solve(depth).is_some() {
            panic!("solved in only {} steps", depth);
        }
        let new_constraint_ty = infer_scope.constraint_ty();
        if new_constraint_ty == constraint_ty {
            continue;
        }
        if let Some(_) = infer_scope.try_solve(max_recursion_depth - depth - 1) {
            panic!("able to solve in fewer steps with multiple calls");
        };
    }
    solution
}

#[allow(unused)]
fn debug_check_inference_steps(infer_scope: InferScope<Tm>, max_depth: u32) {
    let mut max_progress = 0;
    let mut max_progress_constraint_ty = infer_scope.constraint_ty();
    println!("constraint_ty == {:?}", max_progress_constraint_ty);
    for depth in 0..max_depth {
        let depth = depth + 1;
        println!("trying depth {}", depth);
        let mut infer_scope = infer_scope.clone();
        match infer_scope.try_solve(depth) {
            None => {
                let new_constraint_ty = infer_scope.constraint_ty();
                if new_constraint_ty != max_progress_constraint_ty {
                    max_progress = depth;
                    max_progress_constraint_ty = infer_scope.constraint_ty();
                    println!("constraint_ty == {:?}", max_progress_constraint_ty);
                }
            },
            Some(_) => {
                panic!("solved in {} steps", depth);
            },
        }
    }
    panic!(
        "failed to solve in {} steps. max progress in {} steps: {:?}",
        max_depth, max_progress, max_progress_constraint_ty,
    );
}

#[allow(unused)]
fn inspect_reduction_behaviour(infer_scope: InferScope<Tm>, max_depth: u32) {
    let mut infer_scope = infer_scope.clone();
    loop {
        let old_constraint_ty = infer_scope.constraint_ty();
        println!("constraint_ty == {:?}", old_constraint_ty);

        let mut depth = 0;
        loop {
            if depth == max_depth {
                panic!("failed to make more progress in {} steps", max_depth);
            }
            depth += 1;
            if let Some(_) = infer_scope.try_solve(depth) {
                panic!("solved");
            }
            let new_constraint_ty = infer_scope.constraint_ty();
            if new_constraint_ty != old_constraint_ty {
                break;
            }
        }
    }
}

#[test]
fn elab_let_stmt() {
    let src = Arc::from("\
        let x = 3;\n\
        let y: x == 3 = refl x;\n\
    ");
    let expr = parse_prec_stmt(&src).unwrap();

    under_init_ctx(|ctx, var_names| {
        let infer_scope = ctx.elab_prec_stmt(var_names, &expr).unwrap();
        let got = check_and_solve_infer_scope(infer_scope, 1);
        assert_eq!(got, ctx.unit_term());
    })
}

#[test]
fn elab_func_type() {
    let src = Arc::from("Fn(arg: ArgTy) -> Foo(arg_renamed = arg)");
    let expr = parse_prec_stmt(&src).unwrap();

    let arg_name = TagScheme::name_from_str("arg");
    let arg_ty_name = TagScheme::name_from_str("ArgTy");
    let foo_name = TagScheme::name_from_str("Foo");
    let arg_renamed_name = TagScheme::name_from_str("arg_renamed");

    under_init_ctx(|ctx, var_names| {
        ctx
        .universe()
        .named_with_cons(var_names, &arg_ty_name, |var_names, arg_ty| {
            let arg_ty = arg_ty.to_ty();

            arg_ty
            .pi(&arg_renamed_name, |arg| arg.ctx().universe())
            .named_with_cons(var_names, &foo_name, |var_names, foo| {
                let arg_ty = arg_ty.weaken_into(&foo.ctx());

                let infer_scope = foo.ctx().elab_prec_stmt(var_names, &expr).unwrap();
                let got = check_and_solve_infer_scope(infer_scope, 1);

                let expected = {
                    arg_ty
                    .pi(&arg_name, |arg| {
                        foo
                        .weaken_into(&arg.ctx())
                        .app(&arg)
                        .to_ty()
                    })
                    .to_term()
                };

                assert_eq!(got, expected);
            })
        })
    })
}

#[test]
fn elab_func_term() {
    let src = Arc::from("fn(arg: ArgTy) => foo(arg_renamed = arg)");
    let expr = parse_prec_stmt(&src).unwrap();

    let arg_name = TagScheme::name_from_str("arg");
    let arg_ty_name = TagScheme::name_from_str("ArgTy");
    let res_ty_name = TagScheme::name_from_str("ResTy");
    let foo_name = TagScheme::name_from_str("foo");
    let arg_renamed_name = TagScheme::name_from_str("arg_renamed");

    under_init_ctx(|ctx, var_names| {
        ctx
        .universe()
        .named_with_cons(var_names, &arg_ty_name, |var_names, arg_ty| {
            let arg_ty = arg_ty.to_ty();

            arg_ty
            .pi(&arg_name, |arg| arg.ctx().universe())
            .named_with_cons(var_names, &res_ty_name, |var_names, res_ty| {
                let arg_ty = arg_ty.weaken_into(&res_ty.ctx());
                let res_ty = {
                    arg_ty
                    .scope(|arg| res_ty.app(&arg).to_ty())
                };

                arg_ty
                .pi(&arg_renamed_name, |arg| res_ty.bind(&arg))
                .named_with_cons(var_names, &foo_name, |var_names, foo| {
                    let arg_ty = arg_ty.weaken_into(&foo.ctx());

                    let infer_scope = foo.ctx().elab_prec_stmt(var_names, &expr).unwrap();
                    let got = check_and_solve_infer_scope(infer_scope, 1);

                    let expected = {
                        arg_ty
                        .func(&arg_name, |arg| {
                            foo
                            .weaken_into(&arg.ctx())
                            .app(&arg)
                        })
                    };

                    assert_eq!(got, expected);
                })
            })
        })
    })
}

#[test]
fn elab_equal() {
    let src = Arc::from("x == y");
    let expr = parse_prec_stmt(&src).unwrap();

    let ty_name = TagScheme::name_from_str("Ty");
    let x_name = TagScheme::name_from_str("x");
    let y_name = TagScheme::name_from_str("y");

    under_init_ctx(|ctx, var_names| {
        ctx
        .universe()
        .named_with_cons(var_names, &ty_name, |var_names, ty| {
            let ty = ty.to_ty();

            ty
            .named_with_cons(var_names, &x_name, |var_names, x| {
                ty
                .weaken_into(&x.ctx())
                .named_with_cons(var_names, &y_name, |var_names, y| {
                    let infer_scope = y.ctx().elab_prec_stmt(var_names, &expr).unwrap();
                    let got = check_and_solve_infer_scope(infer_scope, 1);
                    assert_eq!(got, x.equals(&y).to_term());
                })
            })
        });
    })
}

#[test]
fn elab_add_mul() {
    let src = Arc::from("{2 + x} * {3 + y}");
    let expr = parse_prec_stmt(&src).unwrap();

    let x_name = TagScheme::name_from_str("x");
    let y_name = TagScheme::name_from_str("y");

    under_init_ctx(|ctx, var_names| {
        ctx
        .nat()
        .named_with_cons(var_names, &x_name, |var_names, x| {
            x
            .ctx()
            .nat()
            .named_with_cons(var_names, &y_name, |var_names, y| {
                let infer_scope = y.ctx().elab_prec_stmt(var_names, &expr).unwrap();
                let got = check_and_solve_infer_scope(infer_scope, 1);
                assert_eq!(
                    got,
                    x
                    .mul(&y)
                    .add(&x.mul(&y.ctx().nat_constant(3u32)))
                    .add(&y.mul(&y.ctx().nat_constant(2u32)))
                    .add(&y.ctx().nat_constant(6u32))
                );
            })
        })
    })
}

#[ignore] // not solvable yet
#[test]
fn elab_pat_refl() {
    let src = Arc::from("\
        let flipped: x1 == x0 = {
            let refl x = x_eq;
            refl x
        };
    ");
    let expr = parse_prec_stmt(&src).unwrap();

    let ty_name = TagScheme::name_from_str("Ty");
    let x0_name = TagScheme::name_from_str("x0");
    let x1_name = TagScheme::name_from_str("x1");
    let x_eq_name = TagScheme::name_from_str("x_eq");

    under_init_ctx(|ctx, var_names| {
        ctx
        .universe()
        .named_with_cons(var_names, &ty_name, |var_names, ty| {
            let ty = ty.to_ty();

            ty
            .named_with_cons(var_names, &x0_name, |var_names, x0| {
                ty
                .weaken_into(&x0.ctx())
                .named_with_cons(var_names, &x1_name, |var_names, x1| {
                    x0
                    .equals(&x1)
                    .named_with_cons(var_names, &x_eq_name, |var_names, x_eq| {
                        let infer_scope = x_eq.ctx().elab_prec_stmt(var_names, &expr).unwrap();
                        debug_check_inference_steps(infer_scope.clone(), 10);
                        let got = check_and_solve_infer_scope(infer_scope, 1);

                        assert_eq!(
                            got,
                            x_eq.ctx().unit_term(),
                        );
                    })
                })
            })
        });
    })
}

#[test]
fn elab_refl() {
    let src = Arc::from("refl val");
    let expr = parse_prec_stmt(&src).unwrap();

    let ty_name = TagScheme::name_from_str("Ty");
    let val_name = TagScheme::name_from_str("val");

    under_init_ctx(|ctx, var_names| {
        ctx
        .universe()
        .named_with_cons(var_names, &ty_name, |var_names, ty| {
            let ty = ty.to_ty();

            ty
            .named_with_cons(var_names, &val_name, |var_names, val| {
                let infer_scope = {
                    val
                    .ctx()
                    .elab_prec_stmt(var_names, &expr)
                    .unwrap()
                };
                let got = check_and_solve_infer_scope(infer_scope, 1);
                assert_eq!(got, val.refl());
            })
        })
    })
}

#[test]
fn elab_var() {
    let var_name = TagScheme::name_from_str("x");
    let src = Arc::from("x");
    let expr = parse_prec_stmt(&src).unwrap();

    under_init_ctx(|ctx, var_names| {
        ctx
        .nat()
        .named_with_cons(var_names, &var_name, |var_names, x| {
            let infer_scope = {
                x
                .ctx()
                .elab_prec_stmt(var_names, &expr)
                .unwrap()
            };
            let got = check_and_solve_infer_scope(infer_scope, 1);
            assert_eq!(got, x)
        });
    })
}

#[test]
fn elab_nat() {
    let val = 23u32;
    let src = format!("{}", val);
    let src = Arc::from(src.as_str());
    let expr = parse_prec_stmt(&src).unwrap();

    under_init_ctx(|ctx, var_names| {
        let infer_scope = ctx.elab_prec_stmt(var_names, &expr).unwrap();
        let got = check_and_solve_infer_scope(infer_scope, 1);
        assert_eq!(got, ctx.nat_constant(val));
    })
}

#[test]
fn elab_type_type() {
    let src = Arc::from("Type");
    let expr = parse_prec_stmt(&src).unwrap();

    under_init_ctx(|ctx, var_names| {
        let infer_scope = ctx.elab_prec_stmt(var_names, &expr).unwrap();
        let got = check_and_solve_infer_scope(infer_scope, 1);
        assert_eq!(got, ctx.universe().to_term());
    })
}

#[test]
fn elab_nat_type() {
    let src = Arc::from("Nat");
    let expr = parse_prec_stmt(&src).unwrap();

    under_init_ctx(|ctx, var_names| {
        let infer_scope = ctx.elab_prec_stmt(var_names, &expr).unwrap();
        let got = check_and_solve_infer_scope(infer_scope, 1);
        assert_eq!(got, ctx.nat().to_term());
    })
}

#[test]
fn elab_never_type() {
    let src = Arc::from("enum {}");

    let expr = parse_prec_stmt(&src).unwrap();

    under_init_ctx(|ctx, var_names| {
        let infer_scope = ctx.elab_prec_stmt(var_names, &expr).unwrap();
        let got = check_and_solve_infer_scope(infer_scope, 1);
        assert_eq!(got, ctx.never().to_term());
    })
}

#[test]
fn elab_enum_type() {
    let src = Arc::from("\
        enum {
            variant_0: Ty0,
            variant_1: Ty1,
            variant_2: Ty2,
        }
    ");

    let expr = parse_prec_stmt(&src).unwrap();

    let variant_0_name = TagScheme::name_from_str("variant_0");
    let variant_1_name = TagScheme::name_from_str("variant_1");
    let variant_2_name = TagScheme::name_from_str("variant_2");
    let ty_0_name = TagScheme::name_from_str("Ty0");
    let ty_1_name = TagScheme::name_from_str("Ty1");
    let ty_2_name = TagScheme::name_from_str("Ty2");

    under_init_ctx(|ctx, var_names| {
        ctx
        .universe()
        .named_with_cons(var_names, &ty_0_name, |var_names, ty_0| {
            let ty_0 = ty_0.to_ty();

            ty_0
            .ctx()
            .universe()
            .named_with_cons(var_names, &ty_1_name, |var_names, ty_1| {
                let ty_1 = ty_1.to_ty();

                ty_1
                .ctx()
                .universe()
                .named_with_cons(var_names, &ty_2_name, |var_names, ty_2| {
                    let ty_2 = ty_2.to_ty();

                    let infer_scope = ty_2.ctx().elab_prec_stmt(var_names, &expr).unwrap();
                    let got = check_and_solve_infer_scope(infer_scope, 1);

                    let expected = {
                        ty_0
                        .sum(
                            &variant_0_name,
                            &ty_1
                            .sum(
                                &variant_1_name,
                                &ty_2
                                .sum(&variant_2_name, &ty_2.ctx().never()),
                            )
                        )
                        .to_term()
                    };
                    assert_eq!(got, expected);
                })
            })
        })
    })
}

#[test]
fn elab_app_shorthand() {
    let src = Arc::from("func(arg)");
    let expr = parse_prec_stmt(&src).unwrap();

    let arg_ty_name = TagScheme::name_from_str("Arg");
    let res_ty_name = TagScheme::name_from_str("Res");
    let func_name = TagScheme::name_from_str("func");
    let arg_name = TagScheme::name_from_str("arg");

    under_init_ctx(|ctx, var_names| {
        ctx
        .universe()
        .named_with_cons(var_names, &arg_ty_name, |var_names, arg_ty| {
            let arg_ty = arg_ty.to_ty();
            
            arg_ty
            .pi(&arg_name, |arg| arg.ctx().universe())
            .named_with_cons(var_names, &res_ty_name, |var_names, res_ty| {
                let arg_ty = arg_ty.weaken_into(&res_ty.ctx());
                let res_ty = arg_ty.scope(|arg| res_ty.app(&arg).to_ty());

                arg_ty
                .pi(&arg_name, |arg| res_ty.bind(&arg))
                .named_with_cons(var_names, &func_name, |var_names, func| {
                    arg_ty
                    .weaken_into(&func.ctx())
                    .named_with_cons(var_names, &arg_name, |var_names, arg| {
                        let func = func.weaken_into(&arg.ctx());

                        let infer_scope = arg.ctx().elab_prec_stmt(var_names, &expr).unwrap();
                        let got = check_and_solve_infer_scope(infer_scope, 1);

                        let expected = func.app(&arg);
                        assert_eq!(got, expected);
                    })
                })
            })
        })
    })
}

//#[ignore] // fix iso bug in more-tt
#[test]
fn elab_sigma_type() {
    let src = Arc::from("\
        struct {
            field_0: Ty0,
            field_1: Ty1,
            field_2: Ty2,
        }
    ");

    let expr = parse_prec_stmt(&src).unwrap();

    let ty_0_name = TagScheme::name_from_str("Ty0");
    let ty_1_name = TagScheme::name_from_str("Ty1");
    let ty_2_name = TagScheme::name_from_str("Ty2");
    let field_0_name = TagScheme::name_from_str("field_0");
    let field_1_name = TagScheme::name_from_str("field_1");
    let field_2_name = TagScheme::name_from_str("field_2");

    under_init_ctx(|ctx, var_names| {
        ctx
        .universe()
        .named_with_cons(var_names, &ty_0_name, |var_names, ty_0| {
            let ty_0 = ty_0.to_ty();

            ty_0
            .ctx()
            .universe()
            .named_with_cons(var_names, &ty_1_name, |var_names, ty_1| {
                let ty_1 = ty_1.to_ty();

                ty_1
                .ctx()
                .universe()
                .named_with_cons(var_names, &ty_2_name, |var_names, ty_2| {
                    let ty_0 = ty_0.weaken_into(&ty_2.ctx());
                    let ty_1 = ty_1.weaken_into(&ty_2.ctx());
                    let ty_2 = ty_2.to_ty();

                    let infer_scope = ty_2.ctx().elab_prec_stmt(var_names, &expr).unwrap();
                    let got = check_and_solve_infer_scope(infer_scope, 1);

                    let expected = {
                        ty_0
                        .sigma(&field_0_name, |_| {
                            ty_1
                            .sigma(&field_1_name, |_| {
                                ty_2
                                .sigma(&field_2_name, |_| {
                                    Ctx::root().unit_ty()
                                })
                            })
                        })
                        .to_term()
                    };
                    assert_eq!(got, expected);
                })
            })
        })
    })
}

