use crate::priv_prelude::*;

#[test]
fn map_functor_sum() {
    Ctx::<StringScheme>::root()
    .with_names(|[lhs_name, input_name]| {
        lhs_name
        .ctx()
        .with_tys(|[input_ty, output_ty]| {
            input_ty
            .pi(&input_name, |_| output_ty.clone())
            .with_cons(|mapping| {
                same_ctx!(&input_ty, &mapping);
                let mapping = input_ty.scope(|input| mapping.app(&input));

                let functor = {
                    input_ty
                    .ctx()
                    .universe()
                    .scope(|var_ty| {
                        let var_ty = var_ty.to_ty();
                        var_ty.sum(&lhs_name, &var_ty)
                    })
                };
                let scope = functor.try_map_functor(&mapping).unwrap();

                input_ty
                .with_cons(|input| {
                    assert_eq!(
                        scope.bind(&input.inj_lhs(&lhs_name, &input_ty)),
                        mapping.bind(&input).inj_lhs(&lhs_name, &output_ty),
                    );
                    assert_eq!(
                        scope.bind(&input.inj_rhs(&lhs_name, &input_ty)),
                        mapping.bind(&input).inj_rhs(&lhs_name, &output_ty),
                    );
                });
            })
        })
    })
}

#[test]
fn map_functor_sigma() {
    Ctx::<StringScheme>::root()
    .with_names(|[head_name, input_name]| {
        head_name
        .ctx()
        .with_tys(|[input_ty, output_ty]| {
            input_ty
            .pi(&input_name, |_| output_ty.clone())
            .with_cons(|mapping| {
                same_ctx!(&input_ty, &mapping);
                let mapping = input_ty.scope(|input| mapping.app(&input));

                let functor = {
                    input_ty
                    .ctx()
                    .universe()
                    .scope(|var_ty| {
                        let var_ty = var_ty.to_ty();
                        var_ty.sigma(&head_name, |_| var_ty.clone())
                    })
                };
                let scope = functor.try_map_functor(&mapping).unwrap();

                input_ty
                .with_cons(|head| {
                    same_ctx!(&input_ty, &head);
                    
                    input_ty
                    .with_cons(|tail| {
                        same_ctx!(&head, &tail);

                        assert_eq!(
                            scope
                            .bind(&head.pair(&head_name, |_| input_ty.clone(), &tail)),
                            mapping
                            .bind(&head)
                            .pair(
                                &head_name,
                                |_| output_ty.clone(),
                                &mapping.bind(&tail),
                            )
                        );
                    })
                })
            })
        })
    })
}

#[test]
fn map_functor_pi() {
    Ctx::<StringScheme>::root()
    .with_names(|[arg_name, input_name]| {
        arg_name
        .ctx()
        .with_tys(|[arg_ty, input_ty, output_ty]| {
            input_ty
            .pi(&input_name, |_| output_ty.clone())
            .with_cons(|mapping| {
                same_ctx!(&arg_ty, &input_ty, &mapping);
                let mapping = input_ty.scope(|input| mapping.app(&input));

                let functor = {
                    input_ty
                    .ctx()
                    .universe()
                    .scope(|var_ty| {
                        same_ctx!(&arg_ty, &var_ty);

                        let var_ty = var_ty.to_ty();
                        arg_ty.pi(&arg_name, |_| var_ty.clone())
                    })
                };
                let scope = functor.try_map_functor(&mapping).unwrap();

                arg_ty
                .pi(&arg_name, |_| input_ty.clone())
                .with_cons(|input| {
                    same_ctx!(&arg_ty, &input);

                    assert_eq!(
                        scope.bind(&input),
                        arg_ty
                        .func(&arg_name, |arg| {
                            mapping.bind(&input.app(&arg))
                        }),
                    );
                })
            })
        })
    })
}

