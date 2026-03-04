use crate::priv_prelude::*;

#[extension(pub trait CtxExt)]
impl<S: Scheme> Ctx<S> {
    fn with_tys<const NUM_TYS: usize, T>(
        &self,
        func: impl FnOnce([Ty<S>; NUM_TYS]) -> T,
    ) -> T {
        fn with_tys_inner<const NUM_TYS: usize, S: Scheme, T>(
            ctx: &Ctx<S>,
            tys: Vec<Ty<S>>,
            func: impl FnOnce([Ty<S>; NUM_TYS]) -> T,
        ) -> T {
            if tys.len() == NUM_TYS {
                let mut tys = tys.into_iter().map(|ty| ty.weaken_into(ctx));
                let tys = std::array::from_fn(|_| {
                    tys.next().unwrap()
                });
                func(tys)
            } else {
                ctx
                .universe()
                .with_cons(move |ty| {
                    let mut tys = tys;
                    tys.push(ty.to_ty());
                    with_tys_inner(&ty.ctx(), tys, func)
                })
            }
        }

        with_tys_inner(self, Vec::new(), func)
    }

    fn function_extensionality_ty(&self) -> Ty<S> {
        let arg_name_name = S::name_from_str("arg_name");
        let arg_ty_name = S::name_from_str("Arg");
        let res_ty_name = S::name_from_str("Res");
        let func_0_name = S::name_from_str("func_0");
        let func_1_name = S::name_from_str("func_1");
        let pointwise_eq_name = S::name_from_str("pointwise_eq");

        self
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
                    let res_ty = {
                        arg_ty
                        .weaken_into(&res_ty.ctx())
                        .scope(|arg| res_ty.app(&arg).to_ty())
                    };
                    arg_ty
                    .weaken_into(&res_ty.ctx())
                    .pi(&arg_name, |arg| res_ty.bind(&arg))
                    .pi(&func_0_name, |func_0| {
                        arg_ty
                        .weaken_into(&func_0.ctx())
                        .pi(&arg_name, |arg| res_ty.bind(&arg))
                        .pi(&func_1_name, |func_1| {
                            arg_ty
                            .weaken_into(&func_1.ctx())
                            .pi(&arg_name, |arg| func_0.app(&arg).equals(&func_1.app(&arg)))
                            .pi(&pointwise_eq_name, |_pointwise_eq| {
                                func_0.equals(&func_1)
                            })
                        })
                    })
                })
            })
        })
    }

    fn try_get_funext(&self) -> Option<Tm<S>> {
        let funext_ty = self.function_extensionality_ty();
        for index in 0..self.len() {
            let term = self.var(index);
            if term.ty() == funext_ty {
                return Some(term);
            }
        }
        None
    }
}

