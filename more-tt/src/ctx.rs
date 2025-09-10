use crate::priv_prelude::*;

#[extension(pub trait CtxExt)]
impl<S: Scheme> Ctx<S> {
    fn function_extensionality_ty(&self) -> Ty<S> {
        self
        .universe()
        .pi(|arg_ty| {
            let arg_ty = arg_ty.to_ty();
            arg_ty
            .pi(|arg| arg.ctx().universe())
            .pi(|res_ty| {
                let res_ty = {
                    arg_ty
                    .weaken_into(&res_ty.ctx())
                    .scope(|arg| res_ty.app(&arg).to_ty())
                };
                arg_ty
                .weaken_into(&res_ty.ctx())
                .pi(|arg| res_ty.bind(&arg))
                .pi(|func_0| {
                    arg_ty
                    .weaken_into(&func_0.ctx())
                    .pi(|arg| res_ty.bind(&arg))
                    .pi(|func_1| {
                        arg_ty
                        .weaken_into(&func_1.ctx())
                        .pi(|arg| func_0.app(&arg).equals(&func_1.app(&arg)))
                        .pi(|_pointwise_eq| {
                            func_0.equals(&func_1)
                        })
                    })
                })
            })
        })
    }
}

