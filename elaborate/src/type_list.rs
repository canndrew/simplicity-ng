use crate::priv_prelude::*;

lazy_static! {
    static ref LEN_NAME: Name = TagScheme::name_from_str("num_inferred_injections");
    static ref LHS_NAME_NAME: Name = TagScheme::name_from_str("lhs_name");
    static ref INFERRED_LHS_NAME_NAME: Name = TagScheme::name_from_str("inferred_lhs_name");
    static ref INFERRED_LHS_TY_NAME: Name = TagScheme::name_from_str("InferredLhs");
    static ref INJECTION_NAME: Name = TagScheme::name_from_str("injection");
    static ref LHS_NAMES_EQ_NAME: Name = TagScheme::name_from_str("lhs_names_eq");
    static ref LHS_NAMES_NOT_EQ_NAME: Name = TagScheme::name_from_str("lhs_names_not_eq");
    static ref INJECTIONS_NAME: Name = TagScheme::name_from_str("injections");
    static ref LHS_TY_NAME: Name = TagScheme::name_from_str("Lhs");
    static ref RHS_TY_NAME: Name = TagScheme::name_from_str("Rhs");


    static ref INJECTIONS_TY_OF_LEN: Tm = {
        Ctx::root()
        .name()
        .func(&LHS_NAME_NAME, |lhs_name| {
            lhs_name
            .ctx()
            .nat()
            .func(&LEN_NAME, |len| {
                len
                .for_loop(
                    |len| len.ctx().universe(),
                    &len.ctx().unit_ty().to_term(),
                    |len, state| {
                        len
                        .ctx()
                        .name()
                        .sigma(&INFERRED_LHS_NAME_NAME, |inferred_lhs_name| {
                            lhs_name
                            .equals(&inferred_lhs_name)
                            .pi(&LHS_NAMES_EQ_NAME, |lhs_names_eq| lhs_names_eq.ctx().never())
                            .sigma(&LHS_NAMES_NOT_EQ_NAME, |lhs_names_not_eq| {
                                lhs_names_not_eq
                                .ctx()
                                .universe()
                                .sigma(&INFERRED_LHS_TY_NAME, |inferred_lhs_ty| {
                                    inferred_lhs_ty.ctx().unit_ty()
                                })
                            })
                        })
                        .sigma(&INJECTION_NAME, |_| state.to_ty())
                        .to_term()
                    },
                )
            })
        })
    };

    static ref TY_OF_APPLY_INJECTIONS_OF_LEN: Tm = {
        Ctx::root()
        .name()
        .func(&LHS_NAME_NAME, |lhs_name| {
            lhs_name
            .ctx()
            .universe()
            .func(&LHS_TY_NAME, |lhs_ty| {
                let lhs_ty = lhs_ty.to_ty();

                lhs_ty
                .ctx()
                .universe()
                .func(&RHS_TY_NAME, |rhs_ty| {
                    let rhs_ty = rhs_ty.to_ty();

                    rhs_ty
                    .ctx()
                    .nat()
                    .func(&LEN_NAME, |len| {
                        len
                        .for_loop(
                            |len| {
                                INJECTIONS_TY_OF_LEN
                                .app(&lhs_name)
                                .app(&len)
                                .to_ty()
                                .pi(&INJECTIONS_NAME, |injections| {
                                    injections.ctx().universe()
                                })
                            },
                            &INJECTIONS_TY_OF_LEN
                            .app(&lhs_name)
                            .app(&rhs_ty.ctx().zero())
                            .to_ty()
                            .func(&INJECTIONS_NAME, |_| {
                                lhs_ty.sum(&lhs_name.to_name(), &rhs_ty).to_term()
                            }),
                            |len, state| {
                                INJECTIONS_TY_OF_LEN
                                .app(&lhs_name)
                                .app(&len.succs(1u32))
                                .to_ty()
                                .func(&INJECTIONS_NAME, |injections| {
                                    let injection = injections.proj_head();
                                    let injections = injections.proj_tail();
                                    let inferred_lhs_name = injection.proj_head().to_name();
                                    let inferred_lhs_ty = injections.proj_tail().proj_tail().to_ty();

                                    inferred_lhs_ty
                                    .sum(
                                        &inferred_lhs_name,
                                        &state.app(&injections).to_ty(),
                                    )
                                    .to_term()
                                })
                            },
                        )
                    })
                })
            })
        })
    };

    static ref APPLY_INJECTIONS_OF_LEN: Tm = {
        Ctx::root()
        .name()
        .func(&LHS_NAME_NAME, |lhs_name| {
            lhs_name
            .ctx()
            .universe()
            .func(&LHS_TY_NAME, |lhs_ty| {

                lhs_ty
                .ctx()
                .universe()
                .func(&RHS_TY_NAME, |rhs_ty| {
                    lhs_ty
                    .weaken_into(&rhs_ty.ctx())
                    .to_ty()
                    .func(&lhs_name.to_name(), |lhs| {
                        lhs
                        .ctx()
                        .nat()
                        .func(&LEN_NAME, |len| {
                            len
                            .for_loop(
                                |len| {
                                    INJECTIONS_TY_OF_LEN
                                    .app(&lhs_name)
                                    .app(&len)
                                    .to_ty()
                                    .pi(&INJECTIONS_NAME, |injections| {
                                        TY_OF_APPLY_INJECTIONS_OF_LEN
                                        .app(&lhs_name)
                                        .app(&lhs_ty)
                                        .app(&rhs_ty)
                                        .app(&len)
                                        .app(&injections)
                                        .to_ty()
                                    })
                                },
                                &INJECTIONS_TY_OF_LEN
                                .app(&lhs_name)
                                .app(&lhs.ctx().zero())
                                .to_ty()
                                .func(&INJECTIONS_NAME, |_| {
                                    lhs.inj_lhs(&lhs_name.to_name(), &rhs_ty.to_ty())
                                }),
                                |len, state| {
                                    INJECTIONS_TY_OF_LEN
                                    .app(&lhs_name)
                                    .app(&len.succs(1u32))
                                    .to_ty()
                                    .func(&INJECTIONS_NAME, |injections| {
                                        let injection = injections.proj_head();
                                        let injections = injections.proj_tail();
                                        let inferred_lhs_name = injection.proj_head().to_name();
                                        let inferred_lhs_ty = {
                                            injections
                                            .proj_tail()
                                            .proj_tail()
                                            .to_ty()
                                        };

                                        state
                                        .app(&injections)
                                        .inj_rhs(&inferred_lhs_name, &inferred_lhs_ty)
                                    })
                                },
                            )
                        })
                    })
                })
            })
        })
    };

    static ref INJECTIONS_TY: Tm = {
        Ctx::root()
        .name()
        .func(&LHS_NAME_NAME, |lhs_name| {
            lhs_name
            .ctx()
            .nat()
            .sigma(&LEN_NAME, |len| {
                INJECTIONS_TY_OF_LEN
                .app(&lhs_name)
                .app(&len)
                .to_ty()
            })
            .to_term()
        })
    };

    static ref TY_OF_APPLY_INJECTIONS: Tm = {
        Ctx::root()
        .name()
        .func(&LHS_NAME_NAME, |lhs_name| {
            lhs_name
            .ctx()
            .universe()
            .func(&LHS_TY_NAME, |lhs_ty| {
                lhs_ty
                .ctx()
                .universe()
                .func(&RHS_TY_NAME, |rhs_ty| {
                    INJECTIONS_TY
                    .app(&lhs_name)
                    .to_ty()
                    .weaken_into(&rhs_ty.ctx())
                    .func(&INJECTIONS_NAME, |injections| {
                        TY_OF_APPLY_INJECTIONS_OF_LEN
                        .app(&lhs_name)
                        .app(&lhs_ty)
                        .app(&rhs_ty)
                        .app(&injections.proj_head())
                        .app(&injections.proj_tail())
                    })
                })
            })
        })
    };

    static ref APPLY_INJECTIONS: Tm = {
        Ctx::root()
        .name()
        .func(&LHS_NAME_NAME, |lhs_name| {
            lhs_name
            .ctx()
            .universe()
            .func(&LHS_TY_NAME, |lhs_ty| {

                lhs_ty
                .ctx()
                .universe()
                .func(&RHS_TY_NAME, |rhs_ty| {

                    lhs_ty
                    .weaken_into(&rhs_ty.ctx())
                    .to_ty()
                    .func(&lhs_name.to_name(), |lhs| {
                        INJECTIONS_TY
                        .app(&lhs_name)
                        .to_ty()
                        .func(&INJECTIONS_NAME, |injections| {
                            APPLY_INJECTIONS_OF_LEN
                            .app(&lhs_name)
                            .app(&lhs_ty)
                            .app(&rhs_ty)
                            .app(&lhs)
                            .app(&injections.proj_head())
                            .app(&injections.proj_tail())
                        })
                    })
                })
            })
        })
    };
}

pub fn injections_ty(lhs_name: &Name) -> Ty {
    INJECTIONS_TY
    .app(&lhs_name.to_term())
    .to_ty()
}

pub fn apply_injections(
    lhs_name: &Name,
    lhs_term: &Tm,
    rhs_ty: &Ty,
    injections: &Tm,
) -> Tm {
    let (lhs_name, lhs_term, rhs_ty, injections) = Ctx::into_common_ctx((
        lhs_name, lhs_term, rhs_ty, injections,
    ));
    APPLY_INJECTIONS
    .app(&lhs_name.to_term())
    .app(&lhs_term.ty().to_term())
    .app(&rhs_ty.to_term())
    .app(&injections)
}






/*
#[extension(pub(crate) trait CtxTypeListExt)]
impl Ctx {
    fn type_list_ty(&self) -> Ty {
        self.nat().sigma(|len| len.type_list_of_len_ty())
    }
}

#[extension(pub(crate) trait TmTypeListExt)]
impl Tm {
    fn map_type_list(
        &self,
        map: impl FnOnce(Ty) -> Ty,
    ) -> Tm {
        let len = self.proj_head();
        let type_list = self.proj_tail();
        len.map_type_list_of_len(&type_list, map)
    }

    fn type_list_of_len_ty(&self) -> Ty {
        self
        .for_loop(
            |len| len.ctx().universe(),
            &self.ctx().unit_ty().to_term(),
            |len, state| {
                len
                .ctx()
                .universe()
                .sigma(|_| state.to_ty())
                .to_term()
            },
        )
        .to_ty()
    }

    fn map_type_list_of_len(
        &self,
        type_list: &Tm,
        map: impl FnOnce(Ty) -> Ty,
    ) -> Tm {
        let (len, type_list) = Ctx::into_common_ctx(self, type_list);
        let map = len.ctx().universe().scope(|ty| map(ty.to_ty()));

        len
        .for_loop(
            |len| {
                len
                .type_list_of_len_ty()
                .pi(|_| len.type_list_of_len_ty())
            },
            &len.ctx().unit_ty().func(|unit| unit.ctx().unit_term()),
            |len, state| {
                len
                .succs(1u32)
                .type_list_of_len_ty()
                .func(|type_list| {
                    let first_ty = type_list.proj_head();
                    let type_list = type_list.proj_tail();

                    let first_ty = map.bind(&first_ty);

                    first_ty
                    .to_term()
                    .pair(
                        |_| len.type_list_of_len_ty(),
                        &state.app(&type_list),
                    )
                })
            },
        )
        .app(&type_list)
    }

    fn big_sigma_of_len_ty(
        &self,
        type_list: &Tm,
    ) -> Ty {
        let (len, type_list) = Ctx::into_common_ctx(self, type_list);

        len
        .for_loop(
            |len| {
                len
                .type_list_of_len_ty()
                .pi(|type_list| type_list.ctx().universe())
            },
            &len.ctx().unit_ty().func(|unit| unit.ctx().unit_ty().to_term()),
            |len, state| {
                len
                .succs(1u32)
                .type_list_of_len_ty()
                .func(|type_list| {
                    let first_ty = type_list.proj_head().to_ty();
                    let type_list = type_list.proj_tail();

                    first_ty
                    .sigma(|_| state.app(&type_list).to_ty())
                    .to_term()
                })
            },
        )
        .app(&type_list)
        .to_ty()
    }
}
*/

