use crate::priv_prelude::*;

#[derive(Debug)]
pub enum ElabError {
    UnknownVar(Ident),
}

pub struct VarNames {
    pub(crate) names: Vec<(Name, usize)>,
}

impl VarNames {
    pub fn new() -> VarNames {
        VarNames {
            names: Vec::new(),
        }
    }
}

#[extension(pub trait CtxElabExt)]
impl Ctx {
    fn new_ty_metavar(&self, metavar_tag: MetavarTag) -> InferScope<Ty> {
        self
        .universe()
        .new_metavar(metavar_tag)
        .map(|_, ty| ty.to_ty())
    }

    fn elab_prec_stmt(
        &self,
        var_names: &mut VarNames,
        prec_stmt: &ast::PrecStmt,
    ) -> Result<InferScope<Tm>, ElabError> {
        match prec_stmt {
            ast::PrecStmt::Let(let_stmt) => self.elab_let_stmt(var_names, let_stmt),
            ast::PrecStmt::Blank(_span) => {
                Ok(self.unit_term().pure())
            },
            ast::PrecStmt::Other(prec_func) => self.elab_prec_func(var_names, prec_func),
        }
    }

    fn elab_prec_func(
        &self,
        var_names: &mut VarNames,
        prec_func: &ast::PrecFunc,
    ) -> Result<InferScope<Tm>, ElabError> {
        match prec_func {
            ast::PrecFunc::FuncType(func_type) => self.elab_expr_func_type(var_names, func_type),
            ast::PrecFunc::FuncTerm(func_term) => self.elab_expr_func_term(var_names, func_term),
            ast::PrecFunc::Other(prec_equal) => self.elab_prec_equal(var_names, prec_equal),
        }
    }

    fn elab_prec_equal(
        &self,
        var_names: &mut VarNames,
        prec_equal: &ast::PrecEqual,
    ) -> Result<InferScope<Tm>, ElabError> {
        match prec_equal {
            ast::PrecEqual::Equal(expr_equal) => self.elab_expr_equal(var_names, expr_equal),
            ast::PrecEqual::Other(prec_add) => self.elab_prec_add(var_names, prec_add),
        }
    }

    fn elab_prec_add(
        &self,
        var_names: &mut VarNames,
        prec_add: &ast::PrecAdd,
    ) -> Result<InferScope<Tm>, ElabError> {
        match prec_add {
            ast::PrecAdd::Add(expr_add) => self.elab_expr_add(var_names, expr_add),
            ast::PrecAdd::Other(prec_mul) => self.elab_prec_mul(var_names, prec_mul),
        }
    }

    fn elab_prec_mul(
        &self,
        var_names: &mut VarNames,
        prec_mul: &ast::PrecMul,
    ) -> Result<InferScope<Tm>, ElabError> {
        match prec_mul {
            ast::PrecMul::Mul(expr_mul) => self.elab_expr_mul(var_names, expr_mul),
            ast::PrecMul::Other(prec_inj) => self.elab_prec_inj(var_names, prec_inj),
        }
    }

    fn elab_prec_inj(
        &self,
        var_names: &mut VarNames,
        prec_inj: &ast::PrecInj,
    ) -> Result<InferScope<Tm>, ElabError> {
        match prec_inj {
            ast::PrecInj::Inj(expr_inj) => self.elab_expr_inj(var_names, expr_inj),
            ast::PrecInj::Refl(expr_refl) => self.elab_expr_refl(var_names, expr_refl),
            ast::PrecInj::Other(prec_proj) => self.elab_prec_proj(var_names, prec_proj),
        }
    }

    fn elab_prec_proj(
        &self,
        var_names: &mut VarNames,
        prec_proj: &ast::PrecProj,
    ) -> Result<InferScope<Tm>, ElabError> {
        match prec_proj {
            ast::PrecProj::Proj(expr_proj) => self.elab_expr_proj(var_names, expr_proj),
            ast::PrecProj::Other(prec_app) => self.elab_prec_app(var_names, prec_app),
        }
    }

    fn elab_prec_app(
        &self,
        var_names: &mut VarNames,
        prec_app: &ast::PrecApp,
    ) -> Result<InferScope<Tm>, ElabError> {
        match prec_app {
            ast::PrecApp::App(expr_app) => self.elab_expr_app(var_names, expr_app),
            ast::PrecApp::Other(prec_atom) => self.elab_prec_atom(var_names, prec_atom),
        }
    }

    fn elab_prec_atom(
        &self,
        var_names: &mut VarNames,
        prec_atom: &ast::PrecAtom,
    ) -> Result<InferScope<Tm>, ElabError> {
        match prec_atom {
            ast::PrecAtom::Var(name) => {
                self.elab_var(var_names, name)
            },
            ast::PrecAtom::Nat(spanned_val) => {
                Ok(self.elab_nat(spanned_val))
            },
            ast::PrecAtom::Match(expr_match) => {
                self.elab_expr_match(var_names, expr_match)
            },
            ast::PrecAtom::StructType(expr_struct_type) => {
                self.elab_expr_struct_type(var_names, expr_struct_type)
            },
            ast::PrecAtom::StructTerm(expr_struct_term) => {
                self.elab_expr_struct_term(var_names, expr_struct_term)
            },
            ast::PrecAtom::EnumType(expr_enum_type) => {
                self.elab_expr_enum_type(var_names, expr_enum_type)
            },
            ast::PrecAtom::Braced(spanned_prec_stmt) => {
                self.elab_prec_stmt(var_names, &spanned_prec_stmt.inner)
            },
        }
    }

    fn elab_let_stmt(
        &self,
        var_names: &mut VarNames,
        let_stmt: &Spanned<ast::LetStmt>,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::LetStmt { var_pat, var_args_opt, var_ty_opt, var_expr, body } = &let_stmt.inner;

        let var_term = match var_args_opt {
            None => self.elab_prec_func(var_names, var_expr)?,
            Some(var_args) => {
                self.elab_func_term_args_and_body(var_names, &var_args.inner, var_expr)?
            },
        };

        var_term
        .try_flat_map(|_, var_term| {
            let var_term = match var_ty_opt {
                None => var_term.pure(),
                Some(var_ty) => {
                    let let_ty_is_ty_metavar = MetavarTag::LetTypeIsType {
                        let_ty_span: var_ty.span(),
                    };
                    let let_term_ty_is_expected_ty_metavar = {
                        MetavarTag::LetTermTypeIsExpectedType {
                            let_ty_span: var_ty.span(),
                            var_term_span: var_expr.span(),
                        }
                    };

                    var_term
                    .ctx()
                    .elab_prec_func(var_names, var_ty)?
                    .flat_map(|_, var_ty| {
                        var_ty
                        .cast_to_ty(let_ty_is_ty_metavar)
                        .flat_map(|_, var_ty| {
                            var_term
                            .weaken_into(&var_ty.ctx())
                            .cast(&var_ty, let_term_ty_is_expected_ty_metavar)
                        })
                    })
                },
            };

            var_term
            .try_flat_map(|_, var_term| {
                var_term
                .ctx()
                .elab_pat_prec_inj(var_names, var_pat, &|ctx, var_names| {
                    ctx.elab_prec_stmt(var_names, body)
                })?
                .flat_map(|_, scope| {
                    let let_term_ty_matches_pat_ty = MetavarTag::LetTermTypeMatchesPatType {
                        var_term_span: var_expr.span(),
                        var_ty_span_opt: var_ty_opt.as_ref().map(|var_ty| var_ty.span()),
                        pat_span: var_pat.span(),
                    };

                    var_term
                    .weaken_into(&scope.ctx())
                    .cast(&scope.var_ty(), let_term_ty_matches_pat_ty)
                    .map(|_, var_term| {
                        scope
                        .weaken_into(&var_term.ctx())
                        .bind(&var_term)
                    })
                    .flatten()
                })
                .wrap_ok()
            })
        })
    }

    fn elab_expr_func_type(
        &self,
        var_names: &mut VarNames,
        expr_func_ty: &Spanned<ast::ExprFuncType>,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::ExprFuncType { args, return_ty } = &expr_func_ty.inner;

        Ok(
            self
            .elab_func_ty_args_and_res_ty(var_names, &args.inner, return_ty)?
            .map(|_, ty| ty.to_term())
        )
    }

    fn elab_expr_func_term(
        &self,
        var_names: &mut VarNames,
        expr_func_term: &Spanned<ast::ExprFuncTerm>,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::ExprFuncTerm { args, body } = &expr_func_term.inner;
        self.elab_func_term_args_and_body(var_names, &args.inner, body)
    }

    fn elab_func_term_args_and_body(
        &self,
        var_names: &mut VarNames,
        args: &[Spanned<ast::FuncTermArg>],
        body: &ast::PrecFunc,
    ) -> Result<InferScope<Tm>, ElabError> {
        match args.split_first() {
            None => self.elab_prec_func(var_names, body),
            Some((arg, args)) => {
                let (arg_name, arg_ty) = self.elab_func_term_arg(var_names, arg)?;

                arg_ty
                .try_flat_map(|_, arg_ty| {
                    arg_ty
                    .try_named_scope(var_names, &arg_name, |var_names, arg| {
                        arg
                        .ctx()
                        .elab_func_term_args_and_body(var_names, args, body)
                    })?
                    .lift_infer_scope(&arg_name)
                    .map(|_, scope| scope.to_func(&arg_name))
                    .wrap_ok()
                })
            },
        }
    }

    fn elab_func_ty_args_and_res_ty(
        &self,
        var_names: &mut VarNames,
        args: &[Spanned<ast::FuncTermArg>],
        res_ty: &ast::PrecFunc,
    ) -> Result<InferScope<Ty>, ElabError> {
        match args.split_first() {
            None => {
                let func_res_ty_is_ty_metavar = MetavarTag::FuncResTyIsTy {
                    res_ty_span: res_ty.span(),
                };
                Ok(
                    self
                    .elab_prec_func(var_names, res_ty)?
                    .flat_map(|_, res_ty| res_ty.cast_to_ty(func_res_ty_is_ty_metavar)),
                )
            },
            Some((arg, args)) => {
                let (arg_name, arg_ty) = self.elab_func_term_arg(var_names, arg)?;

                let ty = {
                    arg_ty
                    .try_map(|_, arg_ty| {
                        arg_ty
                        .try_named_scope(var_names, &arg_name, |var_names, arg| {
                            arg
                            .ctx()
                            .elab_func_ty_args_and_res_ty(var_names, args, res_ty)
                        })?
                        .lift_infer_scope(&arg_name)
                        .wrap_ok()
                    })?
                    .flatten()
                    .map(|_, pi_scope| pi_scope.to_pi(&arg_name))
                };
                Ok(ty)
            },
        }
    }

    fn elab_func_term_arg(
        &self,
        var_names: &mut VarNames,
        func_term_arg: &Spanned<ast::FuncTermArg>,
    ) -> Result<(Name, InferScope<Ty>), ElabError> {
        let ast::FuncTermArg { arg_name, arg_ty_opt } = &func_term_arg.inner;

        let arg_ty = match arg_ty_opt {
            None => {
                let func_term_elided_arg_ty_metavar = MetavarTag::FuncTermElidedArgType {
                    arg_name: arg_name.clone(),
                };
                self.new_ty_metavar(func_term_elided_arg_ty_metavar)
            },
            Some(func_term_arg_ty) => {
                self.elab_func_term_arg_ty(var_names, func_term_arg_ty)?
            },
        };
        let arg_name = Name::from_ident(arg_name.clone());
        Ok((arg_name, arg_ty))
    }

    fn elab_func_term_arg_ty(
        &self,
        var_names: &mut VarNames,
        func_term_arg_ty: &ast::FuncTermArgTy,
    ) -> Result<InferScope<Ty>, ElabError> {
        let ast::FuncTermArgTy { args_opt, ty } = func_term_arg_ty;

        match args_opt {
            None => {
                let func_arg_ty_is_ty_metavar = MetavarTag::FuncArgTyIsTy {
                    arg_ty_span: ty.span(),
                };

                self
                .elab_prec_func(var_names, ty)?
                .flat_map(|_, ty| ty.cast_to_ty(func_arg_ty_is_ty_metavar))
                .wrap_ok()
            },
            Some(args) => {
                self.elab_func_ty_args_and_res_ty(var_names, &args.inner, ty)
            },
        }
    }

    fn elab_expr_equal(
        &self,
        var_names: &mut VarNames,
        expr_equal: &Spanned<ast::ExprEqual>,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::ExprEqual { eq_expr_0, eq_expr_1 } = &expr_equal.inner;

        let eq_term_0 = self.elab_prec_add(var_names, eq_expr_0)?;
        let eq_term_1 = self.elab_prec_add(var_names, eq_expr_1)?;
        let eq_tys_match_metavar = MetavarTag::EqualsLeftTypeMatchesRightType {
            equals_span: expr_equal.span(),
            eq_term_0_span: eq_expr_0.span(),
            eq_term_1_span: eq_expr_1.span(),
        };
        let term = {
            eq_term_0
            .flat_map(|_, eq_term_0| {
                eq_term_1
                .weaken_into(&eq_term_0.ctx())
                .flat_map(|_, eq_term_1| {
                    eq_term_0
                    .weaken_into(&eq_term_1.ctx())
                    .cast(&eq_term_1.ty(), eq_tys_match_metavar)
                    .map(|_, eq_term_0| {
                        eq_term_0.equals(&eq_term_1).to_term()
                    })
                })
            })
        };
        Ok(term)
    }

    fn elab_expr_add(
        &self,
        var_names: &mut VarNames,
        expr_add: &Spanned<ast::ExprAdd>,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::ExprAdd { lhs, rhs } = &expr_add.inner;

        let lhs_is_nat_metavar = MetavarTag::AddArgumentTypeIsNat {
            argument_span: lhs.span(),
        };
        let rhs_is_nat_metavar = MetavarTag::AddArgumentTypeIsNat {
            argument_span: rhs.span(),
        };

        self
        .elab_prec_add(var_names, lhs)?
        .try_flat_map(|_, lhs| {
            lhs
            .cast(&lhs.ctx().nat(), lhs_is_nat_metavar)
            .try_flat_map(|_, lhs| {
                lhs
                .ctx()
                .elab_prec_mul(var_names, rhs)?
                .flat_map(|_, rhs| {
                    rhs
                    .cast(&rhs.ctx().nat(), rhs_is_nat_metavar)
                    .map(|_, rhs| {
                        lhs.add(&rhs)
                    })
                })
                .wrap_ok()
            })
        })
    }

    fn elab_expr_mul(
        &self,
        var_names: &mut VarNames,
        expr_mul: &Spanned<ast::ExprMul>,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::ExprMul { lhs, rhs } = &expr_mul.inner;

        let lhs_is_nat_metavar = MetavarTag::MulArgumentTypeIsNat {
            argument_span: lhs.span(),
        };
        let rhs_is_nat_metavar = MetavarTag::MulArgumentTypeIsNat {
            argument_span: rhs.span(),
        };

        self
        .elab_prec_mul(var_names, lhs)?
        .try_flat_map(|_, lhs| {
            lhs
            .cast(&lhs.ctx().nat(), lhs_is_nat_metavar)
            .try_flat_map(|_, lhs| {
                lhs
                .ctx()
                .elab_prec_inj(var_names, rhs)?
                .flat_map(|_, rhs| {
                    rhs
                    .cast(&rhs.ctx().nat(), rhs_is_nat_metavar)
                    .map(|_, rhs| {
                        lhs.mul(&rhs)
                    })
                })
                .wrap_ok()
            })
        })
    }

    fn elab_expr_inj(
        &self,
        var_names: &mut VarNames,
        expr_inj: &Spanned<ast::ExprInj>,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::ExprInj { variant_name, payload } = &expr_inj.inner;

        let rhs_ty_metavar = MetavarTag::InjectionRhsType {
            lhs_name: variant_name.clone(),
            inj_span: expr_inj.span(),
            payload_span: payload.span(),
        };
        let injections_metavar = MetavarTag::Injections {
            lhs_name: variant_name.clone(),
            inj_span: expr_inj.span(),
            payload_span: payload.span(),
        };

        let lhs_name = Name::from_ident(variant_name.clone());

        self
        .elab_prec_inj(var_names, payload)?
        .flat_map(|_, lhs_term| {
            lhs_term
            .ctx()
            .new_ty_metavar(rhs_ty_metavar)
            .flat_map(|_, rhs_ty| {
                crate::type_list::injections_ty(&lhs_name)
                .new_metavar(injections_metavar)
                .map(|_, injections| {
                    crate::type_list::apply_injections(
                        &lhs_name, &lhs_term, &rhs_ty, &injections,
                    )
                })
            })
        })
        .wrap_ok()
    }

    fn elab_expr_refl(
        &self,
        var_names: &mut VarNames,
        expr_refl: &Spanned<ast::ExprRefl>,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::ExprRefl { eq_expr } = &expr_refl.inner;

        self
        .elab_prec_inj(var_names, &eq_expr)?
        .map(|_, eq_term| eq_term.refl())
        .wrap_ok()
    }

    fn elab_expr_proj(
        &self,
        _var_names: &mut VarNames,
        _expr_proj: &Spanned<ast::ExprProj>,
    ) -> Result<InferScope<Tm>, ElabError> {
        /*
        let ast::ExprProj { base, field_name } = &expr_proj.inner;

        let full_sigma_ty_metavar = MetavarTag::ProjectionFullType {
            base_span: base.span(),
            field_name: field_name.clone(),
        };
        let base_ty_is_sigma_metavar = MetavarTag::ProjectionBaseTypeIsSigma {
            base_span: base.span(),
            field_name: field_name.clone(),
        };
        let head_ty_metavar = MetavarTag::ProjectionHeadType {
            base_span: base.span(),
            field_name: field_name.clone(),
        };
        let tail_ty_metavar = MetavarTag::ProjectionTailType {
            base_span: base.span(),
            field_name: field_name.clone(),
        };
        let coercion_metavar = MetavarTag::ProjectionCoercion {
            base_span: base.span(),
            field_name: field_name.clone(),
        };

        self
        .elab_prec_proj(base)?
        .flat_map(|_, base| {
            base
            .ctx()
            .new_ty_metavar(full_sigma_ty_metavar)
            .flat_map(|_, full_sigma_ty| {
                base
                .cast(&full_sigma_ty, base_ty_is_sigma_metavar)
                .flat_map(|_, base| {
                    base
                    .ctx()
                    .new_ty_metavar(head_ty_metavar)
                    .flat_map(|_, head_ty| {
                        head_ty
                        .name_tag(field_name)
                        .pi(|head| head.ctx().universe())
                        .new_metavar(tail_ty_metavar)
                        .flat_map(|_, tail_ty| {
                            let head_ty = head_ty.weaken_into(&tail_ty.ctx());
                            let tail_ty = {
                                head_ty
                                .name_tag(&field_name)
                                .scope(|head| tail_ty.app(&head).to_ty())
                            };

                            full_sigma_ty
                            .weaken_into(&tail_ty.ctx())
                            .pi(|_| tail_ty.to_sigma())
                            .new_metavar(coercion_metavar)
                            .map(|_, coercion| {
                                coercion.app(&base).proj_head().strip_tag()
                            })
                        })
                    })
                })
            })
        })
        .wrap_ok()
        */
        todo!()
    }

    fn elab_expr_app(
        &self,
        var_names: &mut VarNames,
        expr_app: &Spanned<ast::ExprApp>,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::ExprApp { func, args } = &expr_app.inner;

        let mut term = self.elab_prec_app(var_names, func)?;
        for func_app_arg in args.inner.iter() {
            let (arg_name, arg) = self.elab_func_app_arg(var_names, func_app_arg)?;
            let app_elim_ty_is_func = MetavarTag::AppElimTypeIsFunc {
                elim_span: func.span(),
                arg_span: func_app_arg.span(),
            };
            let app_res_ty_metavar = MetavarTag::AppResType {
                elim_span: func.span(),
                arg_span: func_app_arg.span(),
            };

            term = {
                term
                .flat_map(|_, func| {
                    arg
                    .weaken_into(&func.ctx())
                    .flat_map(|_, arg| {
                        arg
                        .ty()
                        .pi(&arg_name, |arg| arg.ctx().universe())
                        .new_metavar(app_res_ty_metavar)
                        .flat_map(|_, res_ty| {
                            let func = func.weaken_into(&res_ty.ctx());
                            let arg = arg.weaken_into(&res_ty.ctx());
                            let res_ty = {
                                arg
                                .ty()
                                .scope(|arg| res_ty.app(&arg).to_ty())
                            };

                            func
                            .cast(&res_ty.to_pi(&arg_name), app_elim_ty_is_func)
                            .map(|_, func| {
                                func.app(&arg)
                            })
                        })
                    })
                })
            };
        }
        Ok(term)
    }

    fn elab_func_app_arg(
        &self,
        var_names: &mut VarNames,
        func_app_arg: &Spanned<ast::FuncAppArg>,
    ) -> Result<(Name, InferScope<Tm>), ElabError> {
        let ast::FuncAppArg { arg_name, arg_expr_opt } = &func_app_arg.inner;

        let arg = match arg_expr_opt {
            None => {
                self.elab_var(var_names, arg_name)?
            },
            Some(arg_expr) => {
                self.elab_func_app_arg_expr(var_names, arg_expr)?
            },
        };
        let arg_name = Name::from_ident(arg_name.clone());
        Ok((arg_name, arg))
    }

    fn elab_func_app_arg_expr(
        &self,
        var_names: &mut VarNames,
        func_app_arg_expr: &ast::FuncAppArgExpr,
    ) -> Result<InferScope<Tm>, ElabError> {
        let ast::FuncAppArgExpr { args_opt, expr } = func_app_arg_expr;
        match args_opt {
            None => self.elab_prec_func(var_names, expr),
            Some(args) => {
                self.elab_func_term_args_and_body(var_names, &args.inner, expr)
            },
        }
    }
    
    fn elab_expr_match(
        &self,
        var_names: &mut VarNames,
        expr_match: &Spanned<ast::ExprMatch>,
    ) -> Result<InferScope<Tm>, ElabError> {
        fn elab_match_branches(
            ctx: &Ctx,
            var_names: &mut VarNames,
            branches: &[Spanned<ast::MatchBranch>],
            end_span: &Span,
            elim_name: &Name,
        ) -> Result<InferScope<Scope<Tm>>, ElabError> {
            match branches.split_first() {
                None => {
                    let motive_metavar = MetavarTag::EmptyMatchMotive {
                        match_end_span: end_span.clone(),
                    };

                    ctx
                    .never()
                    .pi(elim_name, |never| never.ctx().universe())
                    .new_metavar(motive_metavar)
                    .map(|_, motive| {
                        motive
                        .ctx()
                        .never()
                        .scope(|never| {
                            never.explode(|never| motive.app(&never).to_ty())
                        })
                    })
                    .wrap_ok()
                },
                Some((branch, branches)) => {
                    let (lhs_name, lhs_inhab) = ctx.elab_match_branch(var_names, branch)?;
                    let rhs_inhab = elab_match_branches(
                        ctx, var_names, branches, end_span, elim_name,
                    )?;
                    let match_span = Span::combine(&branch.span(), end_span);
                    let motive_metavar = MetavarTag::MatchMotive {
                        match_span: match_span.clone(),
                    };

                    let scope = {
                        lhs_inhab.flat_map(|_, lhs_inhab| {
                            let lhs_ty = lhs_inhab.var_ty();

                            rhs_inhab
                            .weaken_into(&lhs_inhab.ctx())
                            .flat_map(|_, rhs_inhab| {
                                let rhs_ty = rhs_inhab.var_ty();
                                let sum_ty = lhs_ty.sum(&lhs_name, &rhs_ty);

                                let motive = {
                                    sum_ty
                                    .scope(|elim| elim.ctx().new_ty_metavar(motive_metavar))
                                    .lift_infer_scope(&elim_name)
                                };
                                motive
                                .map(|_, motive| {
                                    sum_ty
                                    .weaken_into(&motive.ctx())
                                    .scope(|elim| {
                                        elim
                                        .case(
                                            |elim| motive.bind(&elim),
                                            |lhs| lhs_inhab.bind(&lhs),
                                            |rhs| rhs_inhab.bind(&rhs),
                                        )
                                    })
                                })
                            })
                        })
                    };
                    Ok(scope)
                },
            }
        }

        let ast::ExprMatch { elim, branches } = &expr_match.inner;

        let elim_ty_metavar = MetavarTag::MatchElimTypeMatchesExpectedType {
            match_span: expr_match.span(),
            elim_span: elim.span(),
        };

        let elim_name = {
            if let ast::PrecEqual::Other(prec_add) = &**elim
            && let ast::PrecAdd::Other(prec_mul) = prec_add
            && let ast::PrecMul::Other(prec_inj) = prec_mul
            && let ast::PrecInj::Other(prec_proj) = prec_inj
            && let ast::PrecProj::Other(prec_app) = prec_proj
            && let ast::PrecApp::Other(prec_atom) = prec_app
            && let ast::PrecAtom::Var(name) = prec_atom
            {
                name.clone()
            } else {
                Ident::from_str_fake_span("match_elim")
            }
        };
        let elim_name = Name::from_ident(elim_name);

        let elim = self.elab_prec_equal(var_names, elim)?;
        let end_span = expr_match.span().end_as_span();
        let branches = elab_match_branches(
            self, var_names, &branches.inner, &end_span, &elim_name,
        )?;

        let term = {
            elim
            .flat_map(|_, elim| {
                branches
                .weaken_into(&elim.ctx())
                .flat_map(|_, branches| {
                    elim
                    .cast(&branches.var_ty(), elim_ty_metavar)
                    .map(|_, elim| {
                        branches.bind(&elim)
                    })
                })
            })
        };
        Ok(term)
    }

    fn elab_expr_struct_type(
        &self,
        var_names: &mut VarNames,
        expr_struct_type: &Spanned<ast::ExprStructType>,
    ) -> Result<InferScope<Tm>, ElabError> {
        fn elab_struct_type_tail(
            ctx: &Ctx,
            var_names: &mut VarNames,
            fields: &[Spanned<ast::TypeField>],
        ) -> Result<InferScope<Ty>, ElabError> {
            match fields.split_first() {
                None => {
                    Ok(ctx.unit_ty().pure())
                },
                Some((head_field, fields)) => {
                    let (head_name, head_ty) = ctx.elab_type_field(var_names, head_field)?;

                    head_ty
                    .try_flat_map(|_, head_ty| {
                        head_ty
                        .try_named_scope(var_names, &head_name, |var_names, head| {
                            elab_struct_type_tail(
                                &head.ctx(),
                                var_names,
                                fields,
                            )
                        })?
                        .lift_infer_scope(&head_name)
                        .map(|_, scope| scope.to_sigma(&head_name))
                        .wrap_ok()
                    })
                },
            }
        }

        let ast::ExprStructType { fields } = &expr_struct_type.inner;

        elab_struct_type_tail(self, var_names, &fields.inner)?
        .map(|_, ty| ty.to_term())
        .wrap_ok()
    }

    fn elab_expr_struct_term(
        &self,
        var_names: &mut VarNames,
        expr_struct_term: &Spanned<ast::ExprStructTerm>,
    ) -> Result<InferScope<Tm>, ElabError> {
        fn elab_struct_term_tail(
            ctx: &Ctx,
            var_names: &mut VarNames,
            fields: &[Spanned<ast::ExprStructTermField>],
            end_span: &Span,
        ) -> Result<InferScope<Tm>, ElabError> {
            match fields.split_first() {
                None => {
                    Ok(ctx.unit_term().pure())
                },
                Some((head_field, fields)) => {
                    let (head_name, head_term) = {
                        ctx.elab_expr_struct_term_field(var_names, head_field)?
                    };

                    head_term
                    .try_flat_map(|_, head_term| {
                        let tail_span = match fields.first() {
                            Some(field) => Span::combine(&field.span(), end_span),
                            None => end_span.clone(),
                        };
                        let tail_ty_metavar = MetavarTag::StructTermTailType {
                            tail_ty_span: tail_span.clone(),
                        };

                        head_term
                        .ty()
                        .pi(&head_name, |head_term| head_term.ctx().universe())
                        .new_metavar(tail_ty_metavar)
                        .try_flat_map(|_, tail_ty| {
                            let head_term = head_term.weaken_into(&tail_ty.ctx());
                            let tail_ty = head_term.ty().scope(|head_term| {
                                tail_ty.app(&head_term).to_ty()
                            });

                            elab_struct_term_tail(&tail_ty.ctx(), var_names, fields, end_span)?
                            .flat_map(|_, tail_term| {
                                let tail_term_ty_metavar = {
                                    MetavarTag::StructTermTailTypeIsExpectedType {
                                        tail_span,
                                    }
                                };

                                tail_term
                                .cast(
                                    &tail_ty.bind(&head_term),
                                    tail_term_ty_metavar,
                                )
                                .map(|_, tail_term| {
                                    let head_term = head_term.weaken_into(&tail_term.ctx());
                                    head_term.pair(&head_name, tail_ty.unbind(), &tail_term)
                                })
                            })
                            .wrap_ok()
                        })
                    })
                },
            }
        }

        let ast::ExprStructTerm { fields } = &expr_struct_term.inner;
        let end_span = fields.span.end_as_span();
        elab_struct_term_tail(self, var_names, &fields.inner, &end_span)
    }

    fn elab_expr_enum_type(
        &self,
        var_names: &mut VarNames,
        expr_enum_type: &Spanned<ast::ExprEnumType>,
    ) -> Result<InferScope<Tm>, ElabError> {
        fn elab_enum_type_variants(
            ctx: &Ctx,
            var_names: &mut VarNames,
            variants: &[Spanned<ast::TypeField>],
        ) -> Result<InferScope<Ty>, ElabError> {
            match variants.split_first() {
                None => {
                    ctx.never().pure().wrap_ok()
                },
                Some((variant, variants)) => {
                    let (lhs_name, lhs_ty) = ctx.elab_type_field(var_names, variant)?;

                    lhs_ty
                    .try_flat_map(|_, lhs_ty| {
                        elab_enum_type_variants(&lhs_ty.ctx(), var_names, variants)?
                        .map(|_, rhs_ty| {
                            lhs_ty.sum(&lhs_name, &rhs_ty)
                        })
                        .wrap_ok()
                    })
                },
            }
        }

        let ast::ExprEnumType { variants } = &expr_enum_type.inner;

        elab_enum_type_variants(self, var_names, &variants.inner)?
        .map(|_, ty| ty.to_term())
        .wrap_ok()
    }

    fn elab_var(
        &self,
        var_names: &mut VarNames,
        name: &Ident
    ) -> Result<InferScope<Tm>, ElabError> {
        let lookup_name = Name::from_ident(name.clone());
        let mut scope = match self.builtin(name.as_str()) {
            None => {
                self.never().scope(|never| {
                    never.explode(|never| never.explode(|never| never.ctx().universe()).to_ty())
                })
            },
            Some(builtin) => {
                self.unit_ty().scope(|_| builtin)
            },
        };

        for (var_name, index) in var_names.names.iter() {
            let here_ty = var_name.to_term().equals(&lookup_name.to_term()).weaken_into(self);
            let here_name = Name::from_metavar_tag(MetavarTag::VariableResolvesToThis {
                name: name.clone(),
                // TODO: track what we're resolving to.
            });
            let not_here_name = Name::from_metavar_tag(MetavarTag::VariableDoesntResolveToThis {
                name: name.clone(),
            });

            let var = self.var(*index);

            scope = {
                here_ty
                .sum(
                    &here_name,
                    &here_ty
                    .pi(&here_name, |here| here.ctx().never())
                    .sigma(&not_here_name, |not_here| {
                        scope.var_ty().weaken_into(&not_here.ctx())
                    })
                )
                .scope(|sum| {
                    sum.case(
                        |sum| {
                            sum
                            .case(
                                |sum| sum.ctx().universe(),
                                |_| var.ty().to_term(),
                                |rhs| scope.bind(&rhs.proj_tail()).ty().to_term(),
                            )
                            .to_ty()
                        },
                        |_| var.clone(),
                        |rhs| scope.bind(&rhs.proj_tail()),
                    )
                })
            };
        }

        let constraint_name = Name::from_metavar_tag(MetavarTag::ResolveVariable {
            name: name.clone(),
        });
        let mut infer_scope = InferScope::from_scope(
            &constraint_name,
            &scope,
        );
        infer_scope.minimize_constraint(u32::try_from(self.len()).unwrap());

        Ok(infer_scope)

        /*
        for (var_name, index) in var_names.names.iter().rev() {
            if let NameKind::Tag { tag } = var_name.kind()
            && let Tag::Name(ident) = tag
            && ident == *name
            {
                return Ok(self.var(*index).pure());
            }
        }
        if let Some(term) = self.builtin(name.as_str()) {
            return Ok(term.pure());
        }
    
        Err(ElabError::UnknownVar(name.clone()))
        */
    }

    fn builtin(&self, name: &str) -> Option<Tm> {
        let term = match name {
            "Nat" => self.nat().to_term(),
            "Type" => self.universe().to_term(),
            "cong" => more_tt::closed::cong(),
            "fold" => more_tt::closed::fold(),
            _ => return None,
        };
        Some(term)
    }

    fn elab_nat(&self, spanned_val: &Spanned<BigUint>) -> InferScope<Tm> {
        self.nat_constant(spanned_val.inner.clone()).pure()
    }

    fn elab_match_branch(
        &self,
        var_names: &mut VarNames,
        match_branch: &Spanned<ast::MatchBranch>,
    ) -> Result<(Name, InferScope<Scope<Tm>>), ElabError> {
        let ast::MatchBranch { variant_name, payload_name, body } = &match_branch.inner;

        let lhs_name = Name::from_ident(variant_name.clone());
        let elim_name = Name::from_ident(payload_name.clone());

        let lhs_ty_metavar = MetavarTag::MatchLhsType {
            match_branch_span: match_branch.span(),
            payload_span: payload_name.span(),
        };

        let branch = {
            self
            .new_ty_metavar(lhs_ty_metavar)
            .try_flat_map(|_, lhs_ty| {
                lhs_ty
                .try_named_scope(var_names, &lhs_name, |var_names, lhs| {
                    lhs
                    .ctx()
                    .elab_prec_equal(var_names, body)
                })?
                .lift_infer_scope(&elim_name)
                .wrap_ok()
            })?
        };
        Ok((lhs_name, branch))
    }

    fn elab_type_field(
        &self,
        var_names: &mut VarNames,
        type_field: &Spanned<ast::TypeField>,
    ) -> Result<(Name, InferScope<Ty>), ElabError> {
        let ast::TypeField { name, ty } = &type_field.inner;

        let ty_is_ty_metavar = MetavarTag::TypeFieldTypeIsType {
            type_field_span: type_field.span(),
            name_span: name.span(),
            ty_span: ty.span(),
        };
        let ty = {
            self
            .elab_prec_equal(var_names, ty)?
            .flat_map(|_, ty| ty.cast_to_ty(ty_is_ty_metavar))
        };
        let name = Name::from_ident(name.clone());
        Ok((name, ty))
    }

    fn elab_expr_struct_term_field(
        &self,
        var_names: &mut VarNames,
        expr_struct_term_field: &Spanned<ast::ExprStructTermField>,
    ) -> Result<(Name, InferScope<Tm>), ElabError> {
        let ast::ExprStructTermField { name, expr_opt } = &expr_struct_term_field.inner;

        let term = match expr_opt {
            None => self.elab_var(var_names, name)?,
            Some(expr) => self.elab_prec_equal(var_names, expr)?,
        };
        let name = Name::from_ident(name.clone());
        Ok((name, term))
    }

    fn elab_pat_prec_inj(
        &self,
        var_names: &mut VarNames,
        pat_prec_inj: &ast::PatPrecInj,
        body: &dyn Fn(&Ctx, &mut VarNames) -> Result<InferScope<Tm>, ElabError>,
    ) -> Result<InferScope<Scope<InferScope<Tm>>>, ElabError> {
        match pat_prec_inj {
            ast::PatPrecInj::Refl(pat_refl) => {
                self.elab_pat_refl(var_names, pat_refl, body)
            },
            ast::PatPrecInj::Other(pat_prec_atom) => {
                self.elab_pat_prec_atom(var_names, pat_prec_atom, body)
            },
        }
    }

    fn elab_pat_prec_atom(
        &self,
        var_names: &mut VarNames,
        pat_prec_atom: &ast::PatPrecAtom,
        body: &dyn Fn(&Ctx, &mut VarNames) -> Result<InferScope<Tm>, ElabError>,
    ) -> Result<InferScope<Scope<InferScope<Tm>>>, ElabError> {
        match pat_prec_atom {
            ast::PatPrecAtom::Var(name) => self.elab_pat_var(var_names, name, body),
            ast::PatPrecAtom::Struct(_pat_struct_term) => todo!(),
        }
    }

    fn elab_pat_refl(
        &self,
        var_names: &mut VarNames,
        pat_refl: &Spanned<ast::PatRefl>,
        body: &dyn Fn(&Ctx, &mut VarNames) -> Result<InferScope<Tm>, ElabError>,
    ) -> Result<InferScope<Scope<InferScope<Tm>>>, ElabError> {
        let ast::PatRefl { eq_pat } = &pat_refl.inner;

        let elim_name = {
            if let ast::PatPrecInj::Other(pat_prec_atom) = &**eq_pat
            && let ast::PatPrecAtom::Var(name) = pat_prec_atom
            {
                name.clone()
            } else {
                Ident::from_str_fake_span("refl_elim")
            }
        };
        let elim_name = Name::from_ident(elim_name);

        self
        .elab_pat_prec_inj(var_names, eq_pat, body)?
        .map(|_, scope| scope.lift_infer_scope(&elim_name))
        .flatten()
        .flat_map(|_, scope| {
            let eq_ty = scope.var_ty();

            let motive_metavar = MetavarTag::ReflPatMotive {
                eq_pat_span: eq_pat.span(),
            };
            let body_ty_matches_motive_metavar = MetavarTag::ReflPatBodyTypeMatchesMotive {
                eq_pat_span: eq_pat.span(),
            };
            let eq_term_0_metavar = MetavarTag::ReflPatEqTerm0 {
                eq_pat_span: eq_pat.span(),
            };
            let eq_term_1_metavar = MetavarTag::ReflPatEqTerm1 {
                eq_pat_span: eq_pat.span(),
            };

            let eq_term_0_name = Name::from_ident(Ident::from_str_fake_span("val_0"));
            let eq_term_1_name = Name::from_ident(Ident::from_str_fake_span("val_1"));
            let eq_elim_name = Name::from_ident(Ident::from_str_fake_span("val_eq"));

            eq_ty
            .pi(&eq_term_0_name, |eq_term_0| {
                eq_ty
                .weaken_into(&eq_term_0.ctx())
                .pi(&eq_term_1_name, |eq_term_1| {
                    eq_term_0
                    .equals(&eq_term_1)
                    .pi(&eq_elim_name, |elim| {
                        elim.ctx().universe()
                    })
                })
            })
            .new_metavar(motive_metavar)
            .flat_map(|_, motive| {
                scope
                .weaken_into(&motive.ctx())
                .map(|eq_term, body| {
                    body
                    .ty()
                    .to_term()
                    .equals(&motive.app(&eq_term).app(&eq_term).app(&eq_term.refl()))
                })
                .to_pi(&elim_name)
                .new_metavar(body_ty_matches_motive_metavar)
                .flat_map(|_, body_ty_matches| {
                    eq_ty
                    .weaken_into(&body_ty_matches.ctx())
                    .new_metavar(eq_term_0_metavar)
                    .flat_map(|_, eq_term_0| {
                        eq_ty
                        .weaken_into(&eq_term_0.ctx())
                        .new_metavar(eq_term_1_metavar)
                        .map(|_, eq_term_1| {
                            eq_term_0
                            .equals(&eq_term_1)
                            .scope(|elim| {
                                elim
                                .cong(
                                    |eq_term_0, eq_term_1, elim| {
                                        motive
                                        .app(&eq_term_0)
                                        .app(&eq_term_1)
                                        .app(&elim)
                                        .to_ty()
                                    },
                                    |eq_term| {
                                        body_ty_matches
                                        .app(&eq_term)
                                        .transport(&scope.bind(&eq_term))
                                    },
                                )
                                .pure()
                            })
                        })
                    })
                })
            })
        })
        .wrap_ok()
    }

    fn elab_pat_var(
        &self,
        var_names: &mut VarNames,
        name: &Ident,
        body: &dyn Fn(&Ctx, &mut VarNames) -> Result<InferScope<Tm>, ElabError>,
    ) -> Result<InferScope<Scope<InferScope<Tm>>>, ElabError> {
        let var_ty_metavar = MetavarTag::VarPatternType { var_name: name.clone() };
        let name = Name::from_ident(name.clone());

        self
        .new_ty_metavar(var_ty_metavar)
        .try_map(|_, var_ty| {
            var_ty
            .try_named_scope(var_names, &name, |var_names, var_term| {
                body(&var_term.ctx(), var_names)
            })
        })
    }
}

