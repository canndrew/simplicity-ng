use crate::priv_prelude::*;

#[derive_where(Clone, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct InferScope<S: Scheme, T: Contextual<S> + Clone + fmt::Debug> {
    pub(crate) scope: Scope<S, T>,
}

impl<S: Scheme, T: Contextual<S>> InferScope<S, T>
where
    S: Scheme,
    T: Contextual<S>,
    T: Clone + fmt::Debug,
{
    pub fn map_out<U>(&self, func: impl FnOnce(Tm<S>, T) -> U) -> U {
        self.scope.map_out(func)
    }

    pub fn map<U>(&self, func: impl FnOnce(Tm<S>, T) -> U) -> InferScope<S, U>
    where
        U: Contextual<S>,
        U: Clone + fmt::Debug,
    {
        InferScope {
            scope: self.scope.map(func),
        }
    }

    pub fn flat_map<U>(
        &self,
        func: impl FnOnce(Tm<S>, T) -> InferScope<S, U>,
    ) -> InferScope<S, U>
    where
        U: Contextual<S>,
        U: Clone + fmt::Debug,
    {
        self.map(func).flatten()
    }
}

impl<S: Scheme> InferScope<S, Tm<S>> {
    pub fn minimize_constraint(&self, recursion_depth: u32) -> InferScope<S, Tm<S>> {
        let reduction = self.scope.reduce_constraint(recursion_depth);
        let reduced = reduction.reduced_scope();
        InferScope { scope: reduced }
    }

    pub fn try_solve(&self, recursion_depth: u32) -> Result<Tm<S>, InferScope<S, Tm<S>>> {
        let InferScope { scope } = self.minimize_constraint(recursion_depth);

        if let TyKind::Unit = scope.var_ty().kind() {
            return Ok(scope.bind(&self.ctx().unit_term()));
        }

        Err(InferScope { scope })
    }
}

impl<S, T> InferScope<S, InferScope<S, T>>
where
    S: Scheme,
    T: Contextual<S>,
    T: Clone + fmt::Debug,
{
    fn flatten(&self) -> InferScope<S, T> {
        InferScope {
            scope: {
                self
                .scope
                .map(|_, inner| inner.scope.var_ty())
                .to_sigma()
                .scope(|pair| {
                    self.scope.bind(&pair.proj_head()).scope.bind(&pair.proj_tail())
                })
            },
        }
    }
}

impl<S> InferScope<S, Ty<S>>
where
    S: Scheme,
{
    pub fn scope<T>(
        &self,
        func: impl FnOnce(Tm<S>) -> InferScope<S, T>,
    ) -> InferScope<S, Scope<S, T>>
    where
        T: Contextual<S>,
        T: Clone + fmt::Debug,
    {
        self
        .map(|_, ty| {
            ty
            .scope(|term| func(term))
            .lift_infer_scope()
        })
        .flatten()
    }

    pub fn sum(
        &self,
        rhs_ty: &InferScope<S, Ty<S>>,
    ) -> InferScope<S, Ty<S>> {
        self
        .flat_map(|_, lhs_ty| {
            rhs_ty
            .weaken_into(&lhs_ty.ctx())
            .map(|_, rhs_ty| {
                Ty::sum(&lhs_ty, &rhs_ty)
            })
        })
    }
}

impl<S> InferScope<S, Tm<S>>
where
    S: Scheme,
{
    pub fn ty(&self) -> InferScope<S, Ty<S>> {
        self.map(|_, term| term.ty())
    }

    pub fn cast(&self, ty: &InferScope<S, Ty<S>>) -> InferScope<S, Tm<S>> {
        self
        .flat_map(|_, term| {
            ty
            .weaken_into(&term.ctx())
            .flat_map(|_, ty| {
                term
                .ty()
                .to_term()
                .equals(&ty.to_term())
                .hole()
                .map(|_, eq| {
                    eq
                    .cong(
                        |ty_0, ty_1, _| ty_0.to_ty().pi(|_| ty_1.to_ty()),
                        |ty| ty.to_ty().func(|term| term),
                    )
                    .app(&term)
                })
            })
        })
    }
    
    pub fn succs(&self, count: impl Into<BigUint>) -> InferScope<S, Tm<S>> {
        self
        .map(|_, term| term.succs(count))
    }

    pub fn equals(
        &self,
        eq_term_1: &InferScope<S, Tm<S>>,
    ) -> InferScope<S, Ty<S>> {
        self
        .flat_map(|_, eq_term_0| {
            eq_term_1
            .map(|_, eq_term_1| {
                eq_term_0.equals(&eq_term_1)
            })
        })
    }

    pub fn refl(&self) -> InferScope<S, Tm<S>> {
        self.map(|_, term| term.refl())
    }

    pub fn inj_lhs(
        &self,
        rhs_ty: &InferScope<S, Ty<S>>,
    ) -> InferScope<S, Tm<S>> {
        self
        .flat_map(|_, lhs_term| {
            rhs_ty
            .weaken_into(&lhs_term.ctx())
            .map(|_, rhs_ty| {
                lhs_term.inj_lhs(&rhs_ty)
            })
        })
    }

    pub fn inj_rhs(
        &self,
        lhs_ty: &InferScope<S, Ty<S>>,
    ) -> InferScope<S, Tm<S>> {
        self
        .flat_map(|_, rhs_term| {
            lhs_ty
            .weaken_into(&rhs_term.ctx())
            .map(|_, lhs_ty| {
                rhs_term.inj_rhs(&lhs_ty)
            })
        })
    }

    pub fn pair(
        &self,
        tail_ty: impl FnOnce(Tm<S>) -> InferScope<S, Ty<S>>,
        tail_term: &InferScope<S, Tm<S>>,
    ) -> InferScope<S, Tm<S>> {
        let tail_ty = self.ty().scope(tail_ty);

        self
        .flat_map(|_, head_term| {
            tail_ty
            .weaken_into(&head_term.ctx())
            .flat_map(|_, tail_ty| {
                tail_term
                .weaken_into(&tail_ty.ctx())
                .map(|_, tail_term| {
                    head_term
                    .weaken_into(&tail_term.ctx())
                    .pair(
                        |head_term| tail_ty.bind(&head_term),
                        &tail_term,
                    )
                })
            })
        })
    }

    pub fn for_loop(
        &self,
        motive: impl FnOnce(Tm<S>) -> InferScope<S, Ty<S>>,
        zero_inhab: &InferScope<S, Tm<S>>,
        succ_inhab: impl FnOnce(Tm<S>, Tm<S>) -> InferScope<S, Tm<S>>,
    ) -> InferScope<S, Tm<S>> {
        let motive = self.ctx().nat().scope(motive).lift_infer_scope();
        let succ_inhab = {
            self
            .ctx()
            .nat()
            .scope(|elim| motive.flat_map(|_, motive| {
                motive
                .bind(&elim)
                .scope(|state| {
                    let elim = elim.weaken_into(&state.ctx());
                    succ_inhab(elim, state)
                })
                .lift_infer_scope()
            }))
            .lift_infer_scope()
        };
        
        self
        .flat_map(|_, elim| {
            motive
            .weaken_into(&elim.ctx())
            .flat_map(|_, motive| {
                zero_inhab
                .weaken_into(&motive.ctx())
                .flat_map(|_, zero_inhab| {
                    succ_inhab
                    .weaken_into(&zero_inhab.ctx())
                    .map(|_, succ_inhab| {
                        elim
                        .weaken_into(&succ_inhab.ctx())
                        .for_loop(
                            |elim| motive.bind(&elim),
                            &zero_inhab,
                            |elim, state| succ_inhab.bind(&elim).bind(&state),
                        )
                    })
                })
            })
        })
    }

    pub fn cong(
        &self,
        motive: impl FnOnce(Tm<S>, Tm<S>, Tm<S>) -> InferScope<S, Ty<S>>,
        inhab: impl FnOnce(Tm<S>) -> InferScope<S, Tm<S>>,
    ) -> InferScope<S, Tm<S>> {
        self
        .flat_map(|_, elim| {
            let TyKind::Equal { eq_term_0, .. } = elim.ty().kind() else {
                panic!();
            };
            let eq_ty = eq_term_0.ty();
            let motive = {
                eq_ty
                .scope(|eq_term_0| {
                    eq_ty
                    .weaken_into(&eq_term_0.ctx())
                    .scope(|eq_term_1| {
                        eq_term_0
                        .equals(&eq_term_1)
                        .scope(|elim| {
                            let eq_term_0 = eq_term_0.weaken_into(&elim.ctx());
                            let eq_term_1 = eq_term_1.weaken_into(&elim.ctx());
                            motive(eq_term_0, eq_term_1, elim)
                        })
                        .lift_infer_scope()
                    })
                    .lift_infer_scope()
                })
                .lift_infer_scope()
            };
            let inhab = eq_ty.scope(inhab).lift_infer_scope();

            motive
            .flat_map(|_, motive| {
                inhab
                .map(|_, inhab| {
                    elim
                    .weaken_into(&inhab.ctx())
                    .cong(
                        |eq_term_0, eq_term_1, elim| {
                            motive.bind(&eq_term_0).bind(&eq_term_1).bind(&elim)
                        },
                        |eq_term| inhab.bind(&eq_term),
                    )
                })
            })
        })
    }
}

impl<S, T> InferScope<S, Scope<S, T>>
where
    S: Scheme,
    T: Contextual<S>,
    T: Clone + fmt::Debug,
{
    pub fn bind(&self, term: &InferScope<S, Tm<S>>) -> InferScope<S, T> {
        let term = term.cast(&self.map(|_, scope| scope.var_ty()));

        self
        .flat_map(|_, scope| {
            term
            .weaken_into(&scope.ctx())
            .map(|_, term| {
                scope.bind(&term)
            })
        })
    }
}

impl<S> InferScope<S, Scope<S, InferScope<S, Ty<S>>>>
where
    S: Scheme,
{
    pub fn to_sigma(&self) -> InferScope<S, Ty<S>> {
        self
        .flat_map(|_, inner| {
            inner
            .lift_infer_scope()
            .map(|_, inner| {
                inner.to_sigma()
            })
        })
    }

    pub fn to_pi(&self) -> InferScope<S, Ty<S>> {
        self
        .flat_map(|_, inner| {
            inner
            .lift_infer_scope()
            .map(|_, inner| {
                inner.to_pi()
            })
        })
    }
}

impl<S> InferScope<S, Scope<S, InferScope<S, Tm<S>>>>
where
    S: Scheme,
{
    pub fn to_pi(&self) -> InferScope<S, Tm<S>> {
        self
        .flat_map(|_, inner| {
            inner
            .lift_infer_scope()
            .map(|_, inner| {
                inner.to_func()
            })
        })
    }
}

#[extension(pub trait ScopeInferExt)]
impl<S, T> Scope<S, InferScope<S, T>>
where
    S: Scheme,
    T: Contextual<S>,
    T: Clone + fmt::Debug,
{
    fn lift_infer_scope(&self) -> InferScope<S, Scope<S, T>> {
        let infer_ty = self.map(|_, inner| inner.scope.var_ty()).to_pi();
        InferScope {
            scope: infer_ty.scope(|infer_val| {
                self.map(|var_term, inner| {
                    inner.scope.bind(&infer_val.app(&var_term))
                })
            }),
        }
    }
}

#[extension(pub trait CtxInferExt)]
impl<S> Ctx<S>
where
    S: Scheme,
{
    fn ty_hole(&self) -> InferScope<S, Ty<S>> {
        InferScope {
            scope: self.universe().scope(|ty| ty.to_ty()),
        }
    }
}

#[extension(pub trait TyInferExt)]
impl<S> Ty<S>
where
    S: Scheme,
{
    fn hole(&self) -> InferScope<S, Tm<S>> {
        InferScope {
            scope: self.scope(|term| term),
        }
    }
}

#[extension(pub trait ContextualInferExt)]
impl<S, T> T
where
    S: Scheme,
    T: Contextual<S>,
    T: Clone + fmt::Debug,
{
    fn pure(&self) -> InferScope<S, T> {
        InferScope {
            scope: self.ctx().unit_ty().scope(|_| self.clone())
        }
    }
}

