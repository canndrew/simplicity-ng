use crate::priv_prelude::*;

#[derive_where(Clone, PartialEq)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Scope<S: Scheme, T: Contextual<S>> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) raw_scope: RawScope<S, T::Raw>,
}

impl<S: Scheme, T: Contextual<S>> Contextual<S> for Scope<S, T>
where
    T::Raw: Clone,
{
    type Raw = RawScopeKind<S, T::Raw>;

    fn into_raw(self) -> (Ctx<S>, RawScope<S, T::Raw>) {
        let Scope { raw_ctx, raw_scope } = self;
        let ctx = Ctx { raw_ctx };
        (ctx, raw_scope)
    }

    fn from_raw(ctx: Ctx<S>, raw: RawScope<S, T::Raw>) -> Scope<S, T> {
        Scope {
            raw_ctx: ctx.raw_ctx,
            raw_scope: raw,
        }
    }

    fn ctx(&self) -> Ctx<S> {
        let raw_ctx = self.raw_ctx.clone();
        Ctx { raw_ctx }
    }

    fn eliminates_var(&self, index: usize) -> bool {
        self.raw_scope.eliminates_var(index)
    }
}

impl<S: Scheme, T: Contextual<S>> Scope<S, T> {
    pub fn var_used(&self) -> bool {
        self.raw_scope.weak.inner.usages.last()
    }

    pub fn var_eliminated(&self) -> bool {
        let index = self.raw_scope.weak.inner.usages.len().strict_sub(1);
        self.raw_scope.weak.inner.eliminates_var(index)
    }

    pub fn ctx(&self) -> Ctx<S> {
        Ctx {
            raw_ctx: self.raw_ctx.clone(),
        }
    }

    pub fn usages(&self) -> &Usages {
        &self.raw_scope.usages
    }

    pub fn transitive_usages(&self) -> Usages {
        let mut usages = self.raw_scope.usages.clone();
        self.raw_ctx.fill_transitive_usages(&mut usages);
        usages
    }

    pub fn unbind(&self) -> impl FnOnce(Tm<S>) -> T {
        |var_term| self.bind(&var_term)
    }

    pub fn bind(&self, term: &Tm<S>) -> T {
        let (ctx, raw_scope, raw_typed_term) = Ctx::merge_into_ctx_2(self, term);
        let (raw_ty, raw_term) = raw_typed_term.into_parts();

        let expected_raw_ty = raw_scope.var_ty_unfiltered();
        if raw_ty != expected_raw_ty {
            let actual_ty = Ty {
                raw_ctx: ctx.raw_ctx.clone(),
                raw_ty: raw_ty,
            };
            let expected_ty = Ty {
                raw_ctx: ctx.raw_ctx.clone(),
                raw_ty: expected_raw_ty,
            };
            panic!(
                "\
                bind() type mismatch:\n\
                expected: {:?}\n\
                got: {:?}\n\
                ",
                expected_ty,
                actual_ty,
            );
        }

        let inner = raw_scope.bind(&raw_term);
        T::from_raw(ctx, inner)
    }

    pub fn map_out<U>(&self, func: impl FnOnce(Tm<S>, T) -> U) -> U {
        let ctx_len = self.raw_scope.usages.len();

        let (inner, raw_ty) = self.raw_scope.clone().into_inner();
        let raw_ctx = self.raw_ctx.cons(raw_ty.clone());
        let var_term = Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(
                raw_ty.clone_weaken(1),
                RawTm::var(ctx_len + 1, ctx_len, &raw_ty),
            ),
        };
        let ctx = Ctx { raw_ctx }; 
        let inner = T::from_raw(ctx, inner);
        func(var_term, inner)
    }

    pub fn map<U: Contextual<S>>(&self, func: impl FnOnce(Tm<S>, T) -> U) -> Scope<S, U> {
        let ctx_len = self.raw_scope.usages.len();

        let (inner, raw_ty) = self.raw_scope.clone().into_inner();
        let raw_ctx = self.raw_ctx.cons(raw_ty.clone());
        let var_term = Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(
                raw_ty.clone_weaken(1),
                RawTm::var(ctx_len + 1, ctx_len, &raw_ty),
            ),
        };
        let ctx = Ctx { raw_ctx };
        let inner = T::from_raw(ctx.clone(), inner);
        let inner = func(var_term, inner);
        let (new_ctx, inner) = inner.into_raw();
        assert_eq!(new_ctx, ctx);
        let raw_scope = RawScope::new(raw_ty, inner);
        Scope {
            raw_ctx: self.raw_ctx.clone(),
            raw_scope,
        }
    }

    pub fn try_map<Y>(
        &self,
        func: impl FnOnce(Tm<S>, T) -> Y,
    ) -> <Y::Residual as Residual<Scope<S, Y::Output>>>::TryType
    where
        Y: Try,
        Y::Output: Contextual<S>,
        Y::Residual: Residual<Scope<S, Y::Output>>,
    {
        let ctx_len = self.raw_scope.usages.len();
        let (inner, raw_ty) = self.raw_scope.clone().into_inner();
        let raw_ctx = self.raw_ctx.cons(raw_ty.clone());
        let var_term = Tm {
            raw_ctx: raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(
                raw_ty.clone_weaken(1),
                RawTm::var(ctx_len + 1, ctx_len, &raw_ty),
            ),
        };

        let ctx = Ctx { raw_ctx };
        let inner = T::from_raw(ctx.clone(), inner);
        let inner_res = func(var_term, inner);
        match inner_res.branch() {
            ControlFlow::Break(err) => {
                <<Y::Residual as Residual<Scope<S, Y::Output>>>::TryType as FromResidual>::from_residual(err)
            },
            ControlFlow::Continue(inner) => {
                let scope = {
                    let (new_ctx, inner) = inner.into_raw();
                    assert_eq!(new_ctx, ctx);
                    let raw_scope = RawScope::new(raw_ty, inner);
                    Scope {
                        raw_ctx: self.raw_ctx.clone(),
                        raw_scope,
                    }
                };
                <<Y::Residual as Residual<Scope<S, Y::Output>>>::TryType as Try>::from_output(scope)
            },
        }
    }

    pub fn into_inner(self) -> T {
        let Scope { raw_ctx, raw_scope } = self;
        let (inner, raw_ty) = raw_scope.into_inner();
        let ctx = Ctx { raw_ctx: raw_ctx.cons(raw_ty) };
        let inner = T::from_raw(ctx, inner);
        inner
    }

    pub fn new(thing: T) -> Scope<S, T> {
        let (Ctx { raw_ctx }, raw) = thing.into_raw();

        let cons = raw_ctx.cons_opt.as_ref().unwrap();
        let raw_ctx = cons.parent.clone();
        let var_ty = cons.var_ty.clone();

        let raw_scope = RawScope::new(var_ty, raw);
        Scope {
            raw_ctx,
            raw_scope,
        }
    }

    pub fn var_ty(&self) -> Ty<S> {
        let Scope { raw_ctx, raw_scope } = self;
        let raw_ty = raw_scope.var_ty_unfiltered();
        let ctx = Ctx { raw_ctx: raw_ctx.clone() };
        Ty::from_raw(ctx, raw_ty)
    }

    pub fn try_strengthen(&self) -> Option<T> {
        if self.raw_scope.var_used() {
            None
        } else {
            let Scope { raw_ctx, raw_scope } = self;
            let raw_inner = raw_scope.inner_unfiltered_strengthen();
            let ctx = Ctx { raw_ctx: raw_ctx.clone() };
            Some(T::from_raw(ctx, raw_inner))
        }
    }
}

impl<S: Scheme> Scope<S, Ty<S>> {
    pub fn to_sigma(&self) -> Ty<S> {
        let Scope { raw_ctx, raw_scope } = self;
        let raw_ctx = raw_ctx.clone();
        let raw_ty = RawTy::sigma(raw_scope.clone());
        Ty { raw_ctx, raw_ty }
    }

    pub fn to_pi(&self) -> Ty<S> {
        let Scope { raw_ctx, raw_scope } = self;
        let raw_ctx = raw_ctx.clone();
        let raw_ty = RawTy::pi(raw_scope.clone());
        Ty { raw_ctx, raw_ty }
    }
}

impl<S: Scheme> Scope<S, Tm<S>> {
    pub fn to_func(&self) -> Tm<S> {
        let Scope { raw_ctx, raw_scope } = self;
        let raw_ctx = raw_ctx.clone();
        let (res_ty, res_term) = raw_scope.clone().into_parts();
        let res_ty = RawTy::pi(res_ty);
        let res_term = RawTm::func(res_term);
        let raw_typed_term = RawTyped::from_parts(res_ty, res_term);

        Tm { raw_ctx, raw_typed_term }
    }
}

