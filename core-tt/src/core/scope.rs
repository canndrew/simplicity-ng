use crate::priv_prelude::*;

/// A `T` scoped under a variable.
#[derive_where(Clone; T::Raw: Clone)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Scope<S: Scheme, T: Contextual<S>> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) raw_scope: RawScope<S, T::Raw>,
}

impl<S: Scheme, T: Contextual<S>> PartialEq for Scope<S, T>
where
    T::Raw: PartialEq,
{
    fn eq(&self, other: &Scope<S, T>) -> bool {
        let (_, (scope_0, scope_1)) = merge_ctxs((self, other));
        scope_0 == scope_1
    }
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

    fn contains_subterm(&self, subterm: &RawTm<S>) -> bool {
        self.raw_scope.contains_subterm(subterm)
    }
}

impl<S: Scheme, T: Contextual<S>> Scope<S, T> {
    /// Whether the variable induced by `self` is referred to at all by `self`'s inner `T`.
    pub fn var_used(&self) -> bool {
        self.raw_scope.weak.inner.usages.last()
    }

    /// Whether the variable induced by `self` is used in an elimination position by `self`'s inner
    /// `T`.
    pub fn var_eliminated(&self) -> bool {
        let index = self.raw_scope.weak.inner.usages.len().strict_sub(1);
        self.raw_scope.weak.inner.eliminates_var(index)
    }

    /// Get context that `self` is scoped under (not containing `self`'s variable).
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

    /// Convert `self` to a closure which binds it's argument to `self`.
    pub fn unbind(&self) -> impl FnOnce(Tm<S>) -> T {
        |var_term| self.bind(&var_term)
    }

    /// Return the inner value of `self` with `self` variable bound to `term`.
    ///
    /// # Panics
    ///
    /// If the type of `term` does not match `self.var_ty()`.
    pub fn bind(&self, term: &Tm<S>) -> T {
        let (ctx, (raw_scope, raw_typed_term)) = merge_ctxs((self, term));
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

    /// Evaluate a function under this scope and return the result.
    ///
    /// The arguments given to `func` are a term representing `self`'s variable and `self`'s inner
    /// `T` bound to that variable.
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

    /// Map the value stored by this scope.
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

        let diff = (ctx_len + 1).strict_sub(new_ctx.len());
        assert_eq!(ctx.raw_ctx.nth_parent(diff), &new_ctx.raw_ctx);
        let inner = inner.weaken(diff);

        let raw_scope = RawScope::new(raw_ty, inner);
        Scope {
            raw_ctx: self.raw_ctx.clone(),
            raw_scope,
        }
    }

    /// Same as `map` but the given closure may return an error (eg. `None` or `Err`).
    pub fn try_map<Y>(
        &self,
        func: impl FnOnce(Tm<S>, T) -> Y,
    ) -> Y::AltOutput<Scope<S, Y::Output>>
    where
        Y: MyTry,
        Y::Output: Contextual<S>,
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
            ControlFlow::Break(err) => Y::AltOutput::from_residual(err),
            ControlFlow::Continue(inner) => {
                let scope = {
                    let (new_ctx, inner) = inner.into_raw();

                    let diff = (ctx_len + 1).strict_sub(new_ctx.len());
                    assert_eq!(ctx.raw_ctx.nth_parent(diff), &new_ctx.raw_ctx);
                    let inner = inner.weaken(diff);

                    let raw_scope = RawScope::new(raw_ty, inner);
                    Scope {
                        raw_ctx: self.raw_ctx.clone(),
                        raw_scope,
                    }
                };
                Y::AltOutput::from_output(scope)
            },
        }
    }

    /// Get the inner value stored by `self`.
    ///
    /// Use this cautiously as the returned value is still scoped under `self`'s variable, not
    /// under `self.ctx()`.
    pub fn into_inner(self) -> T {
        let Scope { raw_ctx, raw_scope } = self;
        let (inner, raw_ty) = raw_scope.into_inner();
        let ctx = Ctx { raw_ctx: raw_ctx.cons(raw_ty) };
        let inner = T::from_raw(ctx, inner);
        inner
    }

    /// Takes a value scoped under a context with at least one variable binding and returns a scope
    /// which scopes the inner-most variable of that context. This can be used in conjunction with
    /// [Scope::map_out]` to map a single scope to multiple things simultaneously.
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

    /// Get the type of `self`'s variable.
    pub fn var_ty(&self) -> Ty<S> {
        let Scope { raw_ctx, raw_scope } = self;
        let raw_ty = raw_scope.var_ty_unfiltered();
        let ctx = Ctx { raw_ctx: raw_ctx.clone() };
        Ty::from_raw(ctx, raw_ty)
    }

    /// Try to strengthen `self`'s inner value to be scoped under `self.ctx()` - ie. minus `self`'s
    /// own variable. Returns `Some` if and only if `self.var_used()` returns `false`.
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
    /// Convert a scoped `Ty` to a sigma type with the given `head_name`.
    ///
    /// The head type of the returned sigma type is the variable type of this scope. The tail type
    /// is the type stored by this scope.
    pub fn to_sigma(&self, head_name: &Name<S>) -> Ty<S> {
        let (Ctx { raw_ctx }, (scope, head_name)) = merge_ctxs((self, head_name));
        let raw_ty = RawTy::sigma(head_name, scope);
        Ty { raw_ctx, raw_ty }
    }

    /// Convert a scoped `Ty` to a pi type with the given `arg_name`.
    ///
    /// The arg type of the returned pi type is the variable type of this scope. The result type is
    /// the type stored by this scope.
    pub fn to_pi(&self, arg_name: &Name<S>) -> Ty<S> {
        let (Ctx { raw_ctx }, (raw_scope, arg_name)) = merge_ctxs((self, arg_name));
        let raw_ty = RawTy::pi(arg_name, raw_scope);
        Ty { raw_ctx, raw_ty }
    }
}

impl<S: Scheme> Scope<S, Tm<S>> {
    /// Convert a scoped term to a function (ie. term of type `Ty::Pi`).
    pub fn to_func(&self, arg_name: &Name<S>) -> Tm<S> {
        let (Ctx { raw_ctx }, (raw_scope, arg_name)) = merge_ctxs((self, arg_name));
        let (res_ty, res_term) = raw_scope.into_parts();
        let res_ty = RawTy::pi(arg_name.clone(), res_ty);
        let res_term = RawTm::func(arg_name, res_term);
        let raw_typed_term = RawTyped::from_parts(res_ty, res_term);

        Tm { raw_ctx, raw_typed_term }
    }
}

