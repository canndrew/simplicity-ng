use crate::priv_prelude::*;

/// A context is an ordered sequence of variable bindings. Each type of each variable can depend on
/// all the preceding variables.
#[derive_where(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Ctx<S: Scheme> {
    pub(crate) raw_ctx: RawCtx<S>,
}

impl<S: Scheme> Ctx<S> {
    /// Get the root context which contains no variable bindings.
    pub fn root() -> Ctx<S> {
        Ctx {
            raw_ctx: RawCtx::root(),
        }
    }

    /// Check whether this is the root context.
    pub fn is_root(&self) -> bool {
        self.len() == 0
    }

    /// Get the number of variable bindings in the context.
    pub fn len(&self) -> usize {
        self.raw_ctx.len()
    }

    /// Try to pop the inner-most variable binding from the context, returning its type.
    /// You can get the popped context by calling the `ctx` method on the returned type.
    pub fn pop(&self) -> Option<Ty<S>> {
        let cons = self.raw_ctx.cons_opt.as_ref()?;
        let RawCtxCons { parent, var_ty } = &**cons;
        let var_ty = Ty { raw_ctx: parent.clone(), raw_ty: var_ty.clone() };
        Some(var_ty)
    }

    /// Push a variable binding of type `var_ty` to the context, returning the extended context.
    pub fn cons(&self, var_ty: &Ty<S>) -> Ctx<S> {
        let ty_ctx_len = var_ty.raw_ty.usages.len();
        let diff = self.len().strict_sub(ty_ctx_len);
        assert_eq!(self.raw_ctx.nth_parent(diff), &var_ty.raw_ctx);
        let raw_ty = var_ty.raw_ty.clone_weaken(diff);
        let raw_ctx = self.raw_ctx.cons(raw_ty);
        Ctx { raw_ctx }
    }

    /// Pushes a variable binding of type `ty` onto the context and calls `func`, passing it a term
    /// that refers to this variable.
    pub fn with_cons<T>(&self, ty: &Ty<S>, func: impl FnOnce(Tm<S>) -> T) -> T {
        let ty_ctx_len = ty.raw_ty.usages.len();
        let diff = self.len().strict_sub(ty_ctx_len);
        assert_eq!(self.raw_ctx.nth_parent(diff), &ty.raw_ctx);
        let raw_ty = ty.raw_ty.clone_weaken(diff);
        let raw_typed_term = RawTyped::from_parts(
            raw_ty.clone_weaken(1),
            RawTm::var(self.len() + 1, self.len(), &raw_ty),
        );
        let var_term = Tm {
            raw_ctx: self.raw_ctx.cons(raw_ty),
            raw_typed_term,
        };
        func(var_term)
    }

    fn get_raw_ty_weakened(&self, index: usize) -> RawTy<S> {
        let de_brujin = self.len().strict_sub(index + 1);
        let var_ty = self.get_raw_ty(index);
        var_ty.clone_weaken(de_brujin + 1)
    }

    pub(crate) fn get_raw_ty(&self, index: usize) -> &RawTy<S> {
        self.raw_ctx.get_raw_ty(self.len(), index)
    }

    /// Get the type of the variable binding at `index`.
    ///
    /// # Panics
    ///
    /// If `index` is out of range.
    pub fn get_ty(&self, index: usize) -> Ty<S> {
        let raw_ty = self.get_raw_ty_weakened(index);
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty,
        }
    }

    /// Get a term that refers to the variable at `index`.
    ///
    /// # Panics
    ///
    /// if `index` is out of range.
    pub fn var(&self, index: usize) -> Tm<S> {
        let raw_ty = self.get_raw_ty(index);
        let raw_term = RawTm::var(self.len(), index, raw_ty);
        let raw_ty = raw_ty.clone_weaken(self.len().strict_sub(index + 1) + 1);
        let raw_typed_term = RawTyped::from_parts(raw_ty, raw_term);
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term,
        }
    }

    fn merge_ctx_2<T0: Contextual<S>, T1: Contextual<S>>(
        thing_0: &T0,
        thing_1: &T1,
    ) -> Ctx<S> {
        let raw_ctx_0 = &thing_0.ctx().raw_ctx;
        let raw_ctx_1 = &thing_1.ctx().raw_ctx;
        let ctx_len_0 = raw_ctx_0.len();
        let ctx_len_1 = raw_ctx_1.len();

        let (raw_ctx, cmp_ctx_0, cmp_ctx_1) = match ctx_len_0.cmp(&ctx_len_1) {
            cmp::Ordering::Less => {
                let diff = ctx_len_1 - ctx_len_0;
                (raw_ctx_1, raw_ctx_0, raw_ctx_1.nth_parent(diff))
            },
            cmp::Ordering::Equal => (raw_ctx_0, raw_ctx_0, raw_ctx_1),
            cmp::Ordering::Greater => {
                let diff = ctx_len_0 - ctx_len_1;
                (raw_ctx_0, raw_ctx_0.nth_parent(diff), raw_ctx_1)
            },
        };
        assert_eq!(cmp_ctx_0, cmp_ctx_1);
        let raw_ctx = raw_ctx.clone();
        Ctx { raw_ctx }
    }

    pub(crate) fn merge_into_ctx_2<T0: Contextual<S> + Clone, T1: Contextual<S> + Clone>(
        thing_0: &T0,
        thing_1: &T1,
    ) -> (Ctx<S>, Weaken<T0::Raw>, Weaken<T1::Raw>) {
        let ctx = Ctx::merge_ctx_2(thing_0, thing_1);

        let (ctx_0, mut thing_0) = thing_0.clone().into_raw();
        thing_0.weaken(ctx.len().strict_sub(ctx_0.len()));
        let (ctx_1, mut thing_1) = thing_1.clone().into_raw();
        thing_1.weaken(ctx.len().strict_sub(ctx_1.len()));

        (ctx, thing_0, thing_1)
    }

    /// Takes two things that implement `Contextual` and returns them weakened into the
    /// common context that includes variables from both their contexts. The context of one thing
    /// (either of them) must be an extension of the context of the other.
    ///
    /// # Panics
    ///
    /// If the contexts have diverged, each containing variables that the other doesn't.
    ///
    pub fn into_common_ctx<T0: Contextual<S> + Clone, T1: Contextual<S> + Clone>(
        thing_0: &T0,
        thing_1: &T1,
    ) -> (T0, T1) {
        let (ctx, thing_0, thing_1) = Ctx::merge_into_ctx_2(thing_0, thing_1);
        let thing_0 = T0::from_raw(ctx.clone(), thing_0);
        let thing_1 = T1::from_raw(ctx, thing_1);
        (thing_0, thing_1)
    }

    /// Returns the free (scoped under the root context) sigma type that contains all the variables
    /// from this context.
    pub fn to_sigma(&self) -> Ty<S> {
        let raw_ctx = RawCtx::root();
        let raw_ty = self.raw_ctx.to_sigma(RawTy::unit(self.len()));
        Ty { raw_ctx, raw_ty }
    }

    pub fn user_ty(&self, user_ty: &S::UserTy) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::user(self.len(), user_ty.clone()),
        }
    }

    pub fn user_term(&self, user_term: &S::UserTm) -> Tm<S> {
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(
                RawTy::user(self.len(), S::user_ty_of(user_term)),
                RawTm::user(self.len(), user_term.clone()),
            ),
        }
    }

    pub fn universe(&self) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::universe(self.len()),
        }
    }

    pub fn nat(&self) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::nat(self.len()),
        }
    }

    pub fn zero(&self) -> Tm<S> {
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(RawTy::nat(self.len()), RawTm::zero(self.len())),
        }
    }

    pub fn nat_constant(&self, val: impl Into<BigUint>) -> Tm<S> {
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(
                RawTy::nat(self.len()),
                RawTm::from_constant(self.len(), val.into()),
            ),
        }
    }

    pub fn never(&self) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::never(self.len()),
        }
    }

    pub fn unit_ty(&self) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::unit(self.len()),
        }
    }

    pub fn unit_term(&self) -> Tm<S> {
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(RawTy::unit(self.len()), RawTm::unit(self.len())),
        }
    }

    /*
    pub fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> Ctx<V> {
        let mut map_user_ty = map_user_ty;
        let mut map_user_term = map_user_term;

        let Ctx { raw_ctx } = self;
        let raw_ctx = raw_ctx.map_scheme(&mut map_user_ty, &mut map_user_term);
        Ctx { raw_ctx }
    }
    */
}

/*
impl<S: Scheme> fmt::Debug for Ctx<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Ctx { raw_ctx, ctx_len } = self;
        let actual_len = pprint::pprint_raw_ctx(f, raw_ctx)?;
        debug_assert_eq!(actual_len, *ctx_len);
        Ok(())
    }
}
*/

