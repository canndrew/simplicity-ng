use crate::priv_prelude::*;

/// A context is an ordered sequence of variable bindings. The type of each variable can depend on
/// all the preceding variables.
#[derive_where(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Ctx<S: Scheme> {
    pub(crate) raw_ctx: RawCtx<S>,
}

impl<S: Scheme> Ctx<S> {
    /// Get the root/empty context containing no variable bindings.
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

    /// Pop the inner-most variable binding from the context, returning its type. You can get the
    /// popped context (ie. minus the inner-most variable) by calling [Ty::ctx] on the returned
    /// [Ty]. Returns `None` if the context is empty.
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

    /// Execute `func` under a context with `NUM_NAMES` name variables.
    pub fn with_names<const NUM_NAMES: usize, T>(
        &self,
        func: impl FnOnce([Name<S>; NUM_NAMES]) -> T,
    ) -> T {
        let mut raw_ctx = self.raw_ctx.clone();
        let ctx_len = raw_ctx.len();
        let mut sub_ctx_len = ctx_len;
        for _ in 0..NUM_NAMES {
            raw_ctx = raw_ctx.cons(RawTy::name(sub_ctx_len));
            sub_ctx_len += 1;
        }
        let names = std::array::from_fn(|index| {
            Name {
                raw_ctx: raw_ctx.clone(),
                raw_name: RawName::stuck(RawStuck::var(sub_ctx_len, ctx_len + index)),
            }
        });
        func(names)
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

    /// Takes a bundle of things that implement `Contextual` and returns them weakened into the
    /// common context that includes variables from all their contexts. The longest context of any
    /// must be an extension of all the other contexts.
    ///
    /// # Panics
    ///
    /// If the contexts have diverged, meaning that there are two contexts where each contain
    /// variables that the other doesn't.
    pub fn into_common_ctx<Ts: BundleOfContextual<S>>(bundle_of_contextual: Ts) -> Ts::Output {
        BundleOfContextual::into_common_ctx(bundle_of_contextual)
    }

    /*
    /// Returns the free (scoped under the root context) sigma type that contains all the variables
    /// from this context.
    pub fn to_sigma(&self) -> Ty<S> {
        let raw_ctx = RawCtx::root();
        let raw_ty = self.raw_ctx.to_sigma(RawTy::unit(self.len()));
        Ty { raw_ctx, raw_ty }
    }
    */

    /// Get the [TyKind::Name] type, scoped under `self`.
    pub fn name(&self) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::name(self.len()),
        }
    }

    /// Convert `tag` into a [Name] scoped under `self`.
    pub fn tag(&self, tag: &S::Tag) -> Name<S> {
        Name {
            raw_ctx: self.raw_ctx.clone(),
            raw_name: RawName::tag(self.len(), tag.clone()),
        }
    }

    /// Get the [TyKind::Universe] type, scoped under `self`.
    pub fn universe(&self) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::universe(self.len()),
        }
    }

    /// Get the [TyKind::Nat] type, scoped under `self`.
    pub fn nat(&self) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::nat(self.len()),
        }
    }

    /// Create the zero value of type [TyKind::Nat] scoped under `self`.
    pub fn zero(&self) -> Tm<S> {
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(RawTy::nat(self.len()), RawTm::zero(self.len())),
        }
    }

    /// Create a constant value of type [TyKind::Nat] scoped under `self`.
    pub fn nat_constant(&self, val: impl Into<BigUint>) -> Tm<S> {
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(
                RawTy::nat(self.len()),
                RawTm::from_constant(self.len(), val.into()),
            ),
        }
    }

    /// Get the [TyKind::Never] type, scoped under `self`.
    pub fn never(&self) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::never(self.len()),
        }
    }

    /// Get the [TyKind::Unit] type, scoped under `self`.
    pub fn unit_ty(&self) -> Ty<S> {
        Ty {
            raw_ctx: self.raw_ctx.clone(),
            raw_ty: RawTy::unit(self.len()),
        }
    }

    /// Get the [TmKind::Unit] term, scoped under `self`.
    pub fn unit_term(&self) -> Tm<S> {
        Tm {
            raw_ctx: self.raw_ctx.clone(),
            raw_typed_term: RawTyped::from_parts(RawTy::unit(self.len()), RawTm::unit(self.len())),
        }
    }

    /// Convert val into a [`NonContextual<T>`] scoped under `self`.
    pub fn non_contextual<T>(&self, val: T) -> NonContextual<S, T> {
        NonContextual {
            raw_ctx: self.raw_ctx.clone(),
            val,
        }
    }
}

