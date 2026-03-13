use crate::priv_prelude::*;

/// Type representing a name.
///
/// Names are used for tagging parts of the AST and for creating nominal types. [TyKind::Sum]
/// types, [TyKind::Sigma] types and [TyKind::Pi] types are all parameterized by a [Name] and are
/// considered different types if the names differ. Constant names wrap a [Scheme::Tag]. There is
/// also a type of names - [TyKind::Name] - used for metaprogramming and writing name-generic code.
/// Any `Name` is either a constant (ie. a [Scheme::Tag]) or a [Stuck] computation evaluating to a
/// term of type [TyKind::Name].
#[derive_where(Clone)]
#[cfg_attr(not(feature = "pretty-formatting"), derive_where(Debug))]
pub struct Name<S: Scheme> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) raw_name: RawName<S>,
}

impl<S: Scheme> PartialEq for Name<S> {
    fn eq(&self, other: &Name<S>) -> bool {
        let (_, (name_0, name_1)) = merge_ctxs((self, other));
        name_0 == name_1
    }
}

#[derive_where(Clone, Debug)]
pub enum NameKind<S: Scheme> {
    /// A stuck computation which computes a name. For instance a variable of type [TyKind::Name].
    Stuck {
        stuck: Stuck<S>,
    },
    /// A constant name, the type of which is determined by the [Scheme].
    Tag {
        tag: S::Tag,
    },
}

impl<S: Scheme> Contextual<S> for Name<S> {
    type Raw = RawNameKind<S>;

    fn into_raw(self) -> (Ctx<S>, RawName<S>) {
        let Name { raw_ctx, raw_name } = self;
        let ctx = Ctx { raw_ctx };
        (ctx, raw_name)
    }

    fn from_raw(ctx: Ctx<S>, raw_name: RawName<S>) -> Name<S> {
        Name {
            raw_ctx: ctx.raw_ctx,
            raw_name,
        }
    }

    fn ctx(&self) -> Ctx<S> {
        let raw_ctx = self.raw_ctx.clone();
        Ctx { raw_ctx }
    }

    fn eliminates_var(&self, index: usize) -> bool {
        self.raw_name.eliminates_var(index)
    }

    fn contains_subterm(&self, subterm: &RawTm<S>) -> bool {
        self.raw_name.contains_subterm(subterm)
    }
}

impl<S: Scheme> Name<S> {
    /// Get the [NameKind] representation of `self` in order to pattern-match on it.
    pub fn kind(&self) -> NameKind<S> {
        let Name { raw_ctx, raw_name } = self;
        match &raw_name.weak {
            RawNameKind::Stuck { stuck } => {
                let raw_ty = RawTy::name(raw_name.usages.len());
                let raw_stuck = Weaken { usages: raw_name.usages.clone(), weak: stuck.clone() };
                let raw_typed_stuck = RawTyped::from_parts(raw_ty, raw_stuck);
                let stuck = Stuck {
                    raw_ctx: raw_ctx.clone(),
                    raw_typed_stuck,
                };
                NameKind::Stuck { stuck }
            },
            RawNameKind::Tag { tag } => {
                NameKind::Tag { tag: tag.clone() }
            },
        }
    }

    /// Convert `self` to a `Tm` of type `TyKind::Name`.
    pub fn to_term(&self) -> Tm<S> {
        let Name { raw_ctx, raw_name } = self;
        let raw_ty = RawTy::name(raw_name.usages.len());
        let raw_term = match &raw_name.weak {
            RawNameKind::Stuck { stuck } => {
                let stuck = Weaken { usages: raw_name.usages.clone(), weak: stuck.clone() };
                RawTm::stuck(stuck)
            },
            RawNameKind::Tag { tag } => {
                RawTm::tag(raw_name.usages.len(), tag.clone())
            },
        };
        let raw_typed_term = RawTyped::from_parts(raw_ty, raw_term);
        Tm { raw_ctx: raw_ctx.clone(), raw_typed_term }
    }
}

