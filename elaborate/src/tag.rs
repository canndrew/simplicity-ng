use crate::priv_prelude::*;

pub type Ctx = core_tt::Ctx<TagScheme>;
pub type Ty = core_tt::Ty<TagScheme>;
pub type Tm = core_tt::Tm<TagScheme>;
pub type Stuck = core_tt::Stuck<TagScheme>;
pub type Scope<T> = core_tt::Scope<TagScheme, T>;
pub type Name = core_tt::Name<TagScheme>;
pub type TyKind = core_tt::TyKind<TagScheme>;
pub type TmKind = core_tt::TmKind<TagScheme>;
pub type StuckKind = core_tt::StuckKind<TagScheme>;
pub type NameKind = core_tt::NameKind<TagScheme>;
pub type Iso = more_tt::Iso<TagScheme>;

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Tag {
    Name(Ident),
    Metavar(Arc<MetavarTag>),
}

impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Tag::Name(name) => write!(f, "{:?}", name.as_str()),
            Tag::Metavar(metavar_tag) => write!(f, "{:?}", metavar_tag),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum MetavarTag {
    Pure,
    DependentConstraintName,
    EqualsLeftTypeMatchesRightType {
        equals_span: Span,
        eq_term_0_span: Span,
        eq_term_1_span: Span,
    },
    AddArgumentTypeIsNat {
        argument_span: Span,
    },
    MulArgumentTypeIsNat {
        argument_span: Span,
    },
    InjectionRhsType {
        lhs_name: Ident,
        inj_span: Span,
        payload_span: Span,
    },
    Injections {
        lhs_name: Ident,
        inj_span: Span,
        payload_span: Span,
    },
    TypeFieldTypeIsType {
        type_field_span: Span,
        name_span: Span,
        ty_span: Span,
    },
    StructTermTailType {
        tail_ty_span: Span,
    },
    StructTermTailTypeIsExpectedType {
        tail_span: Span,
    },
    VarPatternType {
        var_name: Ident,
    },
    EmptyMatchMotive {
        match_end_span: Span,
    },
    MatchMotive {
        match_span: Span,
    },
    MatchElimTypeMatchesExpectedType {
        match_span: Span,
        elim_span: Span,
    },
    MatchLhsType {
        match_branch_span: Span,
        payload_span: Span,
    },
    AppElimTypeIsFunc {
        elim_span: Span,
        arg_span: Span,
    },
    AppResType {
        elim_span: Span,
        arg_span: Span,
    },
    FuncTermElidedArgType {
        arg_name: Ident,
    },
    FuncArgTyIsTy {
        arg_ty_span: Span,
    },
    FuncResTyIsTy {
        res_ty_span: Span,
    },
    ProjectionFullType {
        base_span: Span,
        field_name: Ident,
    },
    ProjectionBaseTypeIsSigma {
        base_span: Span,
        field_name: Ident,
    },
    ProjectionHeadType {
        base_span: Span,
        field_name: Ident,
    },
    ProjectionTailType {
        base_span: Span,
        field_name: Ident,
    },
    ProjectionCoercion {
        base_span: Span,
        field_name: Ident,
    },
    LetTypeIsType {
        let_ty_span: Span,
    },
    LetTermTypeIsExpectedType {
        let_ty_span: Span,
        var_term_span: Span,
    },
    LetTermTypeMatchesPatType {
        var_term_span: Span,
        var_ty_span_opt: Option<Span>,
        pat_span: Span,
    },
    ReflPatMotive {
        eq_pat_span: Span,
    },
    ReflPatBodyTypeMatchesMotive {
        eq_pat_span: Span,
    },
    ReflPatEqTerm0 {
        eq_pat_span: Span,
    },
    ReflPatEqTerm1 {
        eq_pat_span: Span,
    },
    
    VariableResolvesToThis {
        name: Ident,
    },
    VariableDoesntResolveToThis {
        name: Ident,
    },
    ResolveVariable {
        name: Ident,
    },
}

pub enum TagScheme {}

impl core_tt::Scheme for TagScheme {
    type Tag = Tag;

    fn interner() -> &'static Interner<TagScheme> {
        lazy_static! {
            static ref TAG_INTERNER: Interner<TagScheme> = Interner::new();
        }
        &*TAG_INTERNER
    }
}

impl more_tt::Scheme for TagScheme {
    fn tag_from_str(s: &str) -> Tag {
        Tag::Name(Ident::from_str_fake_span(s))
    }

    fn try_tag_as_string(tag: &Tag) -> Option<String> {
        match tag {
            Tag::Name(ident) => Some(ident.as_str().to_string()),
            Tag::Metavar(_) => None,
        }
    }
}

#[extension(pub trait TyTagExt)]
impl Ty {
    fn new_metavar(&self, metavar_tag: MetavarTag) -> InferScope<Tm> {
        let constraint_name = self.ctx().tag(&Tag::Metavar(Arc::new(metavar_tag)));
        InferScope::from_scope(&constraint_name, &self.scope(|term| term))
    }

    fn named_with_cons<T>(
        &self,
        var_names: &mut VarNames,
        name: &Name,
        func: impl FnOnce(&mut VarNames, Tm) -> T,
    ) -> T {
        let ctx = self.ctx();
        let ctx_len = ctx.len();
        let name = name.weaken_into(&ctx);
        var_names.names.push((name.clone(), ctx_len));
        let ret = self.with_cons(|var_term| {
            func(var_names, var_term)
        });
        let (_name, index) = var_names.names.pop().unwrap();
        debug_assert_eq!(index, ctx_len);
        ret
    }

    fn named_scope<T>(
        &self,
        var_names: &mut VarNames,
        name: &Name,
        func: impl FnOnce(&mut VarNames, Tm) -> T,
    ) -> Scope<T>
    where
        T: Contextual<TagScheme>,
        T: Clone + fmt::Debug,
    {
        let ctx = self.ctx();
        let ctx_len = ctx.len();
        let name = name.weaken_into(&ctx);
        var_names.names.push((name.clone(), ctx_len));
        let ret = self.scope(|var_term| {
            func(var_names, var_term)
        });
        let (_name, index) = var_names.names.pop().unwrap();
        debug_assert_eq!(index, ctx_len);
        ret
    }

    fn try_named_scope<T, E>(
        &self,
        var_names: &mut VarNames,
        name: &Name,
        func: impl FnOnce(&mut VarNames, Tm) -> Result<T, E>,
    ) -> Result<Scope<T>, E>
    where
        T: Contextual<TagScheme>,
        T: Clone + fmt::Debug,
    {
        let ctx = self.ctx();
        let ctx_len = ctx.len();
        let name = name.weaken_into(&ctx);
        var_names.names.push((name.clone(), ctx_len));
        let ret = self.try_scope(|var_term| {
            func(var_names, var_term)
        });
        let (_name, index) = var_names.names.pop().unwrap();
        debug_assert_eq!(index, ctx_len);
        ret
    }
}

#[extension(pub trait TmTagExt)]
impl Tm {
    fn cast_to_ty(&self, metavar_tag: MetavarTag) -> InferScope<Ty> {
        self
        .cast(&self.ctx().universe(), metavar_tag)
        .map(|_, ty| ty.to_ty())
    }

    fn cast(&self, ty: &Ty, metavar_tag: MetavarTag) -> InferScope<Tm> {
        self
        .ty()
        .to_term()
        .equals(&ty.to_term())
        .new_metavar(metavar_tag)
        .map(|_, eq| {
            eq.transport(self)
        })
    }
}

#[extension(pub trait ContextualTagExt)]
impl<T> T
where
    T: Contextual<TagScheme>,
    T: Clone + fmt::Debug,
{
    fn pure(&self) -> InferScope<T> {
        self
        .ctx()
        .unit_ty()
        .new_metavar(MetavarTag::Pure)
        .map(|_, _| self.clone())
    }
}

#[extension(pub trait ScopeInferScopeTagExt)]
impl<T> Scope<InferScope<T>>
where
    T: Contextual<TagScheme> + Clone + fmt::Debug,
{
    fn lift_infer_scope(self, arg_name: &Name) -> InferScope<Scope<T>> {
        let (scope, arg_name) = Ctx::into_common_ctx((&self, arg_name));

        let constraint_name = {
            scope
            .map(|_, inner| inner.constraint_name())
            .force_strengthen()
        };
        let arg_ty = scope.var_ty();
        let res_ty = scope.map(|_, inner| inner.constraint_ty());

        let new_constraint_ty = arg_ty.pi(&arg_name, res_ty.unbind());

        let new_scope = new_constraint_ty.scope(|func| {
            arg_ty
            .weaken_into(&func.ctx())
            .scope(|arg| {
                scope.bind(&arg).bind_constraint(&func.app(&arg))
            })
        });
        InferScope::from_scope(&constraint_name, &new_scope)
    }
}

#[extension(pub trait NameTagExt)]
impl Name {
    fn from_ident(ident: Ident) -> Name {
        Ctx::root().tag(&Tag::Name(ident))
    }

    fn from_metavar_tag(metavar_tag: MetavarTag) -> Name {
        Ctx::root().tag(&Tag::Metavar(Arc::new(metavar_tag)))
    }
}

#[extension(pub trait ScopeNameTagExt)]
impl Scope<Name> {
    fn force_strengthen(&self) -> Name {
        match self.try_strengthen() {
            Some(name) => name,
            None => {
                self.ctx().tag(&Tag::Metavar(Arc::new(MetavarTag::DependentConstraintName)))
            },
        }
    }
}

