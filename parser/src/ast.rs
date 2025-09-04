use crate::priv_prelude::*;

pub struct Program {
    pub items: Vec<Item>,
}

pub enum Item {
    ItemFn(Spanned<ItemFn>),
}

pub struct ItemFn {
    pub name: Ident,
    pub args: Spanned<Vec<Spanned<TypeField>>>,
    pub return_ty: Box<PrecEqual>,
    pub body: Spanned<Box<PrecStmt>>,
}

pub struct TypeField {
    pub name: Ident,
    pub ty: Box<PrecEqual>,
}

pub enum PrecAtom {
    Commit(Span),
    TypeType(Span),
    NatType(Span),
    FundsType(Span),
    Var(Ident),
    Nat(Spanned<BigUint>),
    Match(Spanned<ExprMatch>),
    ForLoop(Spanned<ExprForLoop>),
    StructType(Spanned<ExprStructType>),
    EnumType(Spanned<ExprEnumType>),
    StructTerm(Spanned<ExprStructTerm>),
    Braced(Spanned<Box<PrecStmt>>),
}

pub struct ExprMatch {
    pub elim: Box<PrecEqual>,
    pub branches: Spanned<Vec<Spanned<MatchBranch>>>,
}

pub struct MatchBranch {
    pub variant_name: Ident,
    pub payload_name: Ident,
    pub body: Box<PrecEqual>,
}

pub struct ExprForLoop {
    pub counter_name: Ident,
    pub elim: Box<PrecEqual>,
    pub state_name: Ident,
    pub state_ty: Box<PrecFunc>,
    pub init: Box<PrecFunc>,
    pub body: Spanned<Box<PrecStmt>>,
}

pub struct ExprStructType {
    pub fields: Spanned<Vec<Spanned<TypeField>>>,
}

pub struct ExprEnumType {
    pub variants: Spanned<Vec<Spanned<TypeField>>>,
}

pub struct ExprStructTerm {
    pub fields: Spanned<Vec<Spanned<ExprStructTermField>>>,
}

pub struct ExprStructTermField {
    pub name: Ident,
    pub expr_ty_opt_opt: Option<(Option<PrecEqual>, PrecEqual)>,
}

pub enum PrecStmt {
    Let(Spanned<LetStmt>),
    Blank(Span),
    Other(PrecFunc),
}

pub enum PatPrecInj {
    //Refl(Box<PatPrecInj>),
    Other(PatPrecAtom),
}

pub enum PatPrecAtom {
    Var(Ident),
    Struct(Spanned<PatStructTerm>),
}

pub struct PatStructTerm {
    pub fields: Spanned<Vec<Spanned<PatStructTermField>>>,
}

pub struct PatStructTermField {
    pub name: Ident,
    pub pat_ty_opt_opt: Option<(Option<PrecEqual>, PatPrecInj)>,
}

pub struct LetStmt {
    pub var_pat: Box<PatPrecInj>,
    pub var_expr: Box<PrecEqual>,
    pub body: Box<PrecStmt>,
}

pub enum PrecFunc {
    FuncType(Spanned<ExprFuncType>),
    FuncTerm(Spanned<ExprFuncTerm>),
    Other(PrecEqual),
}

pub struct ExprFuncType {
    pub args: Spanned<Vec<Spanned<TypeField>>>,
    pub return_ty: Box<PrecFunc>,
}

pub struct ExprFuncTerm {
    pub args: Spanned<Vec<Spanned<TypeField>>>,
    pub body: Box<PrecFunc>,
}

pub enum PrecEqual {
    Equal(Spanned<ExprEqual>),
    Other(PrecAdd),
}

pub struct ExprEqual {
    pub eq_expr_0: Box<PrecAdd>,
    pub eq_expr_1: Box<PrecAdd>,
}

pub enum PrecAdd {
    Add(Spanned<ExprAdd>),
    Other(PrecMul),
}

pub struct ExprAdd {
    pub lhs: Box<PrecAdd>,
    pub rhs: Box<PrecMul>,
}

pub enum PrecMul {
    Mul(Spanned<ExprMul>),
    Other(PrecInj),
}

pub struct ExprMul {
    pub lhs: Box<PrecMul>,
    pub rhs: Box<PrecInj>,
}

pub enum PrecInj {
    Inj(Spanned<ExprInj>),
    Refl(Spanned<ExprRefl>),
    Other(PrecProj),
}

pub struct ExprInj {
    pub variant_name: Ident,
    pub payload: Box<PrecInj>,
}

pub struct ExprRefl {
    pub eq_expr: Box<PrecInj>,
}

pub enum PrecProj {
    Proj(Spanned<ExprProj>),
    Other(PrecApp),
}

pub struct ExprProj {
    pub base: Box<PrecProj>,
    pub field_name: Ident,
}

pub enum PrecApp {
    App(Spanned<ExprApp>),
    Other(PrecAtom),
}

pub struct ExprApp {
    pub func: Box<PrecApp>,
    pub args: Spanned<Vec<Spanned<FuncAppArg>>>,
}

pub struct FuncAppArg {
    pub arg_name: Ident,
    pub arg_expr_opt: Option<Box<PrecFunc>>,
}

impl PrecFunc {
    pub fn span(&self) -> Span {
        match self {
            PrecFunc::FuncType(x) => x.span(),
            PrecFunc::FuncTerm(x) => x.span(),
            PrecFunc::Other(x) => x.span(),
        }
    }
}

impl PrecEqual {
    pub fn span(&self) -> Span {
        match self {
            PrecEqual::Equal(expr_equal) => expr_equal.span(),
            PrecEqual::Other(prec_add) => prec_add.span(),
        }
    }
}

impl PrecAdd {
    pub fn span(&self) -> Span {
        match self {
            PrecAdd::Add(expr_add) => expr_add.span(),
            PrecAdd::Other(prec_mul) => prec_mul.span(),
        }
    }
}

impl PrecMul {
    pub fn span(&self) -> Span {
        match self {
            PrecMul::Mul(expr_mul) => expr_mul.span(),
            PrecMul::Other(prec_inj) => prec_inj.span(),
        }
    }
}

impl PrecInj {
    pub fn span(&self) -> Span {
        match self {
            PrecInj::Inj(expr_inj) => expr_inj.span(),
            PrecInj::Refl(expr_refl) => expr_refl.span(),
            PrecInj::Other(prec_proj) => prec_proj.span(),
        }
    }
}

impl PrecProj {
    pub fn span(&self) -> Span {
        match self {
            PrecProj::Proj(expr_proj) => expr_proj.span(),
            PrecProj::Other(prec_app) => prec_app.span(),
        }
    }
}

impl PrecApp {
    pub fn span(&self) -> Span {
        match self {
            PrecApp::App(expr_app) => expr_app.span(),
            PrecApp::Other(prec_atom) => prec_atom.span(),
        }
    }
}

impl PrecAtom {
    pub fn span(&self) -> Span {
        match self {
            PrecAtom::Commit(s) => s.clone(),
            PrecAtom::TypeType(s) => s.clone(),
            PrecAtom::NatType(s) => s.clone(),
            PrecAtom::FundsType(s) => s.clone(),
            PrecAtom::Var(s) => s.span(),
            PrecAtom::Nat(x) => x.span(),
            PrecAtom::Match(x) => x.span(),
            PrecAtom::StructType(x) => x.span(),
            PrecAtom::EnumType(x) => x.span(),
            PrecAtom::StructTerm(x) => x.span(),
            PrecAtom::ForLoop(x) => x.span(),
            PrecAtom::Braced(x) => x.span(),
        }
    }
}

impl PatPrecInj {
    pub fn span(&self) -> Span {
        match self {
            PatPrecInj::Other(x) => x.span(),
        }
    }
}

impl PatPrecAtom {
    pub fn span(&self) -> Span {
        match self {
            PatPrecAtom::Var(s) => s.span(),
            PatPrecAtom::Struct(x) => x.span(),
        }
    }
}

