use crate::priv_prelude::*;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("unexpected token at {}", token.span())]
    UnexpectedToken {
        token: Token,
    },
    #[error("{0}")]
    Tokenize(TokenizeError),
    #[error("error parsing let pattern at {}", let_span)]
    ParseLetPattern {
        let_span: Span,
    },
    #[error("error parsing let statement ty starting at {}", colon_span)]
    ParseLetTy {
        colon_span: Span,
    },
    #[error("expected '=' after pattern for let statement at {}", let_span)]
    ParseLetEq {
        let_span: Span,
    },
    #[error("error parsing let rhs at {}", let_span)]
    ParseLetRhs {
        let_span: Span,
    },
    #[error("error parsing let body at {}", let_span)]
    ParseLetBody {
        let_span: Span,
    },
    #[error("error parsing block at {}", block_span)]
    ParseBlock {
        block_span: Span,
    },
    #[error("expected fn arguments at {}", fn_span)]
    MissingFnTermArgs {
        fn_span: Span,
    },
    #[error("error parsing field type starting at {}", colon_span)]
    ParseTypeFieldTy {
        colon_span: Span,
    },
    #[error("error parsing function arg type starting at {}", colon_span)]
    ParseFuncTermArgTy {
        colon_span: Span,
    },
}

impl From<UnexpectedTokenError> for ParseError {
    fn from(err: UnexpectedTokenError) -> ParseError {
        ParseError::UnexpectedToken { token: err.token }
    }
}

impl From<TokenizeError> for ParseError {
    fn from(err: TokenizeError) -> ParseError {
        ParseError::Tokenize(err)
    }
}

#[derive(Clone, Copy)]
enum Keyword {
    Def,
    FnLower,
    FnUpper,
    Let,
    Refl,
    Match,
    For,
    In,
    With,
    Struct,
    Enum,
    Type,
    Nat,
    /*
    Funds,
    Commit,
    */
}

impl Keyword {
    fn all() -> &'static [Keyword] {
        &[
            Keyword::Def,
            Keyword::FnLower,
            Keyword::FnUpper,
            Keyword::Let,
            Keyword::Refl,
            Keyword::Match,
            Keyword::For,
            Keyword::In,
            Keyword::With,
            Keyword::Struct,
            Keyword::Enum,
            Keyword::Type,
            Keyword::Nat,
            /*
            Keyword::Funds,
            Keyword::Commit,
            */
        ]
    }

    fn as_str(&self) -> &'static str {
        match self {
            Keyword::Def => "def",
            Keyword::FnLower => "fn",
            Keyword::FnUpper => "Fn",
            Keyword::Let => "let",
            Keyword::Refl => "refl",
            Keyword::Match => "match",
            Keyword::For => "for",
            Keyword::In => "in",
            Keyword::With => "with",
            Keyword::Struct => "struct",
            Keyword::Enum => "enum",
            Keyword::Type => "Type",
            Keyword::Nat => "Nat",
            /*
            Keyword::Funds => "Funds",
            Keyword::Commit => "commit",
            */
        }
    }
}

fn keyword<E>(keyword: Keyword) -> impl Parser<Output = (), Error = E> {
    ident()
    .filter_map(move |ident| {
        (ident.as_str() == keyword.as_str()).then_some(())
    })
}

fn name<E>() -> impl Parser<Output = Ident, Error = E> {
    ident().filter_map(move |ident| {
        if Keyword::all().iter().all(|keyword| ident.as_str() != keyword.as_str()) {
            Some(ident)
        } else {
            None
        }
    })
}

pub fn program() -> Box<dyn Parser<Output = ast::Program, Error = ParseError>> {
    item().many().map(|items| ast::Program { items }).box_dyn()
}

fn item() -> Box<dyn Parser<Output = ast::Item, Error = ParseError>> {
    item_def().spanned().map(|item| ast::Item::ItemDef(item)).box_dyn()
}

fn item_def() -> Box<dyn Parser<Output = ast::ItemDef, Error = ParseError>> {
    all_of((
        keyword(Keyword::Def).unit_then(name()),
        parens(|_| type_field().spanned().box_dyn().comma_separated()),
        punct(PunctKind::Arrow).unit_then(prec_equal().boxed()),
        curly_braced(|_| prec_stmt().boxed()),
    ))
    .map(|(name, args, return_ty, body)| ast::ItemDef { name, args, return_ty, body })
    .box_dyn()
}

fn let_stmt() -> Box<dyn Parser<Output = ast::LetStmt, Error = ParseError>> {
    keyword(Keyword::Let)
    .spanned()
    .spanned_unit_then(|let_span| {
        all_of((
            {
                let let_span = let_span.clone();
                pat_prec_inj().boxed().required(move || ParseError::ParseLetPattern { let_span: let_span.clone() })
            },
            {
                parens(|_| {
                    func_term_arg()
                    .spanned()
                    .box_dyn()
                    .comma_separated()
                })
                .optional()
            },
            {
                punct(PunctKind::Colon)
                .spanned()
                .spanned_unit_then(|colon_span| {
                    let colon_span = colon_span.clone();
                    prec_func()
                    .required(move || ParseError::ParseLetTy { colon_span: colon_span.clone() })
                })
                .boxed()
                .optional()
            },
            {
                let let_span_0 = let_span.clone();
                let let_span_1 = let_span.clone();
                punct(PunctKind::Equal)
                .required(move || ParseError::ParseLetEq { let_span: let_span_0.clone() })
                .unit_then(prec_func())
                .boxed()
                .required(move || ParseError::ParseLetRhs { let_span: let_span_1.clone() })
            },
            {
                let let_span = let_span.clone();
                punct(PunctKind::Semicolon)
                .unit_then(prec_stmt())
                .boxed()
                .required(move || ParseError::ParseLetBody { let_span: let_span.clone() })
            },
        ))
        .map(|(var_pat, var_args_opt, var_ty_opt, var_expr, body)| {
            ast::LetStmt { var_pat, var_args_opt, var_ty_opt, var_expr, body }
        })
    })
    .box_dyn()
}

fn expr_func_type() -> Box<dyn Parser<Output = ast::ExprFuncType, Error = ParseError>> {
    all_of((
        keyword(Keyword::FnUpper).unit_then(parens(|_| func_term_arg().spanned().box_dyn().comma_separated())),
        punct(PunctKind::Arrow).unit_then(prec_func().boxed()),
    ))
    .map(|(args, return_ty)| ast::ExprFuncType { args, return_ty })
    .box_dyn()
}

fn func_term_arg() -> Box<dyn Parser<Output = ast::FuncTermArg, Error = ParseError>> {
    name()
    .then(func_term_arg_ty().optional())
    .map(|(arg_name, arg_ty_opt)| ast::FuncTermArg { arg_name, arg_ty_opt })
    .box_dyn()
}

fn func_term_arg_ty() -> Box<dyn Parser<Output = ast::FuncTermArgTy, Error = ParseError>> {
    all_of((
        parens(|_| {
            func_term_arg()
            .spanned()
            .box_dyn()
            .comma_separated()
        })
        .optional(),
        punct(PunctKind::Colon)
        .spanned()
        .spanned_unit_then(|colon_span| {
            prec_func()
            .required(move || ParseError::ParseFuncTermArgTy { colon_span: colon_span.clone() })
            .boxed()
        })
    ))
    .map(|(args_opt, ty)| ast::FuncTermArgTy { args_opt, ty })
    .box_dyn()
}

fn expr_func_term() -> Box<dyn Parser<Output = ast::ExprFuncTerm, Error = ParseError>> {
    all_of((
        keyword(Keyword::FnLower)
        .spanned()
        .spanned_unit_then(|fn_span| {
            let fn_span = fn_span.clone();
            parens(|_| {
                func_term_arg()
                .spanned()
                .box_dyn()
                .comma_separated()
            })
            .required(move || ParseError::MissingFnTermArgs { fn_span: fn_span.clone() })
        }),
        punct(PunctKind::FatArrow).unit_then(prec_func().boxed()),
    ))
    .map(|(args, body)| ast::ExprFuncTerm { args, body })
    .box_dyn()
}

fn expr_equal() -> Box<dyn Parser<Output = ast::ExprEqual, Error = ParseError>> {
    all_of((
        prec_add().boxed(),
        punct(PunctKind::DoubleEqual).unit_then(prec_add().boxed()),
    ))
    .map(|(eq_expr_0, eq_expr_1)| ast::ExprEqual { eq_expr_0, eq_expr_1 })
    .box_dyn()
}

fn expr_inj() -> Box<dyn Parser<Output = ast::ExprInj, Error = ParseError>> {
    all_of((
        punct(PunctKind::Dot).unit_then(name()),
        prec_inj().boxed(),
    ))
    .map(|(variant_name, payload)| ast::ExprInj { variant_name, payload })
    .box_dyn()
}

fn expr_refl() -> Box<dyn Parser<Output = ast::ExprRefl, Error = ParseError>> {
    keyword(Keyword::Refl)
    .unit_then(prec_inj().boxed())
    .map(|eq_expr| ast::ExprRefl { eq_expr })
    .box_dyn()
}

fn func_app_arg() -> Box<dyn Parser<Output = ast::FuncAppArg, Error = ParseError>> {
    all_of((
        name(),
        func_app_arg_expr().optional(),
    ))
    .map(|(arg_name, arg_expr_opt)| ast::FuncAppArg { arg_name, arg_expr_opt })
    .box_dyn()
}

fn func_app_arg_expr() -> Box<dyn Parser<Output = ast::FuncAppArgExpr, Error = ParseError>> {
    all_of((
        parens(|_| {
            func_term_arg()
            .spanned()
            .box_dyn()
            .comma_separated()
        })
        .optional(),
        punct(PunctKind::Equal).unit_then(prec_func().boxed()),
    ))
    .map(|(args_opt, expr)| ast::FuncAppArgExpr { args_opt, expr })
    .box_dyn()
}

fn expr_match() -> Box<dyn Parser<Output = ast::ExprMatch, Error = ParseError>> {
    all_of((
        keyword(Keyword::Match).unit_then(prec_equal().boxed()),
        curly_braced(|_| match_branch().spanned().box_dyn().comma_separated()),
    ))
    .map(|(elim, branches)| ast::ExprMatch { elim, branches })
    .box_dyn()
}

fn match_branch() -> Box<dyn Parser<Output = ast::MatchBranch, Error = ParseError>> {
    all_of((
        name(),
        name(),
        punct(PunctKind::FatArrow).unit_then(prec_equal().boxed()),
    ))
    .map(|(variant_name, payload_name, body)| {
        ast::MatchBranch { variant_name, payload_name, body }
    })
    .box_dyn()
}

fn expr_for_loop() -> Box<dyn Parser<Output = ast::ExprForLoop, Error = ParseError>> {
    all_of((
        keyword(Keyword::For).unit_then(name()),
        keyword(Keyword::In).unit_then(prec_equal().boxed()),
        keyword(Keyword::With).unit_then(name()),
        punct(PunctKind::Colon).unit_then(prec_func().boxed()),
        punct(PunctKind::Equal).unit_then(prec_func().boxed()),
        curly_braced(|_| prec_stmt().boxed()),
    ))
    .map(|(counter_name, elim, state_name, state_ty, init, body)| {
        ast::ExprForLoop { counter_name, elim, state_name, state_ty, init, body }
    })
    .box_dyn()
}

fn expr_struct_type() -> Box<dyn Parser<Output = ast::ExprStructType, Error = ParseError>> {
    keyword(Keyword::Struct)
    .unit_then(curly_braced(|_| type_field().spanned().box_dyn().comma_separated()))
    .map(|fields| ast::ExprStructType { fields })
    .box_dyn()
}

fn expr_enum_type() -> Box<dyn Parser<Output = ast::ExprEnumType, Error = ParseError>> {
    keyword(Keyword::Enum)
    .unit_then(curly_braced(|_| type_field().spanned().box_dyn().comma_separated()))
    .map(|variants| ast::ExprEnumType { variants })
    .box_dyn()
}

fn type_field() -> Box<dyn Parser<Output = ast::TypeField, Error = ParseError>> {
    name()
    .then(
        punct(PunctKind::Colon)
        .spanned()
        .spanned_unit_then(|colon_span| {
            prec_equal()
            .required(move || ParseError::ParseTypeFieldTy { colon_span: colon_span.clone() })
            .boxed()
        })
    )
    .map(|(name, ty)| ast::TypeField { name, ty })
    .box_dyn()
}

fn expr_struct_term() -> Box<dyn Parser<Output = ast::ExprStructTerm, Error = ParseError>> {
    parens(|_| expr_struct_term_field().spanned().box_dyn().comma_separated())
    .map(|fields| ast::ExprStructTerm { fields })
    .box_dyn()
}

fn expr_struct_term_field() -> Box<dyn Parser<Output = ast::ExprStructTermField, Error = ParseError>> {
    name()
    .then(
        punct(PunctKind::Colon)
        .unit_then(prec_equal())
        .optional()
        .then(punct(PunctKind::Equal).unit_then(prec_equal()))
        .optional()
    )
    .map(|(name, expr_ty_opt_opt)| ast::ExprStructTermField { name, expr_ty_opt_opt })
    .box_dyn()
}

/*
fn expr_commit() -> Box<dyn Parser<Output = Span, Error = ParseError>> {
    keyword(Keyword::Commit).spanned().map(|spanned| spanned.span()).box_dyn()
}
*/

fn expr_type_type() -> Box<dyn Parser<Output = Span, Error = ParseError>> {
    keyword(Keyword::Type).spanned().map(|spanned| spanned.span()).box_dyn()
}

fn expr_nat_type() -> Box<dyn Parser<Output = Span, Error = ParseError>> {
    keyword(Keyword::Nat).spanned().map(|spanned| spanned.span()).box_dyn()
}

/*
fn expr_funds_type() -> Box<dyn Parser<Output = Span, Error = ParseError>> {
    keyword(Keyword::Funds).spanned().map(|spanned| spanned.span()).box_dyn()
}
*/

pub fn prec_stmt() -> Box<dyn Parser<Output = ast::PrecStmt, Error = ParseError>> {
    lazy(|| {
        any_of((
            let_stmt().spanned().map(ast::PrecStmt::Let),
            prec_func().map(ast::PrecStmt::Other),
            pure(()).spanned().map(|spanned| ast::PrecStmt::Blank(spanned.span)),
        ))
    })
    .box_dyn()
}

fn prec_func() -> Box<dyn Parser<Output = ast::PrecFunc, Error = ParseError>> {
    lazy(|| {
        any_of((
            expr_func_type().spanned().map(ast::PrecFunc::FuncType),
            expr_func_term().spanned().map(ast::PrecFunc::FuncTerm),
            prec_equal().map(ast::PrecFunc::Other),
        ))
    })
    .box_dyn()
}

fn prec_equal() -> Box<dyn Parser<Output = ast::PrecEqual, Error = ParseError>> {
    lazy(|| {
        any_of((
            expr_equal().spanned().map(ast::PrecEqual::Equal),
            prec_add().map(ast::PrecEqual::Other),
        ))
    })
    .box_dyn()
}

fn prec_add() -> Box<dyn Parser<Output = ast::PrecAdd, Error = ParseError>> {
    lazy(|| {
        prec_mul()
        .map(ast::PrecAdd::Other)
        .then(punct(PunctKind::Plus).unit_then(prec_mul().boxed()).many())
        .map(|(lhs, rhss)| rhss.into_iter().fold(lhs, |lhs, rhs| {
            let span = Span::combine(&lhs.span(), &rhs.span());
            ast::PrecAdd::Add(Spanned::new(span, ast::ExprAdd { lhs: Box::new(lhs), rhs }))
        }))
    })
    .box_dyn()
}

fn prec_mul() -> Box<dyn Parser<Output = ast::PrecMul, Error = ParseError>> {
    lazy(|| {
        prec_inj()
        .map(ast::PrecMul::Other)
        .then(punct(PunctKind::Star).unit_then(prec_inj().boxed()).many())
        .map(|(lhs, rhss)| rhss.into_iter().fold(lhs, |lhs, rhs| {
            let span = Span::combine(&lhs.span(), &rhs.span());
            ast::PrecMul::Mul(Spanned::new(span, ast::ExprMul { lhs: Box::new(lhs), rhs }))
        }))
    })
    .box_dyn()
}

fn prec_inj() -> Box<dyn Parser<Output = ast::PrecInj, Error = ParseError>> {
    lazy(|| {
        any_of((
            expr_inj().spanned().map(ast::PrecInj::Inj),
            expr_refl().spanned().map(ast::PrecInj::Refl),
            prec_proj().map(ast::PrecInj::Other),
        ))
    })
    .box_dyn()
}

fn prec_proj() -> Box<dyn Parser<Output = ast::PrecProj, Error = ParseError>> {
    lazy(|| {
        prec_app()
        .map(ast::PrecProj::Other)
        .then(punct(PunctKind::Dot).unit_then(name()).many())
        .map(|(base, field_names)| field_names.into_iter().fold(base, |base, field_name| {
            let span = Span::combine(&base.span(), &field_name.span());
            ast::PrecProj::Proj(Spanned::new(span, ast::ExprProj { base: Box::new(base), field_name }))
        }))
    })
    .box_dyn()
}

fn prec_app() -> Box<dyn Parser<Output = ast::PrecApp, Error = ParseError>> {
    lazy(|| {
        prec_atom()
        .map(ast::PrecApp::Other)
        .then(parens(|_| func_app_arg().spanned().box_dyn().comma_separated()).many())
        .map(|(func, argss)| argss.into_iter().fold(func, |func, args| {
            let span = Span::combine(&func.span(), &args.span);
            ast::PrecApp::App(Spanned::new(span, ast::ExprApp { func: Box::new(func), args }))
        }))
    })
    .box_dyn()
}

fn prec_atom() -> Box<dyn Parser<Output = ast::PrecAtom, Error = ParseError>> {
    lazy(|| {
        any_of((
            //expr_commit().map(ast::PrecAtom::Commit),
            expr_type_type().map(ast::PrecAtom::TypeType),
            expr_nat_type().map(ast::PrecAtom::NatType),
            //expr_funds_type().map(ast::PrecAtom::FundsType),
            name().map(ast::PrecAtom::Var),
            number().spanned().map(ast::PrecAtom::Nat),
            expr_match().spanned().map(ast::PrecAtom::Match),
            expr_for_loop().spanned().map(ast::PrecAtom::ForLoop),
            expr_struct_type().spanned().map(ast::PrecAtom::StructType),
            expr_enum_type().spanned().map(ast::PrecAtom::EnumType),
            expr_struct_term().spanned().map(ast::PrecAtom::StructTerm),
            curly_braced(|block_span| {
                prec_stmt()
                .boxed()
                .required(move || ParseError::ParseBlock { block_span: block_span.clone() })
            }).map(ast::PrecAtom::Braced),
        ))
    })
    .box_dyn()
}

fn pat_refl() -> Box<dyn Parser<Output = ast::PatRefl, Error = ParseError>> {
    keyword(Keyword::Refl)
    .unit_then(pat_prec_inj().boxed())
    .map(|eq_pat| ast::PatRefl { eq_pat })
    .box_dyn()
}

fn pat_struct_term() -> Box<dyn Parser<Output = ast::PatStructTerm, Error = ParseError>> {
    parens(|_| pat_struct_term_field().spanned().box_dyn().comma_separated())
    .map(|fields| ast::PatStructTerm { fields })
    .box_dyn()
}

fn pat_struct_term_field() -> Box<dyn Parser<Output = ast::PatStructTermField, Error = ParseError>> {
    name()
    .then(
        punct(PunctKind::Colon)
        .unit_then(prec_equal())
        .optional()
        .then(punct(PunctKind::Equal).unit_then(pat_prec_inj()))
        .optional()
    )
    .map(|(name, pat_ty_opt_opt)| ast::PatStructTermField { name, pat_ty_opt_opt })
    .box_dyn()
}

fn pat_prec_inj() -> Box<dyn Parser<Output = ast::PatPrecInj, Error = ParseError>> {
    lazy(|| {
        any_of((
            pat_refl().spanned().map(ast::PatPrecInj::Refl),
            pat_prec_atom().map(ast::PatPrecInj::Other)
        ))
    })
    .box_dyn()
}

fn pat_prec_atom() -> Box<dyn Parser<Output = ast::PatPrecAtom, Error = ParseError>> {
    lazy(||
        any_of((
            name().map(ast::PatPrecAtom::Var),
            pat_struct_term().spanned().map(ast::PatPrecAtom::Struct),
        ))
    )
    .box_dyn()
}

