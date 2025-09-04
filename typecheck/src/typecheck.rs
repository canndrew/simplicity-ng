use crate::priv_prelude::*;

#[derive(Error, Debug)]
pub enum CheckError {
    #[error("unknown var {:?}", name)]
    UnknownVar {
        name: Name,
    },
}

/*
fn check_prec_atom(ctx: &Ctx, prec_atom: &Spanned<ast::PrecAtom>) -> Result<Scope<Tm>, CheckError> {
    match &prec_atom.inner {
        ast::PrecAtom::TypeType(_span) => {

        },
    }
}
*/

