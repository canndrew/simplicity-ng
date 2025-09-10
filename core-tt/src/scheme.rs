use crate::priv_prelude::*;

pub trait Scheme: Sized + 'static {
    type UserTy: PartialEq + Eq + PartialOrd + Ord + fmt::Debug + Clone + hash::Hash + 'static;
    type UserTm: PartialEq + Eq + PartialOrd + Ord + fmt::Debug + Clone + hash::Hash + 'static;
    fn user_ty_of(user_tm: &Self::UserTm) -> Self::UserTy;
    fn interner() -> &'static Interner<Self>;
}

impl Scheme for ! {
    type UserTy = !;
    type UserTm = !;

    fn user_ty_of(user_tm: &!) -> ! {
        *user_tm
    }

    fn interner() -> &'static Interner<!> {
        lazy_static! {
            static ref NEVER_INTERNER: Interner<!> = Interner::new();
        }
        &*NEVER_INTERNER
    }
}

