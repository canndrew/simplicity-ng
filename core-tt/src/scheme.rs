use crate::priv_prelude::*;

pub trait Scheme: Sized + 'static {
    type Tag: PartialEq + Eq + PartialOrd + Ord + fmt::Debug + Clone + hash::Hash + 'static;
    fn interner() -> &'static Interner<Self>;
}

impl Scheme for ! {
    type Tag = !;

    fn interner() -> &'static Interner<!> {
        lazy_static! {
            static ref NEVER_INTERNER: Interner<!> = Interner::new();
        }
        &*NEVER_INTERNER
    }
}

