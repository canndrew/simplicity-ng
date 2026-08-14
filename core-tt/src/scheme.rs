use core::convert::Infallible;

use crate::priv_prelude::*;

pub trait Scheme: Sized + 'static {
    type Tag: PartialEq + Eq + PartialOrd + Ord + fmt::Debug + Clone + hash::Hash + 'static;
    fn interner() -> &'static Interner<Self>;
}

impl Scheme for Infallible {
    type Tag = Infallible;

    fn interner() -> &'static Interner<Infallible> {
        lazy_static! {
            static ref NEVER_INTERNER: Interner<Infallible> = Interner::new();
        }
        &*NEVER_INTERNER
    }
}

