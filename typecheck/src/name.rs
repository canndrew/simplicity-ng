use crate::priv_prelude::*;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Name {
    Real(Ident),
    Fake(Fake),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Fake {}

impl core_tt::Name for Name {}

