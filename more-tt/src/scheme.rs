use crate::priv_prelude::*;

pub trait Scheme: core_tt::Scheme {
    fn tag_from_str(s: &str) -> Self::Tag;
    fn try_tag_as_string(tag: &Self::Tag) -> Option<String>;
}

#[extension(pub trait SchemeExt)]
impl<S: Scheme> S {
    fn name_from_str(s: &str) -> Name<S> {
        Ctx::root().tag(&S::tag_from_str(s))
    }

    fn try_name_as_string(name: &Name<S>) -> Option<String> {
        match name.kind() {
            NameKind::Tag { tag } => S::try_tag_as_string(&tag),
            NameKind::Stuck { .. } => None,
        }
    }
}

