use crate::priv_prelude::*;

mod closed;
mod iso;
mod map_functor;

pub(crate) enum StringScheme {}
impl core_tt::Scheme for StringScheme {
    type Tag = String;

    fn interner() -> &'static core_tt::Interner<StringScheme> {
        lazy_static! {
            static ref INTERNER: core_tt::Interner<StringScheme> = core_tt::Interner::new();
        }
        &*INTERNER
    }
}

impl Scheme for StringScheme {
    fn tag_from_str(s: &str) -> String {
        String::from(s)
    }

    fn try_tag_as_string(tag: &String) -> Option<String> {
        Some(tag.clone())
    }
}

