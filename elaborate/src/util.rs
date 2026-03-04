use crate::priv_prelude::*;

#[extension(pub trait WrapOkMethod)]
impl<T> T {
    fn wrap_ok<E>(self) -> Result<T, E> {
        Ok(self)
    }
}

pub fn as_equal<T: PartialEq>(x: T, y: T) -> Option<T> {
    if x == y {
        Some(x)
    } else {
        None
    }
}
