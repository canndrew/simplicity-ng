pub fn as_equal<T: PartialEq>(val_0: T, val_1: T) -> Option<T> {
    if val_0 == val_1 {
        Some(val_0)
    } else {
        None
    }
}

/*
macro_rules! count_tokens {
    () => { 0 };
    ($first:tt $($rest:tt)*) => {
        1 + count_tokens!($($rest)*)
    };
}
*/
