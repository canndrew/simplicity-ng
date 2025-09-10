pub fn as_equal<T: PartialEq>(x: T, y: T) -> Option<T> {
    if x == y {
        Some(x)
    } else {
        None
    }
}
