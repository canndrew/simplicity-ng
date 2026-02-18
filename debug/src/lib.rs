use std::{
    thread_local,
    cell::Cell,
};

thread_local! {
    #[doc(hidden)]
    pub static INDENT: Cell<u32> = const { Cell::new(0) };
    #[doc(hidden)]
    pub static PRINTED_INDENT: Cell<u32> = const { Cell::new(0) };
}

#[doc(hidden)]
pub struct IndentScope {
    indent: u32,
}

/// Creates a value that causes `debug!` to be indented by one extra level until the value is
/// dropped.
///
/// # Examples
///
/// ```
/// # use debug::{debug, indent_scope};
/// debug!("this prints with indentation x");
/// let _indent = indent_scope();
/// debug!("this prints with indentation x + 1");
/// ```
pub fn indent_scope() -> IndentScope {
    let indent = INDENT.get();
    INDENT.set(indent + 1);
    IndentScope { indent }
}

impl Drop for IndentScope {
    fn drop(&mut self) {
        INDENT.set(self.indent);
    }
}

#[doc(hidden)]
pub struct DebugOnPanic {
    text: String,
}

impl DebugOnPanic {
    pub fn new(text: String) -> DebugOnPanic {
        DebugOnPanic { text }
    }
}

impl Drop for DebugOnPanic {
    fn drop(&mut self) {
        if std::thread::panicking() {
            debug!("{}", self.text);
        }
    }
}

/// Prints to stdout with the same syntax as `println!` but also respects indentation set with
/// `indent_scope`.
#[macro_export]
macro_rules! debug {
    ($($tokens:tt)*) => {{
        while $crate::PRINTED_INDENT.get() < $crate::INDENT.get() {
            let indent = $crate::PRINTED_INDENT.get();
            for _ in 0..indent {
                print!("    ");
            }
            println!("{{");
            $crate::PRINTED_INDENT.set(indent + 1);
        }
        while $crate::PRINTED_INDENT.get() > $crate::INDENT.get() {
            let indent = $crate::PRINTED_INDENT.get() - 1;
            for _ in 0..indent {
                print!("    ");
            }
            println!("}}");
            $crate::PRINTED_INDENT.set(indent);
        }
        let indent = $crate::INDENT.get();
        for _ in 0..indent {
            print!("    ");
        }
        println!($($tokens)*);
    }};
}

/// Creates a value that prints the given message if the thread panics before the value is dropped.
///
/// Useful for debugging panics when you need more information than just a stack trace but don't
/// want to spam stdout with useless info like you might with `debug!`. Respects indentation set
/// with `indent_scope`. Messages are printed in reverse order as the stack unwinds.
///
/// # Examples
///
/// ```should_panic
/// # use debug::debug_on_panic;
/// {
///     debug_on_panic!("this will not be printed");
/// }
/// {
///     debug_on_panic!("this will be");
///     panic!("oh no!");
/// }
/// ```
#[macro_export]
macro_rules! debug_on_panic {
    ($($tokens:tt)*) => {
        let _debug_on_panic = ::debug::DebugOnPanic::new(format!($($tokens)*));
    };
}

