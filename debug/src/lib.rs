use std::{
    thread_local,
    cell::Cell,
};

thread_local! {
    pub static INDENT: Cell<u32> = const { Cell::new(0) };
    pub static PRINTED_INDENT: Cell<u32> = const { Cell::new(0) };
}

pub struct IndentScope {
    indent: u32,
}

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

#[macro_export]
macro_rules! indent {
    ($($tokens:tt)*) => {{
        let indent = $crate::INDENT.get();
        $crate::INDENT.set(indent + 1);
        let ret = { $($tokens)* };
        $crate::INDENT.set(indent);
        ret
    }};
}

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

#[macro_export]
macro_rules! debug_indent {
    (($($tokens:tt)*), $block:block) => {{
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
        print!($($tokens)*);
        println!(" {{");
        $crate::INDENT.set(indent + 1);
        $crate::PRINTED_INDENT.set(indent + 1);

        let ret = $block;

        $crate::INDENT.set(indent);
        $crate::PRINTED_INDENT.set(indent);

        for _ in 0..indent {
            print!("    ");
        }
        println!("}}");

        ret
    }};
}

#[macro_export]
macro_rules! debug_on_panic {
    ($($tokens:tt)*) => {
        let _debug_on_panic = ::debug::DebugOnPanic::new(format!($($tokens)*));
    };
}

