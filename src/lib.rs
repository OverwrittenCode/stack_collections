//! stack_collections: Stack-allocated collections for Rust
//!
//! Provides `StackString`, `StackVec`, and `StackArrayString`.
//! These are fixed-capacity, stack-allocated collections designed for
//! `no_std` environments, zero heap allocations, predictable memory usage,
//! and deterministic performance.

#![deny(missing_docs)]
#![deny(clippy::missing_docs_in_private_items)]
#![no_std]
#![cfg_attr(feature = "std", allow(unused))]
#![cfg_attr(feature = "nightly", feature(ascii_char))]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(feature = "std")]
extern crate std;

use core::hash::{Hash, Hasher};
use core::hint::unreachable_unchecked;
use core::iter::FromIterator;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut, Index, IndexMut};
use core::slice;
use core::{fmt, mem, ptr, str};

#[cfg(feature = "std")]
use std::{
    borrow::ToOwned,
    io::{self, Write},
    string::String,
};

/// Helper macro to define unchecked, normal, and try variants of a method.
macro_rules! define_variants {
    (
        $(#[$meta:meta])*
        fn $name:ident(&mut $self:ident $(, $param:ident: $param_ty:ty)*) $(-> $ret:ty)?,
        $(where_clause: { $($where_clause:tt)* } )?

        normal_brief: $normal_brief:literal,
        try_brief: $try_brief:literal,
        unchecked_brief_suffix: $unchecked_brief_suffix:literal,
        checks: {
            $($check:expr => $error:literal),+ $(,)?
        },
        prefixes: {
            normal: {$($normal_prefix:tt)*},
            unchecked: {$($unchecked_prefix:tt)*},
            try: {$($try_prefix:tt)*},
        },
        unchecked_fn: $unchecked_fn:ident,
        try_fn: $try_fn:ident,

        body: { $($body:tt)* },

        $(examples: {
            normal: { $($ex_normal:tt)* }
            try: { $($ex_try:tt)* }
        })?
    ) => {
        $(#[$meta])*
        #[doc = concat!(" ", $normal_brief, ", ", $unchecked_brief_suffix, ".")]
        ///
        #[doc = concat!("See also [`Self::", stringify!($name), "`] for the safe version and [`Self::", stringify!($try_fn), "`] for the `Option` returning version.")]
        ///
        /// # Safety
        ///
        /// Calling this function when any of the following conditions are **`true`** is **undefined behavior**:
        $( #[doc = concat!(" - `", stringify!($check), "`")] )+
        #[inline]
        $($unchecked_prefix)* unsafe fn $unchecked_fn(&mut $self $(, $param: $param_ty)*) $(-> $ret)?
        $(where $($where_clause)*)?
        {
            $($body)*
        }
        $(#[$meta])*
        #[doc = concat!(" ", $normal_brief, ".")]
        ///
        #[doc = concat!("See also [`Self::", stringify!($unchecked_fn), "`] for the unchecked version and [`Self::", stringify!($try_fn), "`] for the `Option` returning version.")]
        ///
        /// # Panics
        ///
        $( #[doc = concat!(" - \"", $error, "\" if `", stringify!($check), "`")] )+
        $(
            ///
            /// # Examples
            ///
            $($ex_normal)*
        )?
        #[inline]
        $($normal_prefix)* fn $name(&mut $self $(, $param: $param_ty)*) $(-> $ret)?
        $(where $($where_clause)*)?
        {
            $( assert!(!($check), $error); )+
            unsafe { $self.$unchecked_fn($($param),*) }
        }

        $(#[$meta])*
        #[doc = concat!(" ", $try_brief, ".")]
        ///
        #[doc = concat!("See also [`Self::", stringify!($name), "`] for the panic-on-error version and [`Self::", stringify!($unchecked_fn), "`] for the unchecked version.")]
        ///
        /// Returns `None` if any of these conditions are **`false`**:
        $( #[doc = concat!(" - `", stringify!($check), "`")] )+
        $(
            ///
            /// # Examples
            ///
            $($ex_try)*
        )?
        #[must_use]
        #[inline]
        $($try_prefix)* fn $try_fn(&mut $self $(, $param: $param_ty)*) $(-> Option<$ret>)?
        $(where $($where_clause)*)?
        {
            $( if $check { return None; } )+
            let result = unsafe { $self.$unchecked_fn($($param),*) };
            Some(result)
        }
    };
}

#[cfg(feature = "nightly")]
use core::ascii::Char;

/// A stack-allocated array of small strings.
///
/// This is a convenience alias for `StackVec<StackString<N>, CAP>`,
/// useful when you need a fixed-capacity collection of short strings.
///
/// # Examples
///
/// ```
/// use stack_collections::StackArrayString;
///
/// let mut arr: StackArrayString<16, 4> = StackArrayString::new();
///
/// arr.push("hello".try_into().unwrap());
/// arr.push("world".try_into().unwrap());
///
/// assert_eq!(arr.len(), 2);
/// assert_eq!(arr.capacity(), 4);
/// assert_eq!(arr[0].capacity(), 16);
/// assert_eq!(arr[0].as_str(), "hello");
/// assert_eq!(arr[1].as_str(), "world");
/// ```
pub type StackArrayString<const N: usize, const CAP: usize> = StackVec<StackString<N>, CAP>;

/// A UTF-8–encoded, stack-allocated, fixed-capacity string.
pub struct StackString<const N: usize> {
    /// Internal buffer holding up to `N` bytes of UTF-8 text.
    buf: [MaybeUninit<u8>; N],

    /// Current string length (in bytes).
    len: usize,
}

impl<const N: usize> StackString<N> {
    /// Creates a new `StackString<N>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let s = StackString::<32>::new();
    /// assert_eq!(s.len(), 0);
    /// assert_eq!(s.capacity(), 32);
    /// assert!(s.is_empty());
    /// assert!(!s.is_full());
    /// assert_eq!(s.as_str(), "");
    /// ```
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        Self {
            buf: unsafe { MaybeUninit::uninit().assume_init() },
            len: 0,
        }
    }

    /// Returns a raw pointer to the string's buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<8>::new();
    /// s.push_str("hello");
    ///
    /// let ptr = s.as_ptr();
    /// unsafe {
    ///     assert_eq!(*ptr, b'h');
    ///     assert_eq!(*ptr.add(4), b'o');
    /// }
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        self.buf.as_ptr().cast::<u8>()
    }

    /// Returns a mutable raw pointer to the string's buffer.
    ///
    /// # Safety
    ///
    /// It is your responsibility to make sure that the string slice only gets modified in a way that it remains valid UTF-8.
    ///
    /// For safe mutable access, use [`Self::as_mut_str()`] instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<8>::new();
    /// s.push_str("hello");
    ///
    /// let ptr = s.as_mut_ptr();
    /// unsafe {
    ///     // SAFETY: converting 'h' to 'H' maintains UTF-8 validity
    ///     *ptr = b'H';
    /// }
    /// assert_eq!(s.as_str(), "Hello");
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut u8 {
        self.buf.as_mut_ptr().cast::<u8>()
    }

    define_variants! {
        fn pop(&mut self) -> char,

        normal_brief: "Removes and returns the last char",
        try_brief: "Attempts to remove and return the last char",
        unchecked_brief_suffix: "without bound checking",
        checks: {
            self.is_empty() => "string is empty",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: pop_unchecked,
        try_fn: try_pop,
        body: {
            const TAG_CONT_MASK: u8 = 0b1100_0000;
            const TAG_CONT: u8 = 0b1000_0000;

            unsafe {
                let mut pos = self.len - 1;
                let ptr = self.buf.as_ptr().cast::<u8>();

                while pos > 0 && (ptr.add(pos).read() & TAG_CONT_MASK) == TAG_CONT {
                    pos -= 1;
                }

                let first_byte = ptr.add(pos).read();
                let code = match self.len - pos {
                    1 => first_byte as u32,
                    2 => {
                        let b1 = first_byte as u32;
                        let b2 = ptr.add(pos + 1).read() as u32;
                        ((b1 & 0x1F) << 6) | (b2 & 0x3F)
                    }
                    3 => {
                        let b1 = first_byte as u32;
                        let b2 = ptr.add(pos + 1).read() as u32;
                        let b3 = ptr.add(pos + 2).read() as u32;
                        ((b1 & 0x0F) << 12) | ((b2 & 0x3F) << 6) | (b3 & 0x3F)
                    }
                    4 => {
                        let b1 = first_byte as u32;
                        let b2 = ptr.add(pos + 1).read() as u32;
                        let b3 = ptr.add(pos + 2).read() as u32;
                        let b4 = ptr.add(pos + 3).read() as u32;
                        ((b1 & 0x07) << 18) | ((b2 & 0x3F) << 12) | ((b3 & 0x3F) << 6) | (b4 & 0x3F)
                    }
                    _ => unreachable_unchecked(),
                };

                self.len = pos;
                char::from_u32_unchecked(code)
            }
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<8>::new();
                /// s.push_str("abc");
                ///
                /// assert_eq!(s.pop(), 'c');
                /// assert_eq!(s.as_str(), "ab");
                /// assert_eq!(s.len(), 2);
                ///
                /// assert_eq!(s.pop(), 'b');
                /// assert_eq!(s.pop(), 'a');
                /// assert!(s.is_empty());
                /// ```
                ///
                /// Multibyte UTF-8 characters:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<16>::new();
                /// s.push_str("hello😀world");
                ///
                /// assert_eq!(s.pop(), 'd');
                /// assert_eq!(s.pop(), 'l');
                /// assert_eq!(s.pop(), 'r');
                /// assert_eq!(s.pop(), 'o');
                /// assert_eq!(s.pop(), 'w');
                /// assert_eq!(s.pop(), '😀');
                /// assert_eq!(s.as_str(), "hello");
                /// ```
                ///
                /// A panic if the string is empty:
                ///
                ///```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<8>::new();
                ///
                /// // this will panic at runtime
                /// s.pop();
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<8>::new();
                /// assert!(s.try_pop().is_none());
                ///
                /// s.push_str("hi");
                /// assert_eq!(s.try_pop(), Some('i'));
                /// assert_eq!(s.try_pop(), Some('h'));
                /// assert_eq!(s.try_pop(), None);
                /// ```
            }
        }
    }

    /// Writes `c` to `dst`
    #[inline(always)]
    const unsafe fn write_char_to_ptr(&mut self, dst: *mut u8, c: char, c_len: usize) {
        const TAG_CONT: u8 = 0b1000_0000;
        const TAG_TWO_B: u8 = 0b1100_0000;
        const TAG_THREE_B: u8 = 0b1110_0000;
        const TAG_FOUR_B: u8 = 0b1111_0000;

        let code = c as u32;

        match c_len {
            1 => {
                unsafe {
                    dst.write(code as u8);
                };
            }
            2 => {
                unsafe {
                    dst.write(TAG_TWO_B | ((code >> 6) as u8));
                    dst.add(1).write(TAG_CONT | ((code & 0x3F) as u8));
                };
            }
            3 => {
                unsafe {
                    dst.write(TAG_THREE_B | ((code >> 12) as u8));
                    dst.add(1).write(TAG_CONT | (((code >> 6) & 0x3F) as u8));
                    dst.add(2).write(TAG_CONT | ((code & 0x3F) as u8));
                };
            }
            _ => {
                unsafe {
                    dst.write(TAG_FOUR_B | ((code >> 18) as u8));
                    dst.add(1).write(TAG_CONT | (((code >> 12) & 0x3F) as u8));
                    dst.add(2).write(TAG_CONT | (((code >> 6) & 0x3F) as u8));
                    dst.add(3).write(TAG_CONT | ((code & 0x3F) as u8));
                };
            }
        }
    }

    // push
    define_variants! {
        fn push(&mut self, c: char) -> (),

        normal_brief: "Appends a char",
        try_brief: "Attempts to append a char",
        unchecked_brief_suffix: "without bound checking",
        checks: {
            self.len() + c.len_utf8() > N => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: push_unchecked,
        try_fn: try_push,

        body: {
            let n = c.len_utf8();
            unsafe {
                let dst = self.buf.as_mut_ptr().add(self.len).cast::<u8>();
                self.write_char_to_ptr(dst, c, n);
            }
            self.len += n;
        },

        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<16>::new();
                /// s.push('a');
                /// s.push('😀');
                /// s.push('z');
                /// assert_eq!(s.as_str(), "a😀z");
                /// assert_eq!(s.len(), 6);
                /// ```
                ///
                /// A panic upon overflow:
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<1>::new();
                /// s.push('a');
                ///
                /// // this will panic at runtime
                /// s.push('b');
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<5>::new();
                /// assert!(s.try_push('a').is_some());
                /// assert_eq!(s.len(), 1);
                /// assert!(s.try_push('😀').is_some());
                /// assert_eq!(s.len(), 5);
                ///
                /// assert!(s.try_push('x').is_none());
                /// assert_eq!(s.as_str(), "a😀");
                /// ```
            }
        }
    }

    // push_ascii
    define_variants! {
        #[cfg(feature = "nightly")]
        #[cfg_attr(docsrs, doc(cfg(feature = "nightly")))]
        fn push_ascii(&mut self, ascii: Char) -> (),

        normal_brief: "Appends an ASCII character",
        try_brief: "Attempts to push an ASCII character",
        unchecked_brief_suffix: "without bound checking",
        checks: {
            self.is_full() => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: push_ascii_unchecked,
        try_fn: try_push_ascii,
        body: {
            unsafe {
                self.buf
                    .as_mut_ptr()
                    .add(self.len)
                    .cast::<u8>()
                    .write(ascii as u8);
            };
            self.len += 1;
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut s = StackString::<16>::new();
                /// s.push_ascii(Char::SmallA);
                /// s.push_ascii(Char::SmallZ);
                /// assert_eq!(s.as_str(), "az");
                /// assert_eq!(s.len(), 2);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut s = StackString::<1>::new();
                /// s.push_ascii(Char::SmallA);
                ///
                /// // this will panic at runtime
                /// s.push_ascii(Char::SmallB);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut s = StackString::<3>::new();
                /// assert!(s.try_push_ascii(Char::SmallA).is_some());
                /// assert_eq!(s.len(), 1);
                ///
                /// assert!(s.try_push_ascii(Char::SmallB).is_some());
                /// assert_eq!(s.len(), 2);
                ///
                /// assert!(s.try_push_ascii(Char::SmallX).is_none());
                /// assert_eq!(s.as_str(), "ab");
                /// ```
            }
        }
    }

    // push_str
    define_variants! {
        fn push_str(&mut self, s: &str) -> (),

        normal_brief: "Appends a `&str`",
        try_brief: "Attempts to append a `&str`",
        unchecked_brief_suffix: "without bound checking",
        checks: {
            self.len + s.len() > N => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: push_str_unchecked,
        try_fn: try_push_str,
        body: {
            let bytes = s.as_bytes();
            unsafe {
                let dst = self.buf.as_mut_ptr().add(self.len).cast::<u8>();
                ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len())
            };
            self.len += bytes.len();
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<32>::new();
                /// s.push_str("hello");
                /// assert_eq!(s.as_str(), "hello");
                /// assert_eq!(s.len(), 5);
                ///
                /// s.push_str(" world");
                /// assert_eq!(s.as_str(), "hello world");
                /// assert_eq!(s.len(), 11);
                ///
                /// s.push_str("");
                /// assert_eq!(s.as_str(), "hello world");
                /// assert_eq!(s.len(), 11);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<4>::new();
                ///
                /// // this will panic at runtime
                /// s.push_str("hello");
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<8>::new();
                /// assert!(s.try_push_str("hello").is_some());
                /// assert_eq!(s.as_str(), "hello");
                ///
                /// assert!(s.try_push_str("world").is_none());
                /// assert_eq!(s.as_str(), "hello");
                ///
                /// assert!(s.try_push_str("!!!").is_some());
                /// assert_eq!(s.as_str(), "hello!!!");
                /// ```
            }
        }
    }

    // insert
    define_variants! {
        fn insert(&mut self, index: usize, c: char) -> (),

        normal_brief: "Inserts a `char` at `index`, shifting all elements after it",
        try_brief: "Attempts to insert a `char` at `index`, shifting all elements after it",
        unchecked_brief_suffix: "without bound or capacity checking",
        checks: {
            index > self.len => "index out of bounds",
            self.len + c.len_utf8() > N => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: insert_unchecked,
        try_fn: try_insert,
        body: {
            let c_len = c.len_utf8();
            unsafe {
                let dst = self.buf.as_mut_ptr().add(index).cast::<u8>();
                ptr::copy(dst, dst.add(c_len), self.len - index);
                self.write_char_to_ptr(dst, c, c_len);
            };

            self.len += c_len;
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<8>::new();
                /// s.push('a');
                /// s.push('c');
                /// assert_eq!(s.as_str(), "ac");
                ///
                /// s.insert(1, 'b');
                /// assert_eq!(s.as_str(), "abc");
                /// assert_eq!(s.len(), 3);
                ///
                /// s.insert(3, '7');
                /// assert_eq!(s.as_str(), "abc7");
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<8>::new();
                /// s.push('a');
                /// s.push('c');
                /// assert_eq!(s.len(), 2);
                ///
                /// // this will panic at runtime
                /// s.insert(3, 'b');
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<2>::new();
                /// s.push('a');
                /// s.push('c');
                /// assert_eq!(s.len(), 2);
                ///
                /// // this will panic at runtime
                /// s.insert(1, 'b');
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<8>::new();
                ///
                /// s.push_str("abcd");
                /// assert_eq!(s.as_str(), "abcd");
                ///
                /// assert!(s.try_insert(1, 'e').is_some());
                /// assert_eq!(s.as_str(), "aebcd");
                ///
                /// // index out of bounds
                /// assert!(s.try_insert(10, 'x').is_none());
                ///
                /// // would exceed capacity
                /// s.push_str("!!!");
                /// assert!(s.try_insert(0, 'x').is_none());
                /// ```
            }
        }
    }

    // insert_ascii
    define_variants! {
        #[cfg(feature = "nightly")]
        #[cfg_attr(docsrs, doc(cfg(feature = "nightly")))]
        fn insert_ascii(&mut self, index: usize, ascii: Char) -> (),

        normal_brief: "Inserts an ASCII character at `index`, shifting all elements after it",
        try_brief: "Attempts to insert an ASCII character at `index`, shifting all elements after it",
        unchecked_brief_suffix: "without bound or capacity checking",
        checks: {
            index > self.len => "index out of bounds",
            self.is_full() => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: insert_ascii_unchecked,
        try_fn: try_insert_ascii,
        body: {
            unsafe {
                let dst = self.buf.as_mut_ptr().add(index).cast::<u8>();
                ptr::copy(dst, dst.add(1), self.len - index);
                dst.write(ascii as u8);
            }
            self.len += 1;
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut s = StackString::<8>::new();
                /// s.push_ascii(Char::SmallA);
                /// s.push_ascii(Char::SmallC);
                /// assert_eq!(s.as_str(), "ac");
                ///
                /// s.insert_ascii(1, Char::SmallB);
                /// assert_eq!(s.as_str(), "abc");
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut s = StackString::<8>::new();
                /// s.push_ascii(Char::SmallA);
                /// assert_eq!(s.len(), 1);
                ///
                /// // this will panic at runtime
                /// s.insert_ascii(2, Char::SmallB);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut s = StackString::<1>::new();
                /// s.push_ascii(Char::SmallA);
                ///
                /// // this will panic at runtime
                /// s.insert_ascii(0, Char::SmallB);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut s = StackString::<3>::new();
                /// assert!(s.try_insert_ascii(0, Char::SmallA).is_some());
                /// assert_eq!(s.as_str(), "a");
                ///
                /// assert!(s.try_insert_ascii(1, Char::SmallC).is_some());
                /// assert_eq!(s.as_str(), "ac");
                ///
                /// // index out of bounds
                /// assert!(s.try_insert_ascii(10, Char::SmallX).is_none());
                ///
                /// assert!(s.try_insert_ascii(1, Char::SmallB).is_some());
                /// assert_eq!(s.as_str(), "abc");
                ///
                /// // String is full
                /// assert!(s.try_insert_ascii(0, Char::SmallX).is_none());
                /// assert_eq!(s.as_str(), "abc");
                /// ```
            }
        }
    }

    // insert_str
    define_variants! {
        fn insert_str(&mut self, index: usize, s: &str) -> (),

        normal_brief: "Inserts a `&str` at `index`, shifting all elements after it",
        try_brief: "Attempts to insert a `&str` at `index`, shifting all elements after it",
        unchecked_brief_suffix: "without bound or capacity checking",
        checks: {
            index > self.len => "index out of bounds",
            self.len + s.len() > N => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: insert_str_unchecked,
        try_fn: try_insert_str,
        body: {
            let bytes = s.as_bytes();
            unsafe {
                let dst = self.buf.as_mut_ptr().add(index).cast::<u8>();
                ptr::copy(dst, dst.add(bytes.len()), self.len - index);
                ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len());
            }
            self.len += s.len();
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<16>::new();
                /// s.push_str("123");
                /// assert_eq!(s.as_str(), "123");
                ///
                /// s.insert_str(1, "ABC");
                /// assert_eq!(s.as_str(), "1ABC23");
                ///
                /// s.insert_str(5, "DEF");
                /// assert_eq!(s.as_str(), "1ABC2DEF3");
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<8>::new();
                /// s.push_str("hello");
                /// assert_eq!(s.len(), 5);
                ///
                /// // this will panic at runtime
                /// s.insert_str(10, "x");
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<8>::new();
                /// s.push_str("hello");
                /// assert_eq!(s.len(), 5);
                ///
                /// // this will panic at runtime
                /// s.insert_str(0, "world");
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut s = StackString::<12>::new();
                /// s.push_str("hd");
                /// assert_eq!(s.as_str(), "hd");
                ///
                /// assert!(s.try_insert_str(1, "el").is_some());
                /// assert_eq!(s.as_str(), "held");
                ///
                /// assert!(s.try_insert_str(4, " world").is_some());
                /// assert_eq!(s.as_str(), "held world");
                ///
                /// // would exceed capacity
                /// assert!(s.try_insert_str(0, "xxx").is_none());
                /// assert_eq!(s.as_str(), "held world");
                ///
                /// // index out of bounds
                /// assert!(s.try_insert_str(20, "x").is_none());
                /// ```
            }
        }
    }

    /// Truncates the string to the specified byte length.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a UTF-8 character boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<16>::new();
    /// s.push_str("hello");
    /// s.truncate(3);
    /// assert_eq!(s.as_str(), "hel");
    /// assert_eq!(s.len(), 3);
    ///
    /// s.truncate(10);
    /// assert_eq!(s.as_str(), "hel");
    /// ```
    ///
    /// A panic upon invalid UTF-8 character boundary:
    ///
    /// ```should_panic
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<16>::new();
    /// s.push_str("hello😀");
    ///
    /// // this will panic at runtime
    /// s.truncate(6);
    /// ```
    #[inline]
    pub const fn truncate(&mut self, new_len: usize) {
        if new_len >= self.len {
            return;
        }
        assert!(
            self.as_str().is_char_boundary(new_len),
            "truncate not on char boundary"
        );
        self.len = new_len;
    }

    /// Returns the contents as a slice of initialized bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<8>::new();
    /// s.push_str("hello");
    /// assert_eq!(s.as_bytes(), b"hello");
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.buf.as_ptr().cast::<u8>(), self.len) }
    }

    /// Borrow the content as `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<8>::new();
    /// s.push_str("test");
    /// assert_eq!(s.as_str(), "test");
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// Borrow the content as a mutable `str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<16>::new();
    /// s.push_str("hello");
    ///
    /// let mutable_str = s.as_mut_str();
    /// mutable_str.make_ascii_uppercase();
    ///
    /// assert_eq!(s.as_str(), "HELLO");
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_mut_str(&mut self) -> &mut str {
        unsafe {
            str::from_utf8_unchecked_mut(slice::from_raw_parts_mut(
                self.buf.as_mut_ptr().cast::<u8>(),
                self.len,
            ))
        }
    }

    /// Clears the string by setting `len = 0`.
    ///
    /// The underlying memory is not zeroed.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<8>::new();
    /// s.push_str("hello");
    /// assert!(!s.is_empty());
    ///
    /// s.clear();
    /// assert!(s.is_empty());
    /// assert_eq!(s.len(), 0);
    /// assert_eq!(s.as_str(), "");
    /// ```
    #[inline]
    pub const fn clear(&mut self) {
        self.len = 0;
    }

    /// Returns the current length in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<16>::new();
    /// assert_eq!(s.len(), 0);
    /// s.push_str("hello");
    /// assert_eq!(s.len(), 5);
    /// ```
    #[must_use]
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns the capacity in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let s = StackString::<32>::new();
    /// assert_eq!(s.capacity(), 32);
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Returns the remaining capacity in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<10>::new();
    /// assert_eq!(s.remaining_capacity(), 10);
    ///
    /// s.push_str("hello");
    /// assert_eq!(s.remaining_capacity(), 5);
    ///
    /// s.push_str("world");
    /// assert_eq!(s.remaining_capacity(), 0);
    /// assert!(s.is_full());
    /// ```
    #[must_use]
    #[inline]
    pub const fn remaining_capacity(&self) -> usize {
        N - self.len
    }

    /// Returns `true` if the string is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<8>::new();
    /// assert!(s.is_empty());
    /// s.push('a');
    /// assert!(!s.is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns `true` if the string is at full capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut s = StackString::<5>::new();
    /// assert!(!s.is_full());
    /// s.push_str("hello");
    /// assert!(s.is_full());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.len >= N
    }
}

impl<const N: usize> Default for StackString<N> {
    /// Returns a new empty `StackString<N>`.
    ///
    /// This is equivalent to [`Self::new`].
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Deref for StackString<N> {
    type Target = str;

    /// Returns a string slice of the `StackString`.
    ///
    /// This is equivalent to [`Self::as_str`].
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> DerefMut for StackString<N> {
    /// Returns a mutable string slice of the `StackString`.
    ///
    /// This is equivalent to [`Self::as_mut_str`].
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_str()
    }
}

impl<const N: usize> AsRef<str> for StackString<N> {
    /// Returns a string slice to the `StackString`.
    ///
    /// This is equivalent to [`Self::as_str`].
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> AsMut<str> for StackString<N> {
    /// Borrow the content as a mutable `str`.
    ///
    /// This is equivalent to [`Self::as_mut_str`].
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> fmt::Debug for StackString<N> {
    /// Formats the `StackString` with quotes, like a normal string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let s: StackString<16> = "test".try_into().unwrap();
    /// assert_eq!(format!("{:?}", s), "\"test\"");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<const N: usize> fmt::Display for StackString<N> {
    /// Formats the `StackString` without quotes, like a normal string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let s: StackString<16> = "test".try_into().unwrap();
    /// assert_eq!(format!("{}", s), "test");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<const N: usize> PartialEq for StackString<N> {
    /// Compares two `StackString`s for equality.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let s1: StackString<16> = "test".try_into().unwrap();
    /// let s2: StackString<16> = "test".try_into().unwrap();
    /// let s3: StackString<16> = "other".try_into().unwrap();
    ///
    /// assert_eq!(s1, s2);
    /// assert_ne!(s1, s3);
    /// assert_eq!(s1, "test");
    /// assert_eq!(&s1, &"test");
    /// ```
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<const N: usize> PartialEq<str> for StackString<N> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl<const N: usize> PartialEq<&str> for StackString<N> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl<const N: usize> Eq for StackString<N> {}

impl<const N: usize> PartialOrd for StackString<N> {
    /// Performs lexicographic ordering on `StackString`s, same as `str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let s1: StackString<8> = "abc".try_into().unwrap();
    /// let s2: StackString<8> = "abd".try_into().unwrap();
    /// let s3: StackString<8> = "abc".try_into().unwrap();
    ///
    /// assert!(s1 < s2);
    /// assert!(s2 > s1);
    /// assert!(s1 <= s3);
    /// assert!(s1 >= s3);
    /// ```
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Ord for StackString<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<const N: usize> Hash for StackString<N> {
    /// Hashes the contents of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use core::hash::{Hash, Hasher};
    ///
    /// // A simple Hasher for testing purposes
    /// struct MyTestHasher {
    ///     hash: u64,
    /// }
    ///
    /// impl Hasher for MyTestHasher {
    ///     fn write(&mut self, bytes: &[u8]) {
    ///         for &byte in bytes {
    ///             self.hash = self.hash.wrapping_add(byte as u64);
    ///         }
    ///     }
    ///     fn finish(&self) -> u64 {
    ///         self.hash
    ///     }
    /// }
    ///
    /// let s1: StackString<16> = "key".try_into().unwrap();
    /// let s2: StackString<16> = "key".try_into().unwrap();
    ///
    /// let mut hasher1 = MyTestHasher { hash: 0 };
    /// let mut hasher2 = MyTestHasher { hash: 0 };
    ///
    /// s1.hash(&mut hasher1);
    /// s2.hash(&mut hasher2);
    ///
    /// assert_eq!(hasher1.finish(), hasher2.finish());
    /// ```
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl<const N: usize> TryFrom<&str> for StackString<N> {
    type Error = &'static str;

    /// Attempts to create a `StackString` from a string slice.
    ///
    /// Returns an error if the input string exceeds the buffer capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use core::convert::TryFrom;
    ///
    /// let s: StackString<16> = "hello".try_into().unwrap();
    /// assert_eq!(s.as_str(), "hello");
    ///
    /// // Fails if the string is too long for the buffer
    /// let result: Result<StackString<4>, _> = "hello".try_into();
    /// assert!(result.is_err());
    /// ```
    #[inline]
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        if s.len() > N {
            return Err("buffer capacity exceeded");
        }
        let mut out = StackString::new();
        unsafe { out.push_str_unchecked(s) };
        Ok(out)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<const N: usize> From<StackString<N>> for String {
    /// Converts a `StackString` into a `String`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let s: StackString<16> = "hello".try_into().unwrap();
    /// let string: String = s.into();
    ///
    /// assert_eq!(string, "hello");
    /// ```
    fn from(value: StackString<N>) -> Self {
        value.as_str().to_owned()
    }
}

impl<const N: usize> Clone for StackString<N> {
    /// Creates a copy of the `StackString`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let s1: StackString<16> = "hello".try_into().unwrap();
    /// let s2 = s1.clone();
    ///
    /// assert_eq!(s1, s2);
    /// assert_eq!(s1.as_str(), s2.as_str());
    /// ```
    #[inline]
    fn clone(&self) -> Self {
        let mut out = StackString::new();
        unsafe { out.push_str_unchecked(self.as_str()) };
        out
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<const N: usize> Write for StackString<N> {
    /// Writes a buffer into the `StackString`.
    ///
    /// Returns the number of bytes written. Per the `Write` trait contract:
    /// - Returns `Ok(0)` if the buffer is full or input is empty.
    /// - Returns `Ok(n)` where `n <= buf.len()` for partial writes.
    /// - Only returns `Err` if the input would create invalid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use std::io::Write;
    ///
    /// let mut s = StackString::<16>::new();
    /// assert_eq!(s.write(b"Hello").unwrap(), 5);
    /// assert_eq!(s.write(b" world!").unwrap(), 7);
    /// assert_eq!(s.as_str(), "Hello world!");
    /// ```
    ///
    /// Partial writes:
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use std::io::Write;
    ///
    /// let mut s = StackString::<8>::new();
    /// s.push_str("1234");
    ///
    /// let written = s.write(b"567890").unwrap();
    /// assert_eq!(written, 4);
    /// assert_eq!(s.as_str(), "12345678");
    /// ```
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let available = N - self.len;
        if available == 0 || buf.is_empty() {
            return Ok(0);
        }

        let mut to_write = buf.len().min(available);

        // Walk back to avoid splitting UTF-8 sequences
        while to_write > 0 && (buf[to_write - 1] & 0b1100_0000) == 0b1000_0000 {
            to_write -= 1;
        }

        if to_write == 0 {
            return Ok(0);
        }

        // Validate the bytes we're writing
        str::from_utf8(&buf[..to_write])
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "invalid UTF-8"))?;

        unsafe {
            let dst = self.buf.as_mut_ptr().add(self.len).cast::<u8>();
            ptr::copy_nonoverlapping(buf.as_ptr(), dst, to_write);
            self.len += to_write;
        }

        Ok(to_write)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl<const N: usize> fmt::Write for StackString<N> {
    /// Writes a string slice into the `StackString`.
    ///
    /// Returns an error if the string would exceed capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use core::fmt::Write;
    ///
    /// let mut s = StackString::<32>::new();
    /// write!(s, "Hello {}", "world").unwrap();
    /// assert_eq!(s.as_str(), "Hello world");
    /// ```
    ///
    /// Error on overflow:
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use core::fmt::Write;
    ///
    /// let mut s = StackString::<5>::new();
    /// assert!(write!(s, "hello world").is_err());
    /// ```
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.try_push_str(s).ok_or(fmt::Error)
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
        self.try_push(c).ok_or(fmt::Error)
    }
}

/// A stack-allocated vector with a fixed capacity.
pub struct StackVec<T, const CAP: usize> {
    /// The underlying storage for elements, allocated on the stack.
    data: [MaybeUninit<T>; CAP],

    /// The current number of initialized elements in the vector.
    len: usize,
}

impl<T, const CAP: usize> StackVec<T, CAP> {
    /// Creates a new `StackVec<T, CAP>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let v = StackVec::<i32, 8>::new();
    /// assert_eq!(v.len(), 0);
    /// assert_eq!(v.capacity(), 8);
    /// assert!(v.is_empty());
    /// assert!(!v.is_full());
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self {
            data: unsafe { MaybeUninit::uninit().assume_init() },
            len: 0,
        }
    }

    /// Returns a raw pointer to the vector's buffer.
    ///
    /// The pointer is valid for reads of `self.len()` elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// let ptr = v.as_ptr();
    /// unsafe {
    ///     assert_eq!(*ptr, 1);
    ///     assert_eq!(*ptr.add(1), 2);
    ///     assert_eq!(*ptr.add(2), 3);
    /// }
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.data.as_ptr() as *const T
    }

    /// Returns a mutable raw pointer to the vector's buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// unsafe {
    ///     let ptr = v.as_mut_ptr();
    ///     *ptr = 10;
    ///     *ptr.add(2) = 30;
    /// }
    /// assert_eq!(v.as_slice(), &[10, 2, 30]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.data.as_mut_ptr() as *mut T
    }

    // push
    define_variants! {
        fn push(&mut self, value: T) -> (),

        normal_brief: "Appends a value",
        try_brief: "Attempts to append a value",
        unchecked_brief_suffix: "without bound checking",
        checks: {
            self.is_full() => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub},
        },
        unchecked_fn: push_unchecked,
        try_fn: try_push,

        body: {
            unsafe {
                self.data
                    .as_mut_ptr()
                    .add(self.len)
                    .write(MaybeUninit::new(value));
            }
            self.len += 1;
        },

        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.push(1);
                /// v.push(2);
                /// v.push(3);
                ///
                /// assert_eq!(v.len(), 3);
                /// assert_eq!(v[0], 1);
                /// assert_eq!(v[1], 2);
                /// assert_eq!(v[2], 3);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 2>::new();
                /// v.push(1);
                /// v.push(2);
                ///
                /// // this will panic at runtime
                /// v.push(3);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 2>::new();
                /// assert!(v.try_push(1).is_some());
                /// assert!(v.try_push(2).is_some());
                /// assert!(v.try_push(3).is_none());
                ///
                /// assert_eq!(v.len(), 2);
                /// assert_eq!(v[0], 1);
                /// assert_eq!(v[1], 2);
                /// ```
            }
        }
    }

    // insert
    define_variants! {
        fn insert(&mut self, index: usize, element: T) -> (),

        normal_brief: "Inserts an element at position `index`, shifting all elements after it",
        try_brief: "Attempts to insert an element at `index`, shifting all elements after it",
        unchecked_brief_suffix: "without bound or capacity checking",
        checks: {
            index > self.len() => "index out of bounds",
            self.is_full() => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub},
        },

        unchecked_fn: insert_unchecked,
        try_fn: try_insert,

        body: {
            unsafe {
                let p = self.data.as_mut_ptr().add(index) as *mut T;
                ptr::copy(p, p.add(1), self.len - index);
                ptr::write(p, element);
            }
            self.len += 1;
        },

        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.push(1);
                /// v.push(3);
                /// assert_eq!(v.len(), 2);
                ///
                /// v.insert(1, 2);
                /// assert_eq!(v.len(), 3);
                /// assert_eq!(v[0], 1);
                /// assert_eq!(v[1], 2);
                /// assert_eq!(v[2], 3);
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.push(40);
                /// assert_eq!(v.len(), 1);
                ///
                /// // this will panic at runtime
                /// v.insert(2, 10);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 2>::new();
                /// v.push(40);
                /// v.push(50);
                /// assert!(v.is_full());
                ///
                /// // this will panic at runtime
                /// v.insert(1, 19);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 3>::new();
                /// v.push(10);
                /// v.push(20);
                ///
                /// assert_eq!(v.len(), 2);
                ///
                /// // index out of bounds
                /// assert!(v.try_insert(3, 30).is_none());
                ///
                /// assert!(v.try_insert(1, 30).is_some());
                /// assert_eq!(v.len(), 3);
                ///
                /// // vector is full
                /// assert!(v.try_insert(3, 10).is_none());
                /// ```
            }
        }
    }

    // remove
    define_variants! {
        fn remove(&mut self, index: usize) -> T,

        normal_brief: "Removes and returns the element at `index`",
        try_brief: "Attempts to remove and return the element at `index`",
        unchecked_brief_suffix: "without bounds checking",
        checks: {
            index >= self.len() => "index out of bounds",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: remove_unchecked,
        try_fn: try_remove,

        body: {
            unsafe {
                let p = self.data.as_mut_ptr().add(index) as *mut T;
                let result = ptr::read(p);
                ptr::copy(p.add(1), p, self.len - index - 1);
                self.len -= 1;
                result
            }
        },

        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.push(1);
                /// v.push(2);
                /// v.push(3);
                ///
                /// let removed = v.remove(1);
                /// assert_eq!(removed, 2);
                /// assert_eq!(v.len(), 2);
                /// assert_eq!(v[0], 1);
                /// assert_eq!(v[1], 3);
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.push(1);
                ///
                /// // this will panic at runtime
                /// v.remove(1);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.push(10);
                ///
                /// assert_eq!(v.try_remove(0), Some(10));
                /// assert_eq!(v.try_remove(0), None);
                /// ```
            }
        }
    }

    // pop
    define_variants! {
        fn pop(&mut self) -> T,

        normal_brief: "Removes and returns the last element",
        try_brief: "Attempts to remove and return the last element",
        unchecked_brief_suffix: "without bound checking",
        checks: {
            self.is_empty() => "vector is empty",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: pop_unchecked,
        try_fn: try_pop,
        body: {
            self.len -= 1;
            unsafe { self.data.as_ptr().add(self.len).cast::<T>().read() }
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.push(1);
                /// v.push(2);
                /// v.push(3);
                ///
                /// assert_eq!(v.pop(), 3);
                /// assert_eq!(v.len(), 2);
                /// assert_eq!(v.pop(), 2);
                /// assert_eq!(v.pop(), 1);
                /// assert!(v.is_empty());
                /// ```
                ///
                /// A panic if the vector is empty:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                ///
                /// // this will panic at runtime
                /// v.pop();
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// assert_eq!(v.try_pop(), None);
                ///
                /// v.push(42);
                /// assert_eq!(v.try_pop(), Some(42));
                /// assert_eq!(v.try_pop(), None);
                /// ```
            }
        }
    }

    // swap_remove
    define_variants! {
        fn swap_remove(&mut self, index: usize) -> T,

        normal_brief: "Removes and returns the element at `index` without shifting, replacing it with the last element (swap remove)",
        try_brief: "Attempts to remove and return the element at `index` without shifting, replacing it with the last element (swap remove)",
        unchecked_brief_suffix: "without bound checking",
        checks: {
            index >= self.len() => "index out of bounds",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: swap_remove_unchecked,
        try_fn: try_swap_remove,

        body: {
            unsafe {
                let p = self.data.as_mut_ptr().add(index) as *mut T;
                let result = ptr::read(p);
                self.len -= 1;
                if index != self.len {
                    let last = self.data.as_ptr().add(self.len).cast::<T>().read();
                    ptr::write(p, last);
                }
                result
            }
        },

        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.push(1);
                /// v.push(2);
                /// v.push(3);
                /// v.push(4);
                ///
                /// // remove middle element
                /// let removed = v.swap_remove(1);
                /// assert_eq!(removed, 2);
                /// assert_eq!(v.len(), 3);
                /// assert_eq!(v[0], 1);
                /// assert_eq!(v[1], 4);
                /// assert_eq!(v[2], 3);
                ///
                /// // remove last element
                /// let removed_last = v.swap_remove(2);
                /// assert_eq!(removed_last, 3);
                /// assert_eq!(v.len(), 2);
                /// assert_eq!(v[0], 1);
                /// assert_eq!(v[1], 4);
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 4>::new();
                /// v.push(10);
                ///
                /// // this will panic at runtime
                /// v.swap_remove(1);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.extend_from_slice(&[1, 2, 3]);
                ///
                /// assert_eq!(v.try_swap_remove(1), Some(2));
                /// assert_eq!(v.as_slice(), &[1, 3]);
                ///
                /// assert_eq!(v.try_swap_remove(10), None);
                /// ```
            }
        }
    }

    /// Retains only elements that satisfy the predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.extend_from_slice(&[1, 2, 3, 4, 5]);
    ///
    /// v.retain(|x| *x % 2 == 0);
    /// assert_eq!(v.as_slice(), &[2, 4]);
    ///
    /// v.retain(|_| true);
    /// assert_eq!(v.as_slice(), &[2, 4]);
    ///
    /// v.retain(|_| false);
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let mut kept = 0;
        for i in 0..self.len {
            let ptr = unsafe { self.as_mut_ptr().add(i) };
            let elem = unsafe { &mut *ptr };
            if f(elem) {
                if kept != i {
                    unsafe {
                        let dst = self.as_mut_ptr().add(kept);
                        ptr::copy_nonoverlapping(ptr, dst, 1);
                    }
                }
                kept += 1;
            } else {
                unsafe { ptr::drop_in_place(elem) };
            }
        }

        self.len = kept;
    }

    /// Returns a reference to the element at `index`, without bounds checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `index < self.len()`.
    ///
    #[must_use]
    #[inline]
    pub const unsafe fn get_unchecked(&self, index: usize) -> &T {
        unsafe { (&*self.data.as_ptr().add(index)).assume_init_ref() }
    }

    /// Returns a mutable reference to the element at `index`, without bounds checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `index < self.len()`.
    ///
    #[must_use]
    #[inline]
    pub const unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        unsafe { (&mut *self.data.as_mut_ptr().add(index)).assume_init_mut() }
    }

    /// Returns a reference to the element at `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.len()`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.extend_from_slice(&[10, 20, 30]);
    ///
    /// assert_eq!(*v.index(0), 10);
    /// assert_eq!(*v.index(1), 20);
    /// assert_eq!(*v.index(2), 30);
    /// ```
    ///
    /// A panic if the index is out of bounds:
    ///
    /// ```should_panic
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    ///
    /// // this will panic at runtime
    /// v.index(0);
    /// ```
    #[must_use]
    #[inline]
    pub const fn index(&self, index: usize) -> &T {
        self.get(index).expect("index out of bounds")
    }

    /// Returns a mutable reference to the element at `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.len()`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.extend_from_slice(&[10, 20, 30]);
    ///
    /// *v.index_mut(1) = 42;
    /// assert_eq!(v[1], 42);
    /// ```
    ///
    /// A panic if the index is out of bounds:
    ///
    /// ```should_panic
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    ///
    /// // this will panic at runtime
    /// v.index_mut(0);
    /// ```
    #[must_use]
    #[inline]
    pub const fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index).expect("index out of bounds")
    }

    /// Attempts to return a reference to the element at `index`.
    ///
    /// Returns `None` if `index >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(10);
    /// v.push(20);
    /// v.push(30);
    ///
    /// assert_eq!(v.get(0), Some(&10));
    /// assert_eq!(v.get(1), Some(&20));
    /// assert_eq!(v.get(2), Some(&30));
    /// assert_eq!(v.get(3), None);
    /// ```
    #[must_use]
    #[inline]
    pub const fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            None
        } else {
            Some(unsafe { (&*self.data.as_ptr().add(index)).assume_init_ref() })
        }
    }

    /// Attempts to return a mutable reference to the element at `index`.
    ///
    /// Returns `None` if `index >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(10);
    /// v.push(20);
    /// v.push(30);
    ///
    /// if let Some(val) = v.get_mut(1) {
    /// *val = 42;
    /// }
    /// assert_eq!(v[1], 42);
    ///
    /// assert_eq!(v.get_mut(10), None);
    /// ```
    #[must_use]
    #[inline]
    pub const fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.len {
            None
        } else {
            Some(unsafe { (&mut *self.data.as_mut_ptr().add(index)).assume_init_mut() })
        }
    }

    /// Returns the contents as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.extend_from_slice(&[1, 2, 3]);
    /// assert_eq!(v.as_slice(), &[1, 2, 3]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.data.as_ptr() as *const T, self.len) }
    }

    /// Returns the contents as a mutable slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.extend_from_slice(&[1, 2, 3]);
    /// let slice = v.as_mut_slice();
    /// slice[1] = 42;
    /// assert_eq!(v[1], 42);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.data.as_mut_ptr() as *mut T, self.len) }
    }

    /// Returns an iterator over the slice.
    ///
    /// The iterator yields all items from start to end.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;;
    ///
    ///  let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// let sum: i32 = v.iter().sum();
    /// assert_eq!(sum, 6);
    /// ```
    #[inline]
    pub fn iter(&self) -> slice::Iter<'_, T> {
        self.as_slice().iter()
    }

    /// Returns an iterator that allows modifying each value.
    ///
    /// The iterator yields all items from start to end.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;;
    ///
    ///  let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// for x in v.iter_mut() {
    ///     *x *= 2;
    /// }
    /// assert_eq!(v[0], 2);
    /// assert_eq!(v[1], 4);
    /// assert_eq!(v[2], 6);
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, T> {
        self.as_mut_slice().iter_mut()
    }

    define_variants! {
        fn extend_from_slice(&mut self, slice: &[T]) -> (),
        where_clause: { T: Clone }

        normal_brief: "Extends the vector from a slice",
        try_brief: "Attempts to extend the vector from a slice",
        unchecked_brief_suffix: "without capacity checking",
        checks: {
            self.len() + slice.len() > CAP => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub},
            unchecked: {pub},
            try: {pub},
        },
        unchecked_fn: extend_from_slice_unchecked,
        try_fn: try_extend_from_slice,

        body: {
            if size_of::<T>() == 0 || mem::needs_drop::<T>() {
                for item in slice {
                    unsafe {
                        self.push_unchecked(item.clone());
                    }
                }
            } else {
                unsafe {
                    ptr::copy_nonoverlapping(
                        slice.as_ptr(),
                        self.data.as_mut_ptr().cast::<T>().add(self.len),
                        slice.len(),
                    );
                }
                self.len += slice.len();
            }
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 8>::new();
                /// v.push(1);
                /// v.extend_from_slice(&[2, 3, 4]);
                ///
                /// assert_eq!(v.len(), 4);
                /// assert_eq!(v[0], 1);
                /// assert_eq!(v[1], 2);
                /// assert_eq!(v[2], 3);
                /// assert_eq!(v[3], 4);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 4>::new();
                /// v.extend_from_slice(&[1, 2, 3, 4, 5]);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut v = StackVec::<i32, 4>::new();
                /// v.push(1);
                ///
                /// assert!(v.try_extend_from_slice(&[2, 3]).is_some());
                /// assert_eq!(v.len(), 3);
                ///
                /// assert!(v.try_extend_from_slice(&[4, 5]).is_none());
                /// assert_eq!(v.len(), 3);
                /// ```
            }
        }
    }

    /// Drops all initialized elements in the vector without resetting `self.len`.
    #[inline]
    fn drop_elements(&mut self, start: usize) {
        if size_of::<T>() == 0 || mem::needs_drop::<T>() {
            unsafe {
                for i in start..self.len {
                    self.data.get_unchecked_mut(i).assume_init_drop();
                }
            }
        }
    }

    /// Truncates the vector to the specified length.
    ///
    /// Does nothing if `len >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// v.truncate(2);
    /// assert_eq!(v.len(), 2);
    /// assert_eq!(v[0], 1);
    /// assert_eq!(v[1], 2);
    ///
    /// v.truncate(10);
    /// assert_eq!(v.len(), 2);
    /// ```
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len > self.len {
            return;
        }
        self.drop_elements(len);
        self.len = len;
    }

    /// Clears the vector, dropping all initialized elements if necessary,
    /// and resets the length to zero.
    ///
    /// For types `T` that implement `Copy` or do not require `Drop`, this is
    /// effectively just setting `len = 0` without running any destructors.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    ///
    /// v.clear();
    /// assert_eq!(v.len(), 0);
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.drop_elements(0);
        self.len = 0;
    }

    /// Returns the current length.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// assert_eq!(v.len(), 0);
    /// v.push(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns the capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let v = StackVec::<i32, 16>::new();
    /// assert_eq!(v.capacity(), 16);
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        CAP
    }

    /// Returns the remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 5>::new();
    /// assert_eq!(v.remaining_capacity(), 5);
    ///
    /// v.push(1);
    /// v.push(2);
    /// assert_eq!(v.remaining_capacity(), 3);
    ///
    /// v.extend_from_slice(&[3, 4, 5]);
    /// assert_eq!(v.remaining_capacity(), 0);
    /// assert!(v.is_full());
    /// ```
    #[must_use]
    #[inline]
    pub const fn remaining_capacity(&self) -> usize {
        CAP - self.len
    }

    /// Returns `true` if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// assert!(v.is_empty());
    /// v.push(1);
    /// assert!(!v.is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns `true` if the vector is at full capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 2>::new();
    /// assert!(!v.is_full());
    /// v.push(1);
    /// v.push(2);
    /// assert!(v.is_full());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.len >= CAP
    }
}

impl<T, const CAP: usize> Default for StackVec<T, CAP> {
    /// Returns a new empty `StackVec<T, CAP>`.
    ///
    /// This is equivalent to [`Self::new`].
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const CAP: usize> Drop for StackVec<T, CAP> {
    /// Drops the `StackVec`, cleaning up all initialized elements.
    ///
    /// This ensures that all elements stored in the vector are properly dropped
    /// when the vector goes out of scope.
    #[inline]
    fn drop(&mut self) {
        self.drop_elements(0);
    }
}

impl<'a, T, const CAP: usize> IntoIterator for &'a StackVec<T, CAP> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    /// Converts the `StackVec` into an owning iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// let collected: Vec<_> = v.into_iter().collect();
    /// assert_eq!(collected, vec![1, 2, 3]);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, const CAP: usize> IntoIterator for &'a mut StackVec<T, CAP> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    /// Converts the `StackVec` into a mutable iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// for x in &mut v {
    ///     *x *= 2;
    /// }
    ///
    /// let collected: Vec<_> = v.iter().copied().collect();
    /// assert_eq!(collected, vec![2, 4, 6]);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// Owning iterator for StackVec: supports double-ended iteration and is exact-size.
pub struct IntoIter<T, const CAP: usize> {
    /// The current front index of the iterator.
    start: usize,

    /// The current back index of the iterator.
    end: usize,

    /// The owned vector being iterated.
    v: StackVec<T, CAP>,
}

impl<T, const CAP: usize> Iterator for IntoIter<T, CAP> {
    type Item = T;

    /// Returns the next element in the iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// let mut iter = v.into_iter();
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    fn next(&mut self) -> Option<T> {
        if self.start < self.end {
            let idx = self.start;
            self.start += 1;
            // take ownership of element
            Some(unsafe { self.v.data.get_unchecked(idx).assume_init_read() })
        } else {
            None
        }
    }

    /// Returns the remaining number of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.extend_from_slice(&[1, 2, 3, 4, 5]);
    ///
    /// let mut iter = v.into_iter();
    /// assert_eq!(iter.size_hint(), (5, Some(5)));
    /// iter.next();
    /// assert_eq!(iter.size_hint(), (4, Some(4)));
    /// iter.next_back();
    /// assert_eq!(iter.size_hint(), (3, Some(3)));
    /// ```
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.end - self.start;
        (rem, Some(rem))
    }
}

impl<T, const CAP: usize> DoubleEndedIterator for IntoIter<T, CAP> {
    /// Returns the next element from the back of the iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// let mut iter = v.into_iter();
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next_back(), Some(3));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        if self.start < self.end {
            self.end -= 1;
            let idx = self.end;
            Some(unsafe { self.v.data.get_unchecked(idx).assume_init_read() })
        } else {
            None
        }
    }
}

impl<T, const CAP: usize> ExactSizeIterator for IntoIter<T, CAP> {}

impl<T, const CAP: usize> Drop for IntoIter<T, CAP> {
    /// Drops the iterator, cleaning up any remaining unyielded elements.
    ///
    /// This ensures that elements not consumed by the iterator are properly dropped.
    #[inline]
    fn drop(&mut self) {
        // Drop any remaining elements that weren't yielded.
        unsafe {
            for i in self.start..self.end {
                self.v.data.get_unchecked_mut(i).assume_init_drop();
            }
            // Prevent the StackVec::Drop from trying to drop them again.
            self.v.len = 0;
        }
    }
}

impl<T, const CAP: usize> IntoIterator for StackVec<T, CAP> {
    type Item = T;
    type IntoIter = IntoIter<T, CAP>;

    /// Converts the `StackVec` into an owning iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    ///
    /// let collected: Vec<_> = v.into_iter().collect();
    /// assert_eq!(collected, vec![1, 2, 3]);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len;
        IntoIter {
            start: 0,
            end: len,
            v: self,
        }
    }
}

impl<T, const CAP: usize> Deref for StackVec<T, CAP> {
    type Target = [T];

    /// Returns a slice reference to the `StackVec`.
    ///
    /// This is equivalent to [`Self::as_slice`].
    ///
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const CAP: usize> DerefMut for StackVec<T, CAP> {
    /// Returns a mutable slice reference to the `StackVec`.
    ///
    /// This is equivalent to [`Self::as_mut_slice`].
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T, const CAP: usize> AsRef<[T]> for StackVec<T, CAP> {
    /// Returns a reference to the `StackVec` as a slice.
    ///
    /// This is equivalent to [`Self::as_slice`].
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const CAP: usize> AsMut<[T]> for StackVec<T, CAP> {
    /// Returns a mutable slice reference to the `StackVec`.
    ///
    /// This is equivalent to [`Self::as_mut_slice`].
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        &mut *self
    }
}

impl<T: fmt::Debug, const CAP: usize> fmt::Debug for StackVec<T, CAP> {
    /// Formats the `StackVec` using the `Debug` trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.extend_from_slice(&[1, 2, 3]);
    ///
    /// assert_eq!(format!("{:?}", v), "[1, 2, 3]");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: PartialEq, const CAP: usize> PartialEq for StackVec<T, CAP> {
    /// Checks if two `StackVec`s are equal element by element.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let v1: StackVec<i32, 8> = [1, 2, 3].iter().copied().collect();
    /// let v2: StackVec<i32, 8> = [1, 2, 3].iter().copied().collect();
    /// let v3: StackVec<i32, 8> = [1, 2, 4].iter().copied().collect();
    ///
    /// assert_eq!(v1, v2);
    /// assert_ne!(v1, v3);
    /// ```
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T: Eq, const CAP: usize> Eq for StackVec<T, CAP> {}

impl<T: PartialOrd, const CAP: usize> PartialOrd for StackVec<T, CAP> {
    /// Performs lexicographic ordering on `StackVec`s, same as slices (`[T]`).
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let v1: StackVec<i32, 8> = [1, 2, 3].iter().copied().collect();
    /// let v2: StackVec<i32, 8> = [1, 2, 4].iter().copied().collect();
    /// let v3: StackVec<i32, 8> = [1, 2, 3].iter().copied().collect();
    ///
    /// assert!(v1 < v2);
    /// assert!(v2 > v1);
    /// assert!(v1 <= v3);
    /// assert!(v1 >= v3);
    /// ```
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: Ord, const CAP: usize> Ord for StackVec<T, CAP> {
    /// Compares two `StackVec`s lexicographically.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let v1: StackVec<i32, 8> = [1, 2, 3].iter().copied().collect();
    /// let v2: StackVec<i32, 8> = [1, 2, 4].iter().copied().collect();
    ///
    /// assert!(v1 < v2);
    /// assert!(v2 > v1);
    /// assert!(v1 <= v1.clone());
    /// assert!(v1 >= v1.clone());
    /// ```
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: Hash, const CAP: usize> Hash for StackVec<T, CAP> {
    /// Hashes the contents of the `StackVec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    /// use core::hash::{Hash, Hasher};
    ///
    /// // simple no_std hasher
    /// struct MyTestHasher {
    ///     hash: u64,
    /// }
    ///
    /// impl Hasher for MyTestHasher {
    ///     fn write(&mut self, bytes: &[u8]) {
    ///         for &byte in bytes {
    ///             self.hash = self.hash.wrapping_add(byte as u64);
    ///         }
    ///     }
    ///     fn finish(&self) -> u64 {
    ///         self.hash
    ///     }
    /// }
    ///
    /// let v1: StackVec<i32, 8> = [1, 2, 3].iter().copied().collect();
    /// let v2: StackVec<i32, 8> = [1, 2, 3].iter().copied().collect();
    ///
    /// let mut hasher1 = MyTestHasher { hash: 0 };
    /// let mut hasher2 = MyTestHasher { hash: 0 };
    ///
    /// v1.hash(&mut hasher1);
    /// v2.hash(&mut hasher2);
    ///
    /// assert_eq!(hasher1.finish(), hasher2.finish());
    /// ```
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: Clone, const CAP: usize> Clone for StackVec<T, CAP> {
    /// Creates a copy of the `StackVec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let v1: StackVec<i32, 8> = [1, 2, 3].iter().copied().collect();
    /// let v2 = v1.clone();
    ///
    /// assert_eq!(v1, v2);
    ///
    /// // works for zero-sized types as well
    /// let mut v3 = StackVec::<(), 8>::new();
    /// v3.push(());
    /// v3.push(());
    /// v3.push(());
    ///
    /// let v4 = v3.clone();
    /// assert_eq!(v4.len(), 3);
    /// ```
    #[inline]
    fn clone(&self) -> Self {
        let mut out = Self::new();
        if size_of::<T>() == 0 || mem::needs_drop::<T>() {
            for item in self.iter() {
                unsafe { out.push_unchecked(item.clone()) }
            }
        } else {
            let dst = out.data.as_mut_ptr() as *mut T;
            let src = self.data.as_ptr() as *const T;
            unsafe {
                ptr::copy_nonoverlapping(src, dst, self.len);
            }
            out.len = self.len;
        }
        out
    }
}

impl<T: Clone, const CAP: usize> TryFrom<&[T]> for StackVec<T, CAP> {
    type Error = &'static str;

    /// Attempts to create a `StackVec` from a slice.
    ///
    /// Returns an error if the slice length exceeds the stack capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let v = StackVec::<i32, 8>::try_from(&[1, 2, 3][..]).unwrap();
    /// assert_eq!(v.len(), 3);
    /// assert_eq!(v[0], 1);
    /// assert_eq!(v[1], 2);
    /// assert_eq!(v[2], 3);
    ///
    /// let result = StackVec::<i32, 2>::try_from(&[1, 2, 3][..]);
    /// assert!(result.is_err());
    /// ```
    fn try_from(slice: &[T]) -> Result<Self, Self::Error> {
        if slice.len() > CAP {
            return Err("value length exceeds capacity");
        }

        let mut v = Self::new();

        unsafe {
            if size_of::<T>() == 0 || mem::needs_drop::<T>() {
                for item in slice {
                    v.push_unchecked(item.clone());
                }
            } else {
                ptr::copy_nonoverlapping(
                    slice.as_ptr(),
                    v.data.as_mut_ptr() as *mut T,
                    slice.len(),
                );
                v.len = slice.len();
            }
        }

        Ok(v)
    }
}

impl<T, const CAP: usize> FromIterator<T> for StackVec<T, CAP> {
    /// Creates a `StackVec` from an iterator.
    ///
    /// # Panics
    ///
    /// Panics if the iterator produces more than `CAP` elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let v: StackVec<i32, 8> = [1, 2, 3].iter().copied().collect();
    /// assert_eq!(v.len(), 3);
    /// assert_eq!(v[0], 1);
    /// ```
    ///
    /// A panic upon overflow
    /// ```should_panic
    /// use stack_collections::StackVec;
    ///
    /// // this will panic at runtime
    /// let v: StackVec<i32, 2> = [1, 2, 3].iter().copied().collect();
    /// ```
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut v = Self::new();
        for item in iter {
            assert!(v.len < CAP, "buffer capacity exceeded in FromIterator");
            unsafe { v.push_unchecked(item) }
        }
        v
    }
}

impl<T, const CAP: usize> Extend<T> for StackVec<T, CAP> {
    /// Extends the `StackVec` with elements from an iterator.
    ///
    /// # Panics
    ///
    /// Panics if adding all elements would exceed capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 8>::new();
    /// v.push(1);
    /// v.extend([2, 3, 4].iter().copied());
    /// assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
    /// ```
    ///
    /// Extending zero-sized types:
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<(), 8>::new();
    /// v.extend_from_slice(&[(), (), ()]);
    /// assert_eq!(v.len(), 3);
    /// ```
    ///
    /// A panic upon overflow:
    ///
    /// ```should_panic
    /// use stack_collections::StackVec;
    ///
    /// let mut v = StackVec::<i32, 3>::new();
    ///
    /// // this will panic at runtime
    /// v.extend([1, 2, 3, 4].iter().copied());
    /// ```
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            assert!(self.len < CAP, "buffer capacity exceeded in extend");
            unsafe { self.push_unchecked(item) }
        }
    }
}

impl<T, const CAP: usize> Index<usize> for StackVec<T, CAP> {
    type Output = T;

    /// Returns a reference to the element at `index`.
    ///
    /// Equivalent to [`Self::index`].
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.index(index)
    }
}

impl<T, const CAP: usize> IndexMut<usize> for StackVec<T, CAP> {
    /// Returns a mutable reference to the element at `index`.
    ///
    /// Equivalent to [`Self::index_mut`].
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.index_mut(index)
    }
}

#[cfg(test)]
mod tests {
    extern crate alloc;

    use super::*;
    use alloc::sync::Arc;
    use core::sync::atomic::{AtomicUsize, Ordering};

    // StackString tests
    #[test]
    fn test_stack_string_multibyte_boundaries() {
        let mut s = StackString::<20>::new();
        s.push_str("a"); // 1 byte
        s.push('ñ'); // 2 bytes
        s.push('€'); // 3 bytes
        s.push('𝄞'); // 4 bytes

        assert_eq!(s.len(), 10);
        assert_eq!(s.as_str(), "añ€𝄞");

        assert_eq!(s.pop(), '𝄞');
        assert_eq!(s.len(), 6);

        assert_eq!(s.pop(), '€');
        assert_eq!(s.len(), 3);

        assert_eq!(s.pop(), 'ñ');
        assert_eq!(s.len(), 1);
    }

    // StackVec tests
    #[test]
    fn test_stack_vec_insert_at_boundaries() {
        let mut v = StackVec::<i32, 8>::new();

        v.insert(0, 1);
        assert_eq!(v[0], 1);

        v.insert(0, 0);
        assert_eq!(v.as_slice(), &[0, 1]);

        v.insert(2, 2);
        assert_eq!(v.as_slice(), &[0, 1, 2]);
    }

    #[test]
    fn test_stack_vec_retain_with_drops() {
        let counter = Arc::new(AtomicUsize::new(0));

        struct DropCounter(i32, Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.1.fetch_add(1, Ordering::SeqCst);
            }
        }

        let mut v = StackVec::<DropCounter, 8>::new();
        v.push(DropCounter(1, counter.clone()));
        v.push(DropCounter(2, counter.clone()));
        v.push(DropCounter(3, counter.clone()));
        v.push(DropCounter(4, counter.clone()));

        v.retain(|dc| dc.0 % 2 == 0);

        assert_eq!(v.len(), 2);
        assert_eq!(counter.load(Ordering::SeqCst), 2);

        drop(v);
        assert_eq!(counter.load(Ordering::SeqCst), 4);
    }

    #[test]
    fn test_stack_vec_truncate_drop() {
        let counter = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let mut v = StackVec::<DropCounter, 4>::new();
        v.push(DropCounter(counter.clone()));
        v.push(DropCounter(counter.clone()));
        v.push(DropCounter(counter.clone()));

        v.truncate(1);
        assert_eq!(counter.load(Ordering::SeqCst), 2);

        v.clear();
        assert_eq!(counter.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn test_stack_vec_drop() {
        let counter = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        {
            let mut v = StackVec::<DropCounter, 4>::new();
            v.push(DropCounter(counter.clone()));
            v.push(DropCounter(counter.clone()));
            v.push(DropCounter(counter.clone()));
        }

        assert_eq!(counter.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn test_stack_vec_into_iter_partial_drop() {
        let counter = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let mut v = StackVec::<DropCounter, 8>::new();
        v.push(DropCounter(counter.clone()));
        v.push(DropCounter(counter.clone()));
        v.push(DropCounter(counter.clone()));

        let mut iter = v.into_iter();
        iter.next();

        drop(iter);
        assert_eq!(counter.load(Ordering::SeqCst), 3);
    }
}
