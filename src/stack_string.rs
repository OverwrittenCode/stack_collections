use crate::internal::{define_variants, empty_collection};

use core::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    hint::unreachable_unchecked,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr, slice, str,
};

#[cfg(feature = "alloc")]
use alloc::{borrow::ToOwned as _, string::String};
#[cfg(feature = "std")]
use std::io::{self, Write};

#[cfg(feature = "nightly")]
use core::ascii::Char;

/// A UTF-8–encoded, stack-allocated, fixed-capacity string.
pub struct StackString<const N: usize> {
    /// Internal buffer holding up to `N` bytes of UTF-8 text.
    buf: [MaybeUninit<u8>; N],

    /// Current string length (in bytes).
    len: usize,
}

impl<const N: usize> StackString<N> {
    /// Creates a new [`StackString`].
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let stack_string = StackString::<32>::new();
    /// assert_eq!(stack_string.len(), 0);
    /// assert_eq!(stack_string.capacity(), 32);
    /// assert!(stack_string.is_empty());
    /// assert!(!stack_string.is_full());
    /// assert_eq!(stack_string.as_str(), "");
    /// ```
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        empty_collection!()
    }

    /// Returns a raw pointer to the string's buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut stack_string = StackString::<8>::new();
    /// stack_string.push_str("hello");
    ///
    /// let ptr = stack_string.as_ptr();
    /// // SAFETY: ptr points to initialized data at index 0
    /// let first = unsafe { ptr.read() };
    /// assert_eq!(first, b'h');
    ///
    /// // SAFETY: computing pointer offset within bounds (5 bytes)
    /// let ptr_4 = unsafe { ptr.add(4) };
    /// // SAFETY: ptr_4 points to initialized data at index 4
    /// let fifth = unsafe { ptr_4.read() };
    /// assert_eq!(fifth, b'o');
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        self.buf.as_ptr().cast::<u8>()
    }

    /// Returns a mutable raw pointer to the string's buffer.
    ///
    /// Using the pointer may be unsafe if:
    /// - the string slice is modified in a way that it is no longer valid UTF-8
    /// - the length of the string is changed manually without also updating it via [`Self::set_len`]
    ///
    /// For safe mutable access, use [`Self::as_mut_str()`] instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut stack_string = StackString::<8>::new();
    /// stack_string.push_str("hello");
    /// assert_eq!(stack_string.len(), 5);
    ///
    /// // Modify an existing byte
    /// let ptr = stack_string.as_mut_ptr();
    /// // SAFETY: converting 'h' to 'H' maintains UTF-8 validity
    /// unsafe {
    ///     ptr.write(b'H');
    /// }
    /// assert_eq!(stack_string.len(), 5);
    /// assert_eq!(stack_string.as_str(), "Hello");
    ///
    /// // Append new bytes manually
    /// // SAFETY: computing pointer to end of string
    /// let end = unsafe { stack_string.as_mut_ptr().add(stack_string.len()) };
    /// // SAFETY: writing a valid ASCII byte to valid pointer
    /// unsafe {
    ///     end.write(b'!');
    /// }
    /// // SAFETY: we wrote one valid UTF-8 byte
    /// unsafe {
    ///     stack_string.set_len(stack_string.len() + 1);
    /// }
    /// assert_eq!(stack_string.len(), 6);
    /// assert_eq!(stack_string.as_str(), "Hello!");
    /// ```
    ///
    /// *Incorrect* usage:
    ///
    /// ```rust,no_run
    /// use stack_collections::StackString;
    ///
    /// let mut stack_string = StackString::<8>::new();
    /// stack_string.push_str("hello");
    ///
    /// unsafe {
    ///     let ptr = stack_string.as_mut_ptr();
    ///
    ///     // Overwrite the first byte with an invalid UTF-8 start byte
    ///     ptr.write(0xFF); // Undefined Behavior! ⚠️
    ///
    ///     // Append a byte without updating the length
    ///     let end = ptr.add(stack_string.len());
    ///     end.write(b'!'); // Undefined Behavior! ⚠️
    /// }
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut u8 {
        self.buf.as_mut_ptr().cast::<u8>()
    }

    /// Forces the length of the string.
    ///
    /// # Safety
    ///
    /// Calling this function when any of the following conditions are **`true`** is **undefined behavior**:
    /// - `new_len > N`
    /// - `self.buf` up to `new_len` are not all initialized with valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut stack_string = StackString::<8>::new();
    /// let ptr = stack_string.as_mut_ptr();
    ///
    /// // SAFETY: copying valid UTF-8 bytes to valid pointer
    /// unsafe {
    ///     core::ptr::copy_nonoverlapping(b"hello".as_ptr(), ptr, 5);
    /// }
    /// // SAFETY: we wrote 5 bytes of valid UTF-8
    /// unsafe {
    ///     stack_string.set_len(5);
    /// }
    ///
    /// assert_eq!(stack_string.as_str(), "hello");
    /// ```
    #[inline]
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= N, "buffer capacity exceeded");
        debug_assert!(
            str::from_utf8(
                // SAFETY: Creating a slice from initialized buffer up to new_len
                unsafe { slice::from_raw_parts(self.as_ptr(), new_len) }
            )
            .is_ok(),
            "Invalid UTF-8"
        );

        self.len = new_len;
    }

    define_variants! {
        fn pop(self : &mut Self) -> char,

        normal_brief: "Removes and returns the last char",
        try_brief: "Attempts to remove and return the last char",
        unchecked_brief_suffix: "without bound checking",
        ub_conditions: {
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

            let mut pos = self.len - 1;
            let ptr = self.as_ptr();

            while pos > 0 {
                // SAFETY: self.len > pos > 0
                let byte_ptr = unsafe { ptr.add(pos) };
                // SAFETY: byte_ptr points to initialized data
                let byte = unsafe { byte_ptr.read() };
                if (byte & TAG_CONT_MASK) != TAG_CONT {
                    break;
                }
                pos -= 1;
            }

            // SAFETY: pos is now at UTF-8 character boundary
            let first_byte_ptr = unsafe { ptr.add(pos) };
            // SAFETY: reading first byte from valid pointer
            let first_byte = unsafe { first_byte_ptr.read() };
            let code = match self.len - pos {
                1 => first_byte as u32,
                2 => {
                    let b1 = first_byte as u32;
                    // SAFETY: UTF-8 validity guarantees byte 2 exists
                    let b2_ptr = unsafe { ptr.add(pos + 1) };
                    // SAFETY: Reading from valid pointer b2_ptr
                    let b2 = unsafe { b2_ptr.read() } as u32;
                    ((b1 & 0x1F) << 6) | (b2 & 0x3F)
                }
                3 => {
                    let b1 = first_byte as u32;
                    // SAFETY: UTF-8 validity guarantees byte 2 exists
                    let b2_ptr = unsafe { ptr.add(pos + 1) };
                    // SAFETY: Reading from valid pointer b2_ptr
                    let b2 = unsafe { b2_ptr.read() } as u32;
                    // SAFETY: UTF-8 validity guarantees byte 3 exists
                    let b3_ptr = unsafe { ptr.add(pos + 2) };
                    // SAFETY: Reading from valid pointer b3_ptr
                    let b3 = unsafe { b3_ptr.read() } as u32;
                    ((b1 & 0x0F) << 12) | ((b2 & 0x3F) << 6) | (b3 & 0x3F)
                }
                4 => {
                    let b1 = first_byte as u32;
                    // SAFETY: UTF-8 validity guarantees byte 2 exists
                    let b2_ptr = unsafe { ptr.add(pos + 1) };
                    // SAFETY: Reading from valid pointer b2_ptr
                    let b2 = unsafe { b2_ptr.read() } as u32;
                    // SAFETY: UTF-8 validity guarantees byte 3 exists
                    let b3_ptr = unsafe { ptr.add(pos + 2) };
                    // SAFETY: Reading from valid pointer b3_ptr
                    let b3 = unsafe { b3_ptr.read() } as u32;
                    // SAFETY: UTF-8 validity guarantees byte 4 exists
                    let b4_ptr = unsafe { ptr.add(pos + 3) };
                    // SAFETY: Reading from valid pointer b4_ptr
                    let b4 = unsafe { b4_ptr.read() } as u32;
                    ((b1 & 0x07) << 18) | ((b2 & 0x3F) << 12) | ((b3 & 0x3F) << 6) | (b4 & 0x3F)
                }
                // SAFETY: Valid UTF-8 characters are 1-4 bytes
                _ => unsafe { unreachable_unchecked() },
            };

            self.len = pos;
            // SAFETY: code was decoded from valid UTF-8, so it represents a valid char
            unsafe { char::from_u32_unchecked(code) }
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                ///```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<8>::new();
                /// stack_string.push_str("abc");
                ///
                /// assert_eq!(stack_string.pop(), 'c');
                /// assert_eq!(stack_string.as_str(), "ab");
                /// assert_eq!(stack_string.len(), 2);
                ///
                /// assert_eq!(stack_string.pop(), 'b');
                /// assert_eq!(stack_string.pop(), 'a');
                /// assert!(stack_string.is_empty());
                /// ```
                ///
                /// Multibyte UTF-8 characters:
                ///
                ///```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<16>::new();
                /// stack_string.push_str("hello😀world");
                ///
                /// assert_eq!(stack_string.pop(), 'd');
                /// assert_eq!(stack_string.pop(), 'l');
                /// assert_eq!(stack_string.pop(), 'r');
                /// assert_eq!(stack_string.pop(), 'o');
                /// assert_eq!(stack_string.pop(), 'w');
                /// assert_eq!(stack_string.pop(), '😀');
                /// assert_eq!(stack_string.as_str(), "hello");
                /// ```
                ///
                /// A panic if the string is empty:
                ///
                ///```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<8>::new();
                ///
                /// // this will panic at runtime
                /// stack_string.pop();
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<8>::new();
                /// assert!(stack_string.try_pop().is_none());
                ///
                /// stack_string.push_str("hi");
                /// assert_eq!(stack_string.try_pop(), Some('i'));
                /// assert_eq!(stack_string.try_pop(), Some('h'));
                /// assert_eq!(stack_string.try_pop(), None);
                /// ```
            }
        }
    }

    /// Writes `value` to `dst`
    #[expect(
        clippy::cast_possible_truncation,
        reason = "Casting from u32 to u8 is safe here because UTF-8 encoding ensures all written byte values are <= 0xFF"
    )]
    #[inline(always)]
    const unsafe fn write_char_to_ptr(dst: *mut u8, value: char, value_len: usize) {
        const TAG_CONT: u8 = 0b1000_0000;
        const TAG_TWO_B: u8 = 0b1100_0000;
        const TAG_THREE_B: u8 = 0b1110_0000;
        const TAG_FOUR_B: u8 = 0b1111_0000;

        const CONT_MASK: u32 = 0x3F;

        let code = value as u32;

        match value_len {
            1 => {
                // SAFETY: Caller ensures dst has space for 1 byte
                unsafe {
                    dst.write(code as u8);
                }
            }
            2 => {
                // SAFETY: Caller ensures dst has space for byte 0
                unsafe {
                    dst.write(TAG_TWO_B | ((code >> 6_u32) as u8));
                }
                // SAFETY: Caller ensures dst has space for byte 1
                let dst1 = unsafe { dst.add(1) };
                // SAFETY: Writing to valid pointer dst1
                unsafe {
                    dst1.write(TAG_CONT | ((code & CONT_MASK) as u8));
                }
            }
            3 => {
                // SAFETY: Caller ensures dst has space for byte 0
                unsafe {
                    dst.write(TAG_THREE_B | ((code >> 12_u32) as u8));
                }
                // SAFETY: Caller ensures dst has space for byte 1
                let dst1 = unsafe { dst.add(1) };
                // SAFETY: Writing to valid pointer dst1
                unsafe {
                    dst1.write(TAG_CONT | (((code >> 6_u32) & CONT_MASK) as u8));
                }
                // SAFETY: Caller ensures dst has space for byte 2
                let dst2 = unsafe { dst.add(2) };
                // SAFETY: Writing to valid pointer dst2
                unsafe {
                    dst2.write(TAG_CONT | ((code & CONT_MASK) as u8));
                }
            }
            _ => {
                // SAFETY: Caller ensures dst has space for byte 0
                unsafe {
                    dst.write(TAG_FOUR_B | ((code >> 18_u32) as u8));
                }
                // SAFETY: Caller ensures dst has space for byte 1
                let dst1 = unsafe { dst.add(1) };
                // SAFETY: Writing to valid pointer dst1
                unsafe {
                    dst1.write(TAG_CONT | (((code >> 12_u32) & CONT_MASK) as u8));
                }
                // SAFETY: Caller ensures dst has space for byte 2
                let dst2 = unsafe { dst.add(2) };
                // SAFETY: Writing to valid pointer dst2
                unsafe {
                    dst2.write(TAG_CONT | (((code >> 6_u32) & CONT_MASK) as u8));
                }
                // SAFETY: Caller ensures dst has space for byte 3
                let dst3 = unsafe { dst.add(3) };
                // SAFETY: Writing to valid pointer dst3
                unsafe {
                    dst3.write(TAG_CONT | ((code & CONT_MASK) as u8));
                }
            }
        }
    }
    // push
    define_variants! {
        fn push(self: &mut Self, value: char) -> (),

        normal_brief: "Appends a char",
        try_brief: "Attempts to append a char",
        unchecked_brief_suffix: "without bound checking",
        ub_conditions: {
            self.len() + value.len_utf8() > N => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: push_unchecked,
        try_fn: try_push,
        body: {
            let value_len = value.len_utf8();
            // SAFETY: self.len is within bounds N
            let dst = unsafe { self.as_mut_ptr().add(self.len) };
            // SAFETY: Caller guarantees sufficient capacity for value_len bytes
            unsafe {
                Self::write_char_to_ptr(dst, value, value_len);
            }
            self.len += value_len;
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<16>::new();
                /// stack_string.push('a');
                /// stack_string.push('😀');
                /// stack_string.push('z');
                /// assert_eq!(stack_string.as_str(), "a😀z");
                /// assert_eq!(stack_string.len(), 6);
                /// ```
                ///
                /// A panic upon overflow:
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<1>::new();
                /// stack_string.push('a');
                ///
                /// // this will panic at runtime
                /// stack_string.push('b');
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<5>::new();
                /// assert!(stack_string.try_push('a').is_some());
                /// assert_eq!(stack_string.len(), 1);
                /// assert!(stack_string.try_push('😀').is_some());
                /// assert_eq!(stack_string.len(), 5);
                ///
                /// assert!(stack_string.try_push('x').is_none());
                /// assert_eq!(stack_string.as_str(), "a😀");
                /// ```
            }
        }
    }

    // push_ascii
    define_variants! {
        #[cfg(feature = "nightly")]
        #[cfg_attr(docsrs, doc(cfg(feature = "nightly")))]
        fn push_ascii(self: &mut Self, ascii: Char) -> (),

        normal_brief: "Appends an ASCII character",
        try_brief: "Attempts to push an ASCII character",
        unchecked_brief_suffix: "without bound checking",
        ub_conditions: {
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
            // SAFETY: self.len is within bounds and caller guarantees space for 1 more byte
            let dst = unsafe { self.as_mut_ptr().add(self.len) };
            // SAFETY: Writing single ASCII byte to valid pointer
            unsafe {
                dst.write(ascii.to_u8());
            }
            self.len += 1;
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// #![feature(ascii_char)]
                /// #![feature(ascii_char_variants)]
                ///
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut stack_string = StackString::<16>::new();
                /// stack_string.push_ascii(Char::SmallA);
                /// stack_string.push_ascii(Char::SmallZ);
                /// assert_eq!(stack_string.as_str(), "az");
                /// assert_eq!(stack_string.len(), 2);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// #![feature(ascii_char)]
                /// #![feature(ascii_char_variants)]
                ///
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut stack_string = StackString::<1>::new();
                /// stack_string.push_ascii(Char::SmallA);
                ///
                /// // this will panic at runtime
                /// stack_string.push_ascii(Char::SmallB);
                /// ```
            }
            try: {
                /// ```
                /// #![feature(ascii_char)]
                /// #![feature(ascii_char_variants)]
                ///
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut stack_string = StackString::<3>::new();
                /// assert!(stack_string.try_push_ascii(Char::SmallA).is_some());
                /// assert_eq!(stack_string.len(), 1);
                ///
                /// assert!(stack_string.try_push_ascii(Char::SmallB).is_some());
                /// assert_eq!(stack_string.len(), 2);
                ///
                /// assert!(stack_string.try_push_ascii(Char::SmallX).is_none());
                /// assert_eq!(stack_string.as_str(), "ab");
                /// ```
            }
        }
    }

    // push_str
    #[rustfmt::skip]
    define_variants!(
        fn push_str(self: &mut Self, string: &str) -> (),

        normal_brief: "Appends a `str`",
        try_brief: "Attempts to append a `str`",
        unchecked_brief_suffix: "without bound checking",
        ub_conditions: {
            self.len + string.len() > N => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: push_str_unchecked,
        try_fn: try_push_str,
        body: {
            let bytes = string.as_bytes();
            // SAFETY: self.len is within bounds N
            let dst = unsafe { self.as_mut_ptr().add(self.len) };
            // SAFETY: Caller guarantees sufficient capacity; copying valid UTF-8 bytes
            unsafe {
                ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len());
            }
            self.len += bytes.len();
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<32>::new();
                /// stack_string.push_str("hello");
                /// assert_eq!(stack_string.as_str(), "hello");
                /// assert_eq!(stack_string.len(), 5);
                ///
                /// stack_string.push_str(" world");
                /// assert_eq!(stack_string.as_str(), "hello world");
                /// assert_eq!(stack_string.len(), 11);
                ///
                /// stack_string.push_str("");
                /// assert_eq!(stack_string.as_str(), "hello world");
                /// assert_eq!(stack_string.len(), 11);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<4>::new();
                ///
                /// // this will panic at runtime
                /// stack_string.push_str("hello");
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<8>::new();
                /// assert!(stack_string.try_push_str("hello").is_some());
                /// assert_eq!(stack_string.as_str(), "hello");
                ///
                /// assert!(stack_string.try_push_str("world").is_none());
                /// assert_eq!(stack_string.as_str(), "hello");
                ///
                /// assert!(stack_string.try_push_str("!!!").is_some());
                /// assert_eq!(stack_string.as_str(), "hello!!!");
                /// ```
            }
        }
    );

    // insert
    define_variants! {
        fn insert(self: &mut Self, index: usize, value: char) -> (),

        normal_brief: "Inserts a `char` at `index`, shifting all elements after it",
        try_brief: "Attempts to insert a `char` at `index`, shifting all elements after it",
        unchecked_brief_suffix: "without bound or capacity checking",
        ub_conditions: {
            index > self.len => "index out of bounds",
            self.len + value.len_utf8() > N => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: insert_unchecked,
        try_fn: try_insert,
        body: {
            let value_len = value.len_utf8();
            // SAFETY: Caller guarantees index <= self.len
            let dst = unsafe { self.as_mut_ptr().add(index) };
            // SAFETY: Computing destination for shifted elements
            let shifted_dst = unsafe { dst.add(value_len) };
            // SAFETY: Shifting elements right by value_len; ranges don't overlap improperly
            unsafe {
                ptr::copy(dst, shifted_dst, self.len - index);
            }
            // SAFETY: Caller guarantees sufficient capacity for value_len bytes
            unsafe {
                Self::write_char_to_ptr(dst, value, value_len);
            }

            self.len += value_len;
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<8>::new();
                /// stack_string.push('a');
                /// stack_string.push('c');
                /// assert_eq!(stack_string.as_str(), "ac");
                ///
                /// stack_string.insert(1, 'b');
                /// assert_eq!(stack_string.as_str(), "abc");
                /// assert_eq!(stack_string.len(), 3);
                ///
                /// stack_string.insert(3, '7');
                /// assert_eq!(stack_string.as_str(), "abc7");
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<8>::new();
                /// stack_string.push('a');
                /// stack_string.push('c');
                /// assert_eq!(stack_string.len(), 2);
                ///
                /// // this will panic at runtime
                /// stack_string.insert(3, 'b');
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<2>::new();
                /// stack_string.push('a');
                /// stack_string.push('c');
                /// assert_eq!(stack_string.len(), 2);
                ///
                /// // this will panic at runtime
                /// stack_string.insert(1, 'b');
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<8>::new();
                ///
                /// stack_string.push_str("abcd");
                /// assert_eq!(stack_string.as_str(), "abcd");
                ///
                /// assert!(stack_string.try_insert(1, 'e').is_some());
                /// assert_eq!(stack_string.as_str(), "aebcd");
                ///
                /// // index out of bounds
                /// assert!(stack_string.try_insert(10, 'x').is_none());
                ///
                /// // would exceed capacity
                /// stack_string.push_str("!!!");
                /// assert!(stack_string.try_insert(0, 'x').is_none());
                /// ```
            }
        }
    }

    // insert_ascii
    define_variants! {
        #[cfg(feature = "nightly")]
        #[cfg_attr(docsrs, doc(cfg(feature = "nightly")))]
        fn insert_ascii(self: &mut Self, index: usize, ascii: Char) -> (),

        normal_brief: "Inserts an ASCII character at `index`, shifting all elements after it",
        try_brief: "Attempts to insert an ASCII character at `index`, shifting all elements after it",
        unchecked_brief_suffix: "without bound or capacity checking",
        ub_conditions: {
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
            // SAFETY: Caller guarantees index <= self.len
            let dst = unsafe { self.as_mut_ptr().add(index) };
            // SAFETY: Computing destination for shifted elements
            let shifted_dst = unsafe { dst.add(1) };
            // SAFETY: Shifting elements right by 1; dst and dst+1 ranges are valid
            unsafe {
                ptr::copy(dst, shifted_dst, self.len - index);
            }
            // SAFETY: Writing single ASCII byte to valid pointer
            unsafe {
                dst.write(ascii.to_u8());
            }
            self.len += 1;
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// #![feature(ascii_char)]
                /// #![feature(ascii_char_variants)]
                ///
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut stack_string = StackString::<8>::new();
                /// stack_string.push_ascii(Char::SmallA);
                /// stack_string.push_ascii(Char::SmallC);
                /// assert_eq!(stack_string.as_str(), "ac");
                ///
                /// stack_string.insert_ascii(1, Char::SmallB);
                /// assert_eq!(stack_string.as_str(), "abc");
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// #![feature(ascii_char)]
                /// #![feature(ascii_char_variants)]
                ///
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut stack_string = StackString::<8>::new();
                /// stack_string.push_ascii(Char::SmallA);
                /// assert_eq!(stack_string.len(), 1);
                ///
                /// // this will panic at runtime
                /// stack_string.insert_ascii(2, Char::SmallB);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// #![feature(ascii_char)]
                /// #![feature(ascii_char_variants)]
                ///
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut stack_string = StackString::<1>::new();
                /// stack_string.push_ascii(Char::SmallA);
                ///
                /// // this will panic at runtime
                /// stack_string.insert_ascii(0, Char::SmallB);
                /// ```
            }
            try: {
                /// ```
                /// #![feature(ascii_char)]
                /// #![feature(ascii_char_variants)]
                ///
                /// use stack_collections::StackString;
                /// use core::ascii::Char;
                ///
                /// let mut stack_string = StackString::<3>::new();
                /// assert!(stack_string.try_insert_ascii(0, Char::SmallA).is_some());
                /// assert_eq!(stack_string.as_str(), "a");
                ///
                /// assert!(stack_string.try_insert_ascii(1, Char::SmallC).is_some());
                /// assert_eq!(stack_string.as_str(), "ac");
                ///
                /// // index out of bounds
                /// assert!(stack_string.try_insert_ascii(10, Char::SmallX).is_none());
                ///
                /// assert!(stack_string.try_insert_ascii(1, Char::SmallB).is_some());
                /// assert_eq!(stack_string.as_str(), "abc");
                ///
                /// // String is full
                /// assert!(stack_string.try_insert_ascii(0, Char::SmallX).is_none());
                /// assert_eq!(stack_string.as_str(), "abc");
                /// ```
            }
        }
    }

    // insert_str
    define_variants! {
        fn insert_str(self: &mut Self, index: usize, string: &str) -> (),

        normal_brief: "Inserts a `str` at `index`, shifting all elements after it",
        try_brief: "Attempts to insert a `str` at `index`, shifting all elements after it",
        unchecked_brief_suffix: "without bound or capacity checking",
        ub_conditions: {
            index > self.len => "index out of bounds",
            self.len + string.len() > N => "buffer capacity exceeded",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: insert_str_unchecked,
        try_fn: try_insert_str,
        body: {
            let bytes = string.as_bytes();
            // SAFETY: Caller guarantees index <= self.len
            let index_ptr = unsafe { self.as_mut_ptr().add(index) };

            // SAFETY: Caller guarantees self.len + string.len() <= N
            let dst = unsafe { index_ptr.add(bytes.len()) };
            // SAFETY: Shifting elements right; ranges are valid
            unsafe {
                ptr::copy(index_ptr, dst, self.len - index);
            }

            // SAFETY: Copying valid UTF-8 bytes; caller guarantees sufficient capacity
            unsafe {
                ptr::copy_nonoverlapping(bytes.as_ptr(), index_ptr, bytes.len());
            }
            self.len += string.len();
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<16>::new();
                /// stack_string.push_str("123");
                /// assert_eq!(stack_string.as_str(), "123");
                ///
                /// stack_string.insert_str(1, "ABC");
                /// assert_eq!(stack_string.as_str(), "1ABC23");
                ///
                /// stack_string.insert_str(5, "DEF");
                /// assert_eq!(stack_string.as_str(), "1ABC2DEF3");
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<8>::new();
                /// stack_string.push_str("hello");
                /// assert_eq!(stack_string.len(), 5);
                ///
                /// // this will panic at runtime
                /// stack_string.insert_str(10, "x");
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<8>::new();
                /// stack_string.push_str("hello");
                /// assert_eq!(stack_string.len(), 5);
                ///
                /// // this will panic at runtime
                /// stack_string.insert_str(0, "world");
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackString;
                ///
                /// let mut stack_string = StackString::<12>::new();
                /// stack_string.push_str("hd");
                /// assert_eq!(stack_string.as_str(), "hd");
                ///
                /// assert!(stack_string.try_insert_str(1, "el").is_some());
                /// assert_eq!(stack_string.as_str(), "held");
                ///
                /// assert!(stack_string.try_insert_str(4, " world").is_some());
                /// assert_eq!(stack_string.as_str(), "held world");
                ///
                /// // would exceed capacity
                /// assert!(stack_string.try_insert_str(0, "xxx").is_none());
                /// assert_eq!(stack_string.as_str(), "held world");
                ///
                /// // index out of bounds
                /// assert!(stack_string.try_insert_str(20, "x").is_none());
                /// ```
            }
        }
    }

    /// Truncates the string to the specified byte length.
    ///
    /// # Panics
    ///
    /// A panic if `new_len` does not lie on a UTF-8 character boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut stack_string = StackString::<16>::new();
    /// stack_string.push_str("hello");
    /// stack_string.truncate(3);
    /// assert_eq!(stack_string.as_str(), "hel");
    /// assert_eq!(stack_string.len(), 3);
    ///
    /// stack_string.truncate(10);
    /// assert_eq!(stack_string.as_str(), "hel");
    /// ```
    ///
    /// A panic upon invalid UTF-8 character boundary:
    ///
    /// ```should_panic
    /// use stack_collections::StackString;
    ///
    /// let mut stack_string = StackString::<16>::new();
    /// stack_string.push_str("hello😀");
    ///
    /// // this will panic at runtime
    /// stack_string.truncate(6);
    /// ```
    #[inline]
    pub const fn truncate(&mut self, new_len: usize) {
        if new_len >= self.len {
            return;
        }
        assert!(self.as_str().is_char_boundary(new_len), "truncate not on char boundary");
        self.len = new_len;
    }

    /// Returns the contents as a slice of initialized bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut stack_string = StackString::<8>::new();
    /// stack_string.push_str("hello");
    /// assert_eq!(stack_string.as_bytes(), b"hello");
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        // SAFETY: self.len bytes starting from buf are initialized valid UTF-8
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len) }
    }

    /// Borrow the content as `str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut stack_string = StackString::<8>::new();
    /// stack_string.push_str("test");
    /// assert_eq!(stack_string.as_str(), "test");
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_str(&self) -> &str {
        // SAFETY: self.as_bytes() returns valid UTF-8 by construction
        unsafe { str::from_utf8_unchecked(self.as_bytes()) }
    }
    /// Borrow the content as a mutable `str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let mut stack_string = StackString::<16>::new();
    /// stack_string.push_str("hello");
    ///
    /// let mutable_str = stack_string.as_mut_str();
    /// mutable_str.make_ascii_uppercase();
    ///
    /// assert_eq!(stack_string.as_str(), "HELLO");
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_mut_str(&mut self) -> &mut str {
        // SAFETY: Creating mutable slice of initialized valid UTF-8 bytes
        let slice = unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) };
        // SAFETY: slice contains valid UTF-8 by construction
        unsafe { str::from_utf8_unchecked_mut(slice) }
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
    /// let mut stack_string = StackString::<8>::new();
    /// stack_string.push_str("hello");
    /// assert!(!stack_string.is_empty());
    ///
    /// stack_string.clear();
    /// assert!(stack_string.is_empty());
    /// assert_eq!(stack_string.len(), 0);
    /// assert_eq!(stack_string.as_str(), "");
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
    /// let mut stack_string = StackString::<16>::new();
    /// assert_eq!(stack_string.len(), 0);
    /// stack_string.push_str("hello");
    /// assert_eq!(stack_string.len(), 5);
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
    /// let stack_string = StackString::<32>::new();
    /// assert_eq!(stack_string.capacity(), 32);
    /// ```
    #[expect(clippy::inline_always, reason = "this method is trivial")]
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
    /// let mut stack_string = StackString::<10>::new();
    /// assert_eq!(stack_string.remaining_capacity(), 10);
    ///
    /// stack_string.push_str("hello");
    /// assert_eq!(stack_string.remaining_capacity(), 5);
    ///
    /// stack_string.push_str("world");
    /// assert_eq!(stack_string.remaining_capacity(), 0);
    /// assert!(stack_string.is_full());
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
    /// let mut stack_string = StackString::<8>::new();
    /// assert!(stack_string.is_empty());
    /// stack_string.push('a');
    /// assert!(!stack_string.is_empty());
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
    /// let mut stack_string = StackString::<5>::new();
    /// assert!(!stack_string.is_full());
    /// stack_string.push_str("hello");
    /// assert!(stack_string.is_full());
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

    /// Returns a string slice.
    ///
    /// This is equivalent to [`Self::as_str`].
    #[inline]
    fn deref(&self) -> &Self::Target {
        Self::as_str(self)
    }
}

impl<const N: usize> DerefMut for StackString<N> {
    /// Returns a mutable string slice.
    ///
    /// This is equivalent to [`Self::as_mut_str`].
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        Self::as_mut_str(self)
    }
}

impl<const N: usize> AsRef<str> for StackString<N> {
    /// Returns a string slice.
    ///
    /// This is equivalent to [`Self::as_str`].
    #[inline]
    fn as_ref(&self) -> &str {
        Self::as_str(self)
    }
}

impl<const N: usize> AsMut<str> for StackString<N> {
    /// Borrow the content as a mutable `str`.
    ///
    /// This is equivalent to [`Self::as_mut_str`].
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        Self::as_mut_str(self)
    }
}

impl<const N: usize> fmt::Debug for StackString<N> {
    /// Formats the contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let stack_string: StackString<16> = "test".try_into().unwrap();
    /// assert_eq!(format!("{:?}", stack_string), "\"test\"");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<const N: usize> fmt::Display for StackString<N> {
    /// Formats the contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let stack_string: StackString<16> = "test".try_into().unwrap();
    /// assert_eq!(format!("{}", stack_string), "test");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<const N: usize> PartialEq for StackString<N> {
    /// Compares two strings for equality.
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
    /// Performs lexicographic ordering on the strings.
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
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Ord for StackString<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
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

    /// Attempts to create a [`StackString`] from a `str`.
    ///
    /// Returns an error ("buffer capacity exceeded") if the input string exceeds the buffer capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use core::convert::TryFrom;
    ///
    /// let stack_string: StackString<16> = "hello".try_into().unwrap();
    /// assert_eq!(stack_string.as_str(), "hello");
    ///
    /// // Fails if the string is too long for the buffer
    /// let result: Result<StackString<4>, _> = "hello".try_into();
    /// assert!(result.is_err());
    /// ```
    #[inline]
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        if value.len() > N {
            return Err("buffer capacity exceeded");
        }
        let mut out = Self::new();
        // SAFETY: We just verified value.len() <= N
        unsafe {
            out.push_str_unchecked(value);
        }
        Ok(out)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<const N: usize> From<StackString<N>> for String {
    /// Converts a [`StackString`] into a [`String`].
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackString;
    ///
    /// let stack_string: StackString<16> = "hello".try_into().unwrap();
    /// assert_eq!(String::from(stack_string), "hello");
    /// ```
    #[inline]
    fn from(value: StackString<N>) -> Self {
        value.as_str().to_owned()
    }
}

impl<const N: usize> Clone for StackString<N> {
    /// Creates a copy of the string.
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
        let mut out = Self::new();
        // SAFETY: self.as_str() fits in new buffer with same capacity N
        unsafe {
            out.push_str_unchecked(self.as_str());
        }
        out
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<const N: usize> Write for StackString<N> {
    /// Writes a buffer into the [`StackString`].
    ///
    /// Returns the number of bytes written. Per the [`Write`] trait contract:
    /// - Returns `Ok(0)` if the buffer is full or input is empty.
    /// - Returns `Ok(n)` where `n <= buf.len()` for partial writes.
    /// - Only returns [`Err`] if the input would create invalid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use std::io::Write;
    ///
    /// let mut stack_string = StackString::<16>::new();
    /// assert_eq!(stack_string.write(b"Hello").unwrap(), 5);
    /// assert_eq!(stack_string.write(b" world!").unwrap(), 7);
    /// assert_eq!(stack_string.as_str(), "Hello world!");
    /// ```
    ///
    /// Partial writes:
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use std::io::Write;
    ///
    /// let mut stack_string = StackString::<8>::new();
    /// stack_string.push_str("1234");
    ///
    /// let written = stack_string.write(b"567890").unwrap();
    /// assert_eq!(written, 4);
    /// assert_eq!(stack_string.as_str(), "12345678");
    /// ```
    #[inline]
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
        str::from_utf8(&buf[..to_write]).map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "invalid UTF-8"))?;

        // SAFETY: self.len is within bounds and we have space for to_write bytes
        let dst = unsafe { self.as_mut_ptr().add(self.len) };
        // SAFETY: Copying validated UTF-8 bytes; to_write <= available capacity
        unsafe {
            ptr::copy_nonoverlapping(buf.as_ptr(), dst, to_write);
        }
        self.len += to_write;

        Ok(to_write)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl<const N: usize> fmt::Write for StackString<N> {
    /// Writes a string slice into the buffer.
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
    /// let mut stack_string = StackString::<32>::new();
    /// write!(stack_string, "Hello {}", "world").unwrap();
    /// assert_eq!(stack_string.as_str(), "Hello world");
    /// ```
    ///
    /// Error on overflow:
    ///
    /// ```
    /// use stack_collections::StackString;
    /// use core::fmt::Write;
    ///
    /// let mut stack_string = StackString::<5>::new();
    /// assert!(write!(stack_string, "hello world").is_err());
    /// ```
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.try_push_str(s).ok_or(fmt::Error)
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.try_push(c).ok_or(fmt::Error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multibyte_boundaries() {
        let mut stack_string = StackString::<20>::new();
        stack_string.push_str("a"); // 1 byte
        stack_string.push('\u{f1}');
        stack_string.push('\u{20ac}');
        stack_string.push('\u{1d11e}');

        assert_eq!(stack_string.len(), 10);
        assert_eq!(stack_string.as_str(), "a\u{f1}\u{20ac}\u{1d11e}");

        assert_eq!(stack_string.pop(), '\u{1d11e}');
        assert_eq!(stack_string.len(), 6);

        assert_eq!(stack_string.pop(), '\u{20ac}');
        assert_eq!(stack_string.len(), 3);

        assert_eq!(stack_string.pop(), '\u{f1}');
        assert_eq!(stack_string.len(), 1);
    }
}
