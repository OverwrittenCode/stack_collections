//! `stack_collections`: Stack-allocated collections for Rust
//!
//! Provides [`StackString`], [`StackVec`], and [`StackArrayString`].
//! These are fixed-capacity, stack-allocated collections designed for
//! `no_std` environments, zero heap allocations, predictable memory usage,
//! and deterministic performance.
#![deny(warnings)]
#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![deny(clippy::nursery)]
#![deny(clippy::undocumented_unsafe_blocks)]
#![deny(clippy::multiple_unsafe_ops_per_block)]
#![deny(clippy::semicolon_if_nothing_returned)]
#![deny(clippy::std_instead_of_core)]
#![deny(clippy::std_instead_of_alloc)]
#![deny(clippy::missing_inline_in_public_items)]
#![deny(clippy::return_self_not_must_use)]
#![no_std]
#![cfg_attr(feature = "std", allow(unused))]
#![cfg_attr(feature = "nightly", feature(ascii_char))]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

/// Internal module that are not meant for users to use.
mod internal {
    /// Helper macro for creating an empty collection.
    macro_rules! empty_collection {
        () => {
            Self {
                // SAFETY: An array of MaybeUninit does not require initialization
                buf: unsafe { MaybeUninit::uninit().assume_init() },
                len: 0,
            }
        };
    }

    /// Helper macro to define unchecked, normal, and try variants of a method.
    macro_rules! define_variants {
    (
        $(#[$meta:meta])*
        fn $name:ident($self:ident : $self_ty:ty $(, $param:ident: $param_ty:ty)*) $(-> $ret:ty)?,
        $(where_clause: { $($where_clause:tt)* } )?

        normal_brief: $normal_brief:literal,
        try_brief: $try_brief:literal,
        unchecked_brief_suffix: $unchecked_brief_suffix:literal,
        ub_conditions: {
            $($ub_condition:expr => $error:literal),+ $(,)?
        },
        prefixes: {
            normal: {$($normal_prefix:tt)*},
            unchecked: {$($unchecked_prefix:tt)*},
            try: {$($try_prefix:tt)*},
        },
        unchecked_fn: $unchecked_fn:ident,
        try_fn: $try_fn:ident,
        body:  $body:tt,
        $(examples: {
            normal: { $($ex_normal:tt)* }
            try: { $($ex_try:tt)* }
        })?
    ) => {
        $(#[$meta])*
        #[doc = concat!(" ", $normal_brief, ", ", $unchecked_brief_suffix, ".")]
        ///
        #[doc = concat!(" See also [`Self::", stringify!($name), "`] for the safe version and [`Self::", stringify!($try_fn), "`] for the [`Option`] returning version.")]
        ///
        /// # Safety
        ///
        /// Calling this function when any of the following conditions are **`true`** is **undefined behavior**:
        $( #[doc = concat!(" - `", stringify!($ub_condition), "`")] )+
        #[inline]
        $($unchecked_prefix)* unsafe fn $unchecked_fn($self: $self_ty $(, $param: $param_ty)*) $(-> $ret)?
        $(where $($where_clause)*)?
        {
            $( debug_assert!(!($ub_condition), $error); )+
            $body
        }

        $(#[$meta])*
        #[doc = concat!(" ", $normal_brief, ".")]
        ///
        #[doc = concat!(" See also [`Self::", stringify!($unchecked_fn), "`] for the unchecked version and [`Self::", stringify!($try_fn), "`] for the [`Option`] returning version.")]
        ///
        /// # Panics
        ///
        $( #[doc = concat!(" - \"", $error, "\" if `", stringify!($ub_condition), "`")] )+
        $(
            ///
            /// # Examples
            ///
            $($ex_normal)*
        )?
        #[inline]
        $($normal_prefix)* fn $name($self: $self_ty $(, $param: $param_ty)*) $(-> $ret)?
        $(where $($where_clause)*)?
        {
            $( assert!(!($ub_condition), $error); )+
            // SAFETY: passed all undefined behaviour conditions above
            unsafe { $self.$unchecked_fn($($param),*) }
        }

        $(#[$meta])*
        #[doc = concat!(" ", $try_brief, ".")]
        ///
        #[doc = concat!(" See also [`Self::", stringify!($name), "`] for the panic-on-error version and [`Self::", stringify!($unchecked_fn), "`] for the unchecked version.")]
        ///
        /// Returns [`None`] if any of these conditions are **`false`**:
        $( #[doc = concat!(" - `", stringify!($ub_condition), "`")] )+
        $(
            ///
            /// # Examples
            ///
            $($ex_try)*
        )?
        #[must_use]
        #[inline]
        $($try_prefix)* fn $try_fn($self: $self_ty $(, $param: $param_ty)*) $(-> Option<$ret>)?
        $(where $($where_clause)*)?
        {
            $( if $ub_condition { return None; } )+
            // SAFETY: passed all undefined behaviour conditions above
            let result = unsafe { $self.$unchecked_fn($($param),*) };
            Some(result)
        }
    };
}

    pub(crate) use define_variants;
    pub(crate) use empty_collection;
}

/// A UTF-8–encoded, stack-allocated, fixed-capacity string.
pub mod stack_string;

/// A stack-allocated vector with a fixed capacity.
pub mod stack_vec;

pub use crate::stack_string::StackString;
pub use crate::stack_vec::StackVec;

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
