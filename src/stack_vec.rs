use crate::internal::{define_variants, empty_collection};

use core::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut, Index, IndexMut},
    ptr, slice,
};

/// A stack-allocated vector with a fixed capacity.
pub struct StackVec<T, const CAP: usize> {
    /// The underlying storage for elements, allocated on the stack.
    buf: [MaybeUninit<T>; CAP],

    /// The current number of initialized elements in the vector.
    len: usize,
}

impl<T, const CAP: usize> StackVec<T, CAP> {
    /// Creates a new [`StackVec`].
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let vec = StackVec::<i32, 8>::new();
    /// assert_eq!(vec.len(), 0);
    /// assert_eq!(vec.capacity(), 8);
    /// assert!(vec.is_empty());
    /// assert!(!vec.is_full());
    /// assert_eq!(vec.as_slice(), &[]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        empty_collection!()
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
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let ptr = vec.as_ptr();
    /// // SAFETY: ptr points to initialized element at index 0
    /// let first = unsafe { ptr.read() };
    /// assert_eq!(first, 1);
    ///
    /// // SAFETY: computing pointer offset within bounds (len = 3)
    /// let ptr_1 = unsafe { ptr.add(1) };
    /// // SAFETY: ptr_1 points to initialized element at index 1
    /// let second = unsafe { ptr_1.read() };
    /// assert_eq!(second, 2);
    ///
    /// // SAFETY: computing pointer offset within bounds (len = 3)
    /// let ptr_2 = unsafe { ptr.add(2) };
    /// // SAFETY: ptr_2 points to initialized element at index 2
    /// let third = unsafe { ptr_2.read() };
    /// assert_eq!(third, 3);
    /// ```
    #[expect(clippy::inline_always, reason = "this method is trivial")]
    #[must_use]
    #[inline(always)]
    pub const fn as_ptr(&self) -> *const T {
        self.buf.as_ptr().cast::<T>()
    }

    /// Returns a mutable raw pointer to the vector's buffer.
    ///
    /// Using the pointer may be unsafe if:
    /// - you write to memory beyond the current length without later calling [`Self::set_len`]
    /// - you read from uninitialized elements (i.e. indices >= `self.len()`)
    /// - you overwrite an element and break its invariants (e.g. leaving a partially dropped object)
    ///
    /// For safe mutable access, use [`Self::as_mut_slice`] instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let ptr = vec.as_mut_ptr();
    /// // SAFETY: ptr points to initialized element at index 0
    /// unsafe { ptr.write(10) };
    ///
    /// let ptr = vec.as_mut_ptr();
    /// // SAFETY: computing pointer offset within bounds (len = 3)
    /// let ptr_2 = unsafe { ptr.add(2) };
    /// // SAFETY: ptr_2 points to initialized element at index 2
    /// unsafe { ptr_2.write(30) };
    ///
    /// assert_eq!(vec.as_slice(), &[10, 2, 30]);
    /// ```
    ///
    /// *Incorrect* usage:
    ///
    /// ```rust,no_run
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 4>::new();
    /// vec.push(1);
    ///
    /// unsafe {
    ///     let ptr = vec.as_mut_ptr();
    ///
    ///     // Writing beyond initialized length without updating len
    ///     let out_of_bounds = ptr.add(3); // UB: index 3 is uninitialized
    ///     out_of_bounds.write(99); // Undefined Behavior! ⚠️
    ///
    ///     // Append an element without updating the length
    ///     let untracked = ptr.add(1);
    ///     untracked.write(42); // Undefined Behavior! ⚠️
    ///
    ///     // Overwriting a live element incorrectly (e.g., if it were a Drop type)
    ///     ptr.write(100); // UB if old value had invariants or resources
    /// }
    /// ```
    #[expect(clippy::inline_always, reason = "this method is trivial")]
    #[must_use]
    #[inline(always)]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.buf.as_mut_ptr().cast::<T>()
    }

    /// Forces the length of the vector.
    ///
    /// # Safety
    ///
    /// Calling this function when any of the following conditions are **`true`** is **undefined behavior**:
    /// - `new_len > CAP`
    /// - `self.buf` up to `new_len` are not all initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// let ptr = vec.as_mut_ptr();
    ///
    /// // SAFETY: writing to ptr initializes the first element
    /// unsafe { ptr.write(10) };
    ///
    /// // SAFETY: computing pointer offset within bounds (capacity = 8)
    /// let ptr_1 = unsafe { ptr.add(1) };
    /// // SAFETY: writing to ptr_1 initializes the second element
    /// unsafe { ptr_1.write(20) };
    ///
    /// // SAFETY: computing pointer offset within bounds (capacity = 8)
    /// let ptr_2 = unsafe { ptr.add(2) };
    /// // SAFETY: writing to ptr_2 initializes the third element
    /// unsafe { ptr_2.write(30) };
    ///
    /// // SAFETY: we initialized 3 elements, so it's safe to set len = 3
    /// unsafe { vec.set_len(3) };
    ///
    /// assert_eq!(vec.as_slice(), &[10, 20, 30]);
    /// ```
    #[inline]
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= CAP, "buffer capacity exceeded");
        self.len = new_len;
    }

    // push
    define_variants! {
        fn push(self: &mut Self, value: T) -> (),

        normal_brief: "Appends a value",
        try_brief: "Attempts to append a value",
        unchecked_brief_suffix: "without bound checking",
        ub_conditions: {
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
            // SAFETY: Caller guarantees self.len < CAP
            let dst = unsafe { self.as_mut_ptr().add(self.len) };
            // SAFETY: Writing to valid uninitialized slot
            unsafe {
                dst.write(value);
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
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(1);
                /// vec.push(2);
                /// vec.push(3);
                ///
                /// assert_eq!(vec.len(), 3);
                /// assert_eq!(vec[0], 1);
                /// assert_eq!(vec[1], 2);
                /// assert_eq!(vec[2], 3);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 2>::new();
                /// vec.push(1);
                /// vec.push(2);
                ///
                /// // this will panic at runtime
                /// vec.push(3);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 2>::new();
                /// assert!(vec.try_push(1).is_some());
                /// assert!(vec.try_push(2).is_some());
                /// assert!(vec.try_push(3).is_none());
                ///
                /// assert_eq!(vec.len(), 2);
                /// assert_eq!(vec[0], 1);
                /// assert_eq!(vec[1], 2);
                /// ```
            }
        }
    }

    // insert
    define_variants! {
        fn insert(self: &mut Self, index: usize, element: T) -> (),

        normal_brief: "Inserts an element at position `index`, shifting all elements after it",
        try_brief: "Attempts to insert an element at `index`, shifting all elements after it",
        unchecked_brief_suffix: "without bound or capacity checking",
        ub_conditions: {
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
            // SAFETY: Caller guarantees index <= self.len
            let src = unsafe { self.as_mut_ptr().add(index) };
            // SAFETY: Computing destination for shifted elements
            let shifted_src = unsafe { src.add(1) };
            // SAFETY: Shifting elements right by 1; ranges are valid
            unsafe {
                ptr::copy(src, shifted_src, self.len - index);
            }
            // SAFETY: Writing element to valid position
            unsafe {
                ptr::write(src, element);
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
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(1);
                /// vec.push(3);
                /// assert_eq!(vec.len(), 2);
                ///
                /// vec.insert(1, 2);
                /// assert_eq!(vec.len(), 3);
                /// assert_eq!(vec[0], 1);
                /// assert_eq!(vec[1], 2);
                /// assert_eq!(vec[2], 3);
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(40);
                /// assert_eq!(vec.len(), 1);
                ///
                /// // this will panic at runtime
                /// vec.insert(2, 10);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 2>::new();
                /// vec.push(40);
                /// vec.push(50);
                /// assert!(vec.is_full());
                ///
                /// // this will panic at runtime
                /// vec.insert(1, 19);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 3>::new();
                /// vec.push(10);
                /// vec.push(20);
                ///
                /// assert_eq!(vec.len(), 2);
                ///
                /// // index out of bounds
                /// assert!(vec.try_insert(3, 30).is_none());
                ///
                /// assert!(vec.try_insert(1, 30).is_some());
                /// assert_eq!(vec.len(), 3);
                ///
                /// // vector is full
                /// assert!(vec.try_insert(3, 10).is_none());
                /// ```
            }
        }
    }

    // remove
    define_variants! {
        fn remove(self: &mut Self, index: usize) -> T,

        normal_brief: "Removes and returns the element at `index`",
        try_brief: "Attempts to remove and return the element at `index`",
        unchecked_brief_suffix: "without bounds checking",
        ub_conditions: {
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
            // SAFETY: Caller guarantees index < self.len
            let ptr_to_remove = unsafe { self.as_mut_ptr().add(index) };
            // SAFETY: Reading initialized element at valid index
            let result = unsafe { ptr::read(ptr_to_remove) };
            // SAFETY: Computing source pointer for shift
            let src = unsafe { ptr_to_remove.add(1) };
            // SAFETY: Shifting remaining elements left by 1
            unsafe {
                ptr::copy(src, ptr_to_remove, self.len - index - 1);
            }
            self.len -= 1;
            result
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(1);
                /// vec.push(2);
                /// vec.push(3);
                ///
                /// let removed = vec.remove(1);
                /// assert_eq!(removed, 2);
                /// assert_eq!(vec.len(), 2);
                /// assert_eq!(vec[0], 1);
                /// assert_eq!(vec[1], 3);
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(1);
                ///
                /// // this will panic at runtime
                /// vec.remove(1);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(10);
                ///
                /// assert_eq!(vec.try_remove(0), Some(10));
                /// assert_eq!(vec.try_remove(0), None);
                /// ```
            }
        }
    }

    // pop
    define_variants! {
        fn pop(self: &mut Self) -> T,

        normal_brief: "Removes and returns the last element",
        try_brief: "Attempts to remove and return the last element",
        unchecked_brief_suffix: "without bound checking",
        ub_conditions: {
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
            // SAFETY: self.len was > 0, now points to last initialized element
            let ptr = unsafe { self.as_ptr().add(self.len) };
            // SAFETY: Reading from initialized element
            unsafe { ptr.read() }
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(1);
                /// vec.push(2);
                /// vec.push(3);
                ///
                /// assert_eq!(vec.pop(), 3);
                /// assert_eq!(vec.len(), 2);
                /// assert_eq!(vec.pop(), 2);
                /// assert_eq!(vec.pop(), 1);
                /// assert!(vec.is_empty());
                /// ```
                ///
                /// A panic if the vector is empty:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                ///
                /// // this will panic at runtime
                /// vec.pop();
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// assert_eq!(vec.try_pop(), None);
                ///
                /// vec.push(42);
                /// assert_eq!(vec.try_pop(), Some(42));
                /// assert_eq!(vec.try_pop(), None);
                /// ```
            }
        }
    }

    // swap_remove
    define_variants! {
        fn swap_remove(self: &mut Self, index: usize) -> T,

        normal_brief: "Removes and returns the element at `index` **without** shifting, replacing it with the last element (swap remove)",
        try_brief: "Attempts to remove and return the element at `index` **without** shifting, replacing it with the last element (swap remove)",
        unchecked_brief_suffix: "without bound checking",
        ub_conditions: {
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
            // SAFETY: Caller guarantees index < self.len
            let dst = unsafe { self.as_mut_ptr().add(index) };
            // SAFETY: Reading initialized element at valid index
            let result = unsafe { ptr::read(dst) };
            self.len -= 1;
            if index != self.len {
                // SAFETY: Computing pointer to last element
                let last_ptr = unsafe { self.as_ptr().add(self.len) };
                // SAFETY: Reading last element after decrementing len
                let last = unsafe { last_ptr.read() };
                // SAFETY: Writing to previously read position
                unsafe {
                    ptr::write(dst, last);
                }
            }
            result
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(1);
                /// vec.push(2);
                /// vec.push(3);
                /// vec.push(4);
                ///
                /// // remove middle element
                /// let removed = vec.swap_remove(1);
                /// assert_eq!(removed, 2);
                /// assert_eq!(vec.len(), 3);
                /// assert_eq!(vec[0], 1);
                /// assert_eq!(vec[1], 4);
                /// assert_eq!(vec[2], 3);
                ///
                /// // remove last element
                /// let removed_last = vec.swap_remove(2);
                /// assert_eq!(removed_last, 3);
                /// assert_eq!(vec.len(), 2);
                /// assert_eq!(vec[0], 1);
                /// assert_eq!(vec[1], 4);
                /// ```
                ///
                /// A panic if the index is out of bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 4>::new();
                /// vec.push(10);
                ///
                /// // this will panic at runtime
                /// vec.swap_remove(1);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.extend_from_slice(&[1, 2, 3]);
                ///
                /// assert_eq!(vec.try_swap_remove(1), Some(2));
                /// assert_eq!(vec.as_slice(), &[1, 3]);
                ///
                /// assert_eq!(vec.try_swap_remove(10), None);
                /// ```
            }
        }
    }

    // index
    define_variants! {
        fn index(self: &Self, index: usize) -> &T,

        normal_brief: "Returns a reference to the element at `index`",
        try_brief: "Attempts to return a reference to the element at `index`",
        unchecked_brief_suffix: "without bounds checking",
        ub_conditions: {
            index >= self.len => "index out of bounds",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: get_unchecked,
        try_fn: get,
        body: {
            // SAFETY: Caller guarantees index < self.len
            let ptr = unsafe { self.buf.as_ptr().add(index) };
            // SAFETY: Creating reference to initialized element
            let elem_ref = unsafe { &*ptr };
            // SAFETY: Element at index is initialized
            unsafe { elem_ref.assume_init_ref() }
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.extend_from_slice(&[10, 20, 30]);
                ///
                /// assert_eq!(*vec.index(0), 10);
                /// assert_eq!(*vec.index(1), 20);
                /// assert_eq!(*vec.index(2), 30);
                /// ```
                ///
                /// Panics on out-of-bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                /// let mut vec = StackVec::<i32, 8>::new();
                ///
                /// // this will panic at runtime
                /// vec.index(0);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(10);
                /// vec.push(20);
                /// vec.push(30);
                ///
                /// assert_eq!(vec.get(0), Some(&10));
                /// assert_eq!(vec.get(10), None);
                /// ```
            }
        }
    }

    // index_mut
    define_variants! {
        fn index_mut(self: &mut Self, index: usize) -> &mut T,

        normal_brief: "Returns a mutable reference to the element at `index`",
        try_brief: "Attempts to return a mutable reference to the element at `index`",
        unchecked_brief_suffix: "without bounds checking",
        ub_conditions: {
            index >= self.len => "index out of bounds",
        },
        prefixes: {
            normal: {pub const},
            unchecked: {pub const},
            try: {pub const},
        },
        unchecked_fn: get_unchecked_mut,
        try_fn: get_mut,
        body: {
            // SAFETY: Caller guarantees index < self.len
            let ptr = unsafe { self.buf.as_mut_ptr().add(index) };
            // SAFETY: Creating mutable reference to initialized element
            let elem_ref = unsafe { &mut *ptr };
            // SAFETY: Element at index is initialized
            unsafe { elem_ref.assume_init_mut() }
        },
        examples: {
            normal: {
                /// Basic usage:
                ///
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.extend_from_slice(&[10, 20, 30]);
                ///
                /// *vec.index_mut(1) = 42;
                /// assert_eq!(vec[1], 42);
                /// ```
                ///
                /// Panics on out-of-bounds:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                /// let mut vec = StackVec::<i32, 8>::new();
                ///
                /// // this will panic at runtime
                /// vec.index_mut(0);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(10);
                /// vec.push(20);
                /// vec.push(30);
                ///
                /// if let Some(val) = vec.get_mut(1) {
                ///     *val = 42;
                /// }
                /// assert_eq!(vec[1], 42);
                ///
                /// assert_eq!(vec.get_mut(10), None);
                /// ```
            }
        }
    }

    define_variants! {
        fn extend_from_slice(self: &mut Self, slice: &[T]) -> (),
        where_clause: { T: Clone }

        normal_brief: "Extends the vector from a slice",
        try_brief: "Attempts to extend the vector from a slice",
        unchecked_brief_suffix: "without capacity checking",
        ub_conditions: {
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
                    // SAFETY: Caller guarantees sufficient capacity
                    unsafe {
                        self.push_unchecked(item.clone());
                    }
                }
            } else {
                // SAFETY: Computing destination pointer at end of initialized elements
                let dst = unsafe { self.as_mut_ptr().add(self.len) };
                // SAFETY: Caller guarantees capacity; copying slice.len() elements
                unsafe {
                    ptr::copy_nonoverlapping(slice.as_ptr(), dst, slice.len());
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
                /// let mut vec = StackVec::<i32, 8>::new();
                /// vec.push(1);
                /// vec.extend_from_slice(&[2, 3, 4]);
                ///
                /// assert_eq!(vec.len(), 4);
                /// assert_eq!(vec[0], 1);
                /// assert_eq!(vec[1], 2);
                /// assert_eq!(vec[2], 3);
                /// assert_eq!(vec[3], 4);
                /// ```
                ///
                /// A panic upon overflow:
                ///
                /// ```should_panic
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 4>::new();
                /// vec.extend_from_slice(&[1, 2, 3, 4, 5]);
                /// ```
            }
            try: {
                /// ```
                /// use stack_collections::StackVec;
                ///
                /// let mut vec = StackVec::<i32, 4>::new();
                /// vec.push(1);
                ///
                /// assert!(vec.try_extend_from_slice(&[2, 3]).is_some());
                /// assert_eq!(vec.len(), 3);
                ///
                /// assert!(vec.try_extend_from_slice(&[4, 5]).is_none());
                /// assert_eq!(vec.len(), 3);
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
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.extend_from_slice(&[1, 2, 3, 4, 5]);
    ///
    /// // Keep only numbers greater than 2
    /// vec.retain(|x| *x > 2);
    /// assert_eq!(vec.as_slice(), &[3, 4, 5]);
    ///
    /// // Keep all (no-op)
    /// vec.retain(|_| true);
    /// assert_eq!(vec.as_slice(), &[3, 4, 5]);
    ///
    /// // Remove all
    /// vec.retain(|_| false);
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let mut kept = 0;
        for i in 0..self.len {
            // SAFETY: i < self.len, so this is a valid and initialized element
            let ptr = unsafe { self.as_mut_ptr().add(i) };
            // SAFETY: ptr points to valid initialized element
            let elem = unsafe { &mut *ptr };
            if f(elem) {
                if kept != i {
                    // SAFETY: kept < i < self.len, ranges don't overlap
                    let dst = unsafe { self.as_mut_ptr().add(kept) };
                    // SAFETY: Copying single element from valid source to valid dest
                    unsafe {
                        ptr::copy_nonoverlapping(ptr, dst, 1);
                    }
                }
                kept += 1;
            } else {
                // SAFETY: Dropping initialized element that won't be kept
                unsafe {
                    ptr::drop_in_place(elem);
                }
            }
        }

        self.len = kept;
    }

    /// Returns the contents as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.extend_from_slice(&[1, 2, 3]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        // SAFETY: First self.len elements are initialized
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len) }
    }

    /// Returns the contents as a mutable slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.extend_from_slice(&[1, 2, 3]);
    /// let slice = vec.as_mut_slice();
    /// slice[1] = 42;
    /// assert_eq!(vec[1], 42);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: First self.len elements are initialized
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) }
    }

    /// Returns an iterator over the slice.
    ///
    /// The iterator yields all items from start to end.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    ///  let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let sum: i32 = vec.iter().sum();
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
    /// use stack_collections::StackVec;
    ///
    ///  let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// for x in vec.iter_mut() {
    ///     *x *= 2;
    /// }
    /// assert_eq!(vec[0], 2);
    /// assert_eq!(vec[1], 4);
    /// assert_eq!(vec[2], 6);
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, T> {
        self.as_mut_slice().iter_mut()
    }

    /// Drops all initialized elements in the vector without resetting `self.len`.
    #[inline]
    fn drop_elements(&mut self, start: usize) {
        if size_of::<T>() == 0 || mem::needs_drop::<T>() {
            for i in start..self.len {
                // SAFETY: i < self.len, so element is initialized
                let elem = unsafe { self.buf.get_unchecked_mut(i) };
                // SAFETY: elem points to initialized element
                unsafe {
                    elem.assume_init_drop();
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
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// vec.truncate(2);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(vec[0], 1);
    /// assert_eq!(vec[1], 2);
    ///
    /// vec.truncate(10);
    /// assert_eq!(vec.len(), 2);
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
    /// For types `T` that implement [`Copy`] or do not require [`Drop`], this is
    /// effectively just setting `len = 0` without running any destructors.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    ///
    /// vec.clear();
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.is_empty());
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
    /// let mut vec = StackVec::<i32, 8>::new();
    /// assert_eq!(vec.len(), 0);
    /// vec.push(1);
    /// assert_eq!(vec.len(), 1);
    /// ```
    #[inline]
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
    #[expect(clippy::inline_always, reason = "this method is trivial")]
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
    /// let mut vec = StackVec::<i32, 5>::new();
    /// assert_eq!(vec.remaining_capacity(), 5);
    ///
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.remaining_capacity(), 3);
    ///
    /// vec.extend_from_slice(&[3, 4, 5]);
    /// assert_eq!(vec.remaining_capacity(), 0);
    /// assert!(vec.is_full());
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
    /// let mut vec = StackVec::<i32, 8>::new();
    /// assert!(vec.is_empty());
    /// vec.push(1);
    /// assert!(!vec.is_empty());
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
    /// let mut vec = StackVec::<i32, 2>::new();
    /// assert!(!vec.is_full());
    /// vec.push(1);
    /// vec.push(2);
    /// assert!(vec.is_full());
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
    /// Drops the vector, cleaning up all initialized elements.
    ///
    /// This ensures that all elements stored in the vector are properly dropped
    /// when the vector goes out of scope.
    #[inline]
    fn drop(&mut self) {
        self.drop_elements(0);
    }
}

impl<'vec, T, const CAP: usize> IntoIterator for &'vec StackVec<T, CAP> {
    type Item = &'vec T;
    type IntoIter = slice::Iter<'vec, T>;

    /// Converts the vector into an owning iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let collected: Vec<_> = vec.into_iter().collect();
    /// assert_eq!(collected, vec![1, 2, 3]);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'vec, T, const CAP: usize> IntoIterator for &'vec mut StackVec<T, CAP> {
    type Item = &'vec mut T;
    type IntoIter = slice::IterMut<'vec, T>;

    /// Converts the vector into a mutable iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// for x in &mut vec {
    ///     *x *= 2;
    /// }
    ///
    /// let collected: Vec<_> = vec.iter().copied().collect();
    /// assert_eq!(collected, vec![2, 4, 6]);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// Owning iterator for [`StackVec`]: supports double-ended iteration and is exact-size.
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
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let mut iter = vec.into_iter();
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    fn next(&mut self) -> Option<T> {
        (self.start < self.end).then(|| {
            let idx = self.start;
            self.start += 1;
            // SAFETY: idx is within range [start, end) which are valid initialized elements
            let elem = unsafe { self.v.buf.get_unchecked(idx) };
            // SAFETY: Taking ownership of initialized element
            unsafe { elem.assume_init_read() }
        })
    }

    /// Returns the remaining number of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.extend_from_slice(&[1, 2, 3, 4, 5]);
    ///
    /// let mut iter = vec.into_iter();
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
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let mut iter = vec.into_iter();
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next_back(), Some(3));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        (self.start < self.end).then(|| {
            self.end -= 1;
            let idx = self.end;
            // SAFETY: idx is within range [start, end) which are valid initialized elements
            let elem_ptr = unsafe { self.v.buf.get_unchecked(idx) };
            // SAFETY: elem_ptr points to an initialized element that we are taking ownership of
            unsafe { elem_ptr.assume_init_read() }
        })
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
        for i in self.start..self.end {
            // SAFETY: Accessing element `i` is safe because all elements in this range are initialized.
            let elem_ptr = unsafe { self.v.buf.get_unchecked_mut(i) };

            // SAFETY: `elem_ptr` points to an initialized element that hasn't been dropped yet,
            // so calling `assume_init_drop()` is safe.
            unsafe {
                elem_ptr.assume_init_drop();
            }
        }
        // Prevent the StackVec::Drop from trying to drop them again.
        self.v.len = 0;
    }
}

impl<T, const CAP: usize> IntoIterator for StackVec<T, CAP> {
    type Item = T;
    type IntoIter = IntoIter<T, CAP>;

    /// Converts the vector into an owning iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let collected: Vec<_> = vec.into_iter().collect();
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

    /// Returns the contents as a slice.
    ///
    /// This is equivalent to [`Self::as_slice`].
    ///
    #[inline]
    fn deref(&self) -> &Self::Target {
        Self::as_slice(self)
    }
}

impl<T, const CAP: usize> DerefMut for StackVec<T, CAP> {
    /// Returns the contents as a mutable slice.
    ///
    /// This is equivalent to [`Self::as_mut_slice`].
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        Self::as_mut_slice(self)
    }
}

impl<T, const CAP: usize> AsRef<[T]> for StackVec<T, CAP> {
    /// Returns the contents as a slice.
    ///
    /// This is equivalent to [`Self::as_slice`].
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const CAP: usize> AsMut<[T]> for StackVec<T, CAP> {
    /// Returns the contents as a mutable slice.
    ///
    /// This is equivalent to [`Self::as_mut_slice`].
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        &mut *self
    }
}

impl<T: fmt::Debug, const CAP: usize> fmt::Debug for StackVec<T, CAP> {
    /// Formats the contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.extend_from_slice(&[1, 2, 3]);
    ///
    /// assert_eq!(format!("{:?}", vec), "[1, 2, 3]");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: PartialEq, const CAP: usize> PartialEq for StackVec<T, CAP> {
    /// Checks if two vectors are equal element by element.
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
    /// Performs lexicographic ordering on the vector contents.
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
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: Ord, const CAP: usize> Ord for StackVec<T, CAP> {
    /// Compares two vectors lexicographically.
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
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: Hash, const CAP: usize> Hash for StackVec<T, CAP> {
    /// Hashes the vector contents.
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
    /// Creates a copy of the vector.
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
            for item in self {
                // SAFETY: self.len <= CAP, so cloning all elements fits
                unsafe { out.push_unchecked(item.clone()) }
            }
        } else {
            let dst = out.as_mut_ptr();
            let src = self.as_ptr();
            // SAFETY: Copying self.len initialized elements; both have capacity CAP
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

    /// Attempts to create a vector from a slice.
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
    #[inline]
    fn try_from(slice: &[T]) -> Result<Self, Self::Error> {
        if slice.len() > CAP {
            return Err("value length exceeds capacity");
        }

        let mut vec = Self::new();

        if size_of::<T>() == 0 || mem::needs_drop::<T>() {
            for item in slice {
                // SAFETY: We verified slice.len() <= CAP
                unsafe {
                    vec.push_unchecked(item.clone());
                }
            }
        } else {
            // SAFETY: Copying slice.len() elements which we verified <= CAP
            unsafe {
                ptr::copy_nonoverlapping(slice.as_ptr(), vec.as_mut_ptr(), slice.len());
            }
            vec.len = slice.len();
        }

        Ok(vec)
    }
}

impl<T, const CAP: usize> FromIterator<T> for StackVec<T, CAP> {
    /// Creates a vector from an iterator.
    ///
    /// # Panics
    ///
    /// A panic if the iterator produces more than `CAP` elements.
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
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut vec = Self::new();
        for item in iter {
            assert!(vec.len < CAP, "buffer capacity exceeded in FromIterator");
            // SAFETY: We just verified vec.len < CAP
            unsafe { vec.push_unchecked(item) }
        }
        vec
    }
}

impl<T, const CAP: usize> Extend<T> for StackVec<T, CAP> {
    /// Extends the vector with elements from an iterator.
    ///
    /// # Panics
    ///
    /// A panic if adding all elements would exceed capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 8>::new();
    /// vec.push(1);
    /// vec.extend([2, 3, 4].iter().copied());
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    /// ```
    ///
    /// Extending zero-sized types:
    ///
    /// ```
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<(), 8>::new();
    /// vec.extend_from_slice(&[(), (), ()]);
    /// assert_eq!(vec.len(), 3);
    /// ```
    ///
    /// A panic upon overflow:
    ///
    /// ```should_panic
    /// use stack_collections::StackVec;
    ///
    /// let mut vec = StackVec::<i32, 3>::new();
    ///
    /// // this will panic at runtime
    /// vec.extend([1, 2, 3, 4].iter().copied());
    /// ```
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            assert!(self.len < CAP, "buffer capacity exceeded in extend");
            // SAFETY: We just verified self.len < CAP
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
        Self::index(self, index)
    }
}

impl<T, const CAP: usize> IndexMut<usize> for StackVec<T, CAP> {
    /// Returns a mutable reference to the element at `index`.
    ///
    /// Equivalent to [`Self::index_mut`].
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        Self::index_mut(self, index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;
    use core::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn insert_at_boundaries() {
        let mut vec = StackVec::<i32, 8>::new();

        vec.insert(0, 1_i32);
        assert_eq!(vec[0], 1_i32);

        vec.insert(0, 0_i32);
        assert_eq!(vec.as_slice(), &[0_i32, 1_i32]);

        vec.insert(2, 2);
        assert_eq!(vec.as_slice(), &[0_i32, 1_i32, 2_i32]);
    }

    #[test]
    fn retain_with_drops() {
        struct DropCounter(i32, Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.1.fetch_add(1, Ordering::SeqCst);
            }
        }

        let counter = Arc::new(AtomicUsize::new(0));
        let mut vec = StackVec::<DropCounter, 8>::new();
        vec.push(DropCounter(1, Arc::clone(&counter)));
        vec.push(DropCounter(2, Arc::clone(&counter)));
        vec.push(DropCounter(3, Arc::clone(&counter)));
        vec.push(DropCounter(4, Arc::clone(&counter)));

        vec.retain(|dc| (dc.0 & 1_i32) == 0);

        assert_eq!(vec.len(), 2);
        assert_eq!(counter.load(Ordering::SeqCst), 2);

        drop(vec);
        assert_eq!(counter.load(Ordering::SeqCst), 4);
    }

    #[test]
    fn truncate_drop() {
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let counter = Arc::new(AtomicUsize::new(0));
        let mut vec = StackVec::<DropCounter, 4>::new();
        vec.push(DropCounter(Arc::clone(&counter)));
        vec.push(DropCounter(Arc::clone(&counter)));
        vec.push(DropCounter(Arc::clone(&counter)));

        vec.truncate(1);
        assert_eq!(counter.load(Ordering::SeqCst), 2);

        vec.clear();
        assert_eq!(counter.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn main_drop() {
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let counter = Arc::new(AtomicUsize::new(0));
        {
            let mut vec = StackVec::<DropCounter, 4>::new();
            vec.push(DropCounter(Arc::clone(&counter)));
            vec.push(DropCounter(Arc::clone(&counter)));
            vec.push(DropCounter(Arc::clone(&counter)));

            // At this point, nothing is dropped yet
            assert_eq!(counter.load(Ordering::SeqCst), 0);
        } // vec goes out of scope here
        assert_eq!(counter.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn into_iter_partial_drop() {
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let counter = Arc::new(AtomicUsize::new(0));
        let mut vec = StackVec::<DropCounter, 8>::new();
        vec.push(DropCounter(Arc::clone(&counter)));
        vec.push(DropCounter(Arc::clone(&counter)));
        vec.push(DropCounter(Arc::clone(&counter)));

        let mut iter = vec.into_iter();
        iter.next();

        drop(iter);
        assert_eq!(counter.load(Ordering::SeqCst), 3);
    }
}
