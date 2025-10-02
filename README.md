# stack_collections

[![Crates.io](https://img.shields.io/crates/v/stack_collections.svg)](https://crates.io/crates/stack_collections)
[![Documentation](https://docs.rs/stack_collections/badge.svg)](https://docs.rs/stack_collections)

Stack-allocated collections for Rust: fixed-capacity string and vector types that live entirely on the stack.

## Features

- **`StackString<N>`**: UTF-8 encoded, fixed-capacity string stored on the stack
- **`StackVec<T, CAP>`**: Fixed-capacity vector stored on the stack
- **`StackArrayString<N, CAP>`**: Convenience alias for `StackVec<StackString<N>, CAP>`
- Zero heap allocations
- `const fn` constructors and many operations
- Comprehensive API with safe and unsafe variants
- Full iterator support including `IntoIterator`, `DoubleEndedIterator`, and `ExactSizeIterator`
- Standard trait implementations: `Debug`, `Display`, `Clone`, `Hash`, `PartialEq`, `Eq`, `Ord`, etc.
- `Write` trait implementation for `StackString`

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
stack_collections = "0.1.0"
```

### StackString Example

```rust
use stack_collections::StackString;

fn main() {
    let mut s = StackString::<32>::new();
    s.push_str("Hello, ");
    s.push_str("world!");

    println!("String: {}", s);
    println!("Length: {}", s.len());
    println!("Capacity: {}", s.capacity());

    // Pop characters
    while let Some(c) = s.try_pop() {
        println!("Popped: {}", c);
    }
}
```

### StackVec Example

```rust
use stack_collections::StackVec;

fn main() {
    let mut v = StackVec::<i32, 8>::new();

    for i in 1..=5 {
        v.push(i);
    }

    println!("Vector: {:?}", v);
    println!("Sum: {}", v.iter().sum::<i32>());

    v.retain(|x| *x % 2 == 0);
    println!("Even numbers: {:?}", v);
}
```

### StackArrayString Example

```rust
use stack_collections::StackArrayString;

fn main() {
    // StackArrayString is a convenient alias for StackVec<StackString<N>, CAP>
    let mut arr: StackArrayString<16, 4> = StackArrayString::new();

    arr.push("hello".try_into().unwrap());
    arr.push("world".try_into().unwrap());

    assert_eq!(arr.len(), 2);
    assert_eq!(arr.capacity(), 4);
    assert_eq!(arr[0].capacity(), 16);
    assert_eq!(arr[0].as_str(), "hello");
    assert_eq!(arr[1].as_str(), "world");
}
```

## When to Use

Use `stack_collections` when you:

- Need predictable memory usage without heap allocations
- Know the maximum capacity at compile time
- Want to avoid allocator overhead for small collections
- Are working in `no_std` environments (note: currently requires `std` for some traits)
- Need deterministic performance without allocator variance

## API Overview

Both `StackString` and `StackVec` provide:

- **Unchecked variants**: `push_unchecked`, `pop_unchecked`, etc. for performance-critical code
- **Try variants**: `try_push`, `try_pop`, etc. that return `Option` instead of panicking
- **Standard methods**: `push`, `pop`, `insert`, `remove`, `clear`, `truncate`, etc.
- **Deref to slice/str**: Seamless integration with standard library functions

## Safety

This crate uses `unsafe` internally for performance but exposes a safe API. All unsafe operations are carefully documented and validated. The public API is designed to prevent
undefined behavior even when capacity is exceeded (operations will panic or return `None` instead).

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as
above, without any additional terms or conditions.