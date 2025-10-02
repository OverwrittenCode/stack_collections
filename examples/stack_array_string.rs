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
