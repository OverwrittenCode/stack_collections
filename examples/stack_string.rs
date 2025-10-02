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
