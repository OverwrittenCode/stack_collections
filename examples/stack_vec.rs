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
