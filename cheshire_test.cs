fn main() -> (Bool, Bool) {
    let a: Bool = true.
    let b: _ = false.

    if a & b {
        return (a, b).
    }
}

fn fibonacci(i: UInt) -> UInt {
    if i == 0u | i == 2u {
        return i.
    }

    return fibonacci(i - 1u) + fibonacci(i - 2u).
}
