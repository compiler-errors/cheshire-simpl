fn fibonacci(i: UInt) -> UInt {
    // UInt literals are like 0u, 1u, etc.
    if i == 0u | i == 1u {
        return i.
    } else {
        return fibonacci(i - 1u) + fibonacci(i - 2u).
    }
}

fn fibonacci_better(i: UInt) -> UInt {
    if i == 0u | i == 1u {
        return i.
    }

    let a = 0u.
    let b = 1u.

    while i != 0u {
        let c = a + b.
        a = b.
        b = c.
        i = i - 1u.
    }

    return a.
}

fn main() -> UInt {
    return fibonacci(20u) + fibonacci_better(20u).
}
