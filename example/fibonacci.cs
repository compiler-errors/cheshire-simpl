export fn println().
export fn print_string(s: String).
export fn print_uint(i: UInt).
export fn print_int(i: Int).

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
    let i = 0u.

    while true {
        print_uint(i).
        print_string(": ").
        print_uint(fibonacci(i)).
        println().
        i = i + 1u.
    }

    return 0u.
}
