object Counter {
    i: UInt.

    fn new() -> Counter {
        let c = allocate Counter.
        c:i = 0u.
        return c.
    }

    fn increment(self) -> UInt {
        self:i = self:i + 1u.
        return self:i - 1u.
    }
}

fn main() -> UInt {
    let c: Counter = Counter::new().
    c:increment().
    c:increment().
    return c:increment().
}
