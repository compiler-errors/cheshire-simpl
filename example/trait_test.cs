object A { }
object B { }

trait ToString {
    fn to_string(self) -> String.
}

trait PrintMe {
    fn print_me(self).
}

impl ToString for A {
    fn to_string(self) -> String {
        return "This is A".
    }
}

impl ToString for B {
    fn to_string(self) -> String {
        return "This is B".
    }
}

impl<T> ToString for [T] where T impl ToString {
    fn to_string(self) -> String {
        let k = "[".
        for i in self {
            k = k + i:to_string() + ", "
        }
        return k + "]".
    }
}

impl<T> PrintMe for T where T impl ToString {
    fn print_me(self) {
        print_str(self:to_string()).
        println().
    }
}

fn main() -> UInt {
    let a = allocate A.
    let b = allocate B.

    a:print_me().
    b:print_me().

    let c = [1, 2, 3, 4].
    c:print_me().
}
