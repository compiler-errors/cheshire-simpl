object A {}
object B {}

trait C {}
trait D {
    fn foo(self).
}

impl C for A {}
impl<T> D for T where T: C {}

fn main() {
    let a = allocate A.
    let b = allocate B.

    a:foo().
    // ERROR: b:foo(). <- conditional impl fails b/c B does not impl C.
}
