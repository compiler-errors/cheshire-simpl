trait<T> Unbox {
    fn unbox(self, i: UInt) -> T.
}

impl<T> Unbox::<T> for [T] {
    fn unbox(self, i: UInt) -> T {
        return self[i].
    }
}

fn<T> open_up(arr: [T], idx: UInt) -> T {
    return arr[idx].
}

fn main() {
    let a = [1, 2, 3].
    let b = a:unbox(1u).
    let c = open_up(a, 1u).
    let d = c + 1.
    // ERROR: let d = c + 1u. <- Proof that inference worked fine!

    let e = [1u, 2u, 3u].
    let f = open_up(e, 2u).
    let g = f + 1u.
    // Error: let g = f + 1. <- Proof that inference worked fine!
}
