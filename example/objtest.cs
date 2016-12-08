object<T> Box {
    t: T.
}

fn main() {
    let int_box = allocate Box::<Int>.
    let string_box = allocate Box::<String>.
    let guess_box = allocate Box::<_>.

    if string_box:t == "Hello, world!" {
        let d = int_box:t + 1.
    }

    guess_box:t = 1u.
    let a = guess_box:t + 1u.
    //let b = guess_box:t + 1.
}
