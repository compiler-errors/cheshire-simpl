export fn println().
export fn print_string(s: String).

fn main() {
  let x = get_a_string().
  print_string(x).
  println().
}

fn get_a_string() -> String {
  return "Hello, world!".
}
