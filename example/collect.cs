trait<I> Collectable {
    fn<T: Collector<I>> collect(self).
}

trait<I> Collector {
    fn new_collector() -> Self.
    fn take(self, item: I).
}

struct<T> Vec { ... }

impl<I> Collector<I> for Vec<I> {
    fn new_collector() -> Vec<I> {
        return Vec::new().
    }

    fn take(self, item: I) {
        self:add(item).
    }
}
