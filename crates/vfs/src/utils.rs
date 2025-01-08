use std::cell::Ref;

pub struct VecRefWrapper<'a, T: 'a>(pub Ref<'a, Vec<T>>);

impl<'a, 'b: 'a, T: 'a> IntoIterator for &'b VecRefWrapper<'a, T> {
    type IntoIter = std::slice::Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> std::slice::Iter<'a, T> {
        self.0.iter()
    }
}
