//! Heaps

pub mod slice;

use core::marker::PhantomData;

use rel::ord::*;
use typenum::consts as N;
use typenum::uint::Unsigned;
use super::vec::Vec;

/// Growable heap in terms of `Vec`
pub struct Heap<T, Arity: Unsigned = N::U2, Rel: TotalOrderRelation<T> = Ord>(PhantomData<(Arity, Rel)>, Vec<T>);

impl<T, Arity: Unsigned, Rel: TotalOrderRelation<T>> Heap<T, Arity, Rel> {
    /// Make a new heap.
    #[inline] pub fn new() -> Self { Heap(PhantomData, Vec::new()) }

    /// Make a new heap with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline] pub fn with_capacity(cap: usize) -> Option<Self> { Vec::with_capacity(cap).map(Self::from_vec) }

    /// Return number of elements in heap.
    #[inline] pub fn length  (&self) -> usize { match self { &Heap(_, ref v) => v.len() } }

    /// Return number of elements heap can hold before reallocation.
    #[inline] pub fn capacity(&self) -> usize { match self { &Heap(_, ref v) => v.capacity() } }

    /// Make sure the heap has enough room for at least `n_more` more elements, reallocating if need be.
    ///
    /// # Failures
    ///
    /// Returns `false` if allocation fails, `true` otherwise.
    #[inline] pub fn reserve(&mut self, n_more: usize) -> bool { match self { &mut Heap(_, ref mut v) => v.reserve(n_more) } }

    /// Build a heap of the elements of `v`.
    #[inline] pub fn from_vec(mut v: Vec<T>) -> Self {
        slice::build(Arity::to_usize(), Rel::less, &mut v[..]);
        Heap(PhantomData, v)
    }

    /// Push an element into the heap.
    #[inline] pub fn push(&mut self, x: T) -> Result<(), T> {
        let &mut Heap(_, ref mut v) = self;
        v.push(x).map(|()| slice::push(Arity::to_usize(), Rel::less, &mut v[..]))
    }

    /// Pop the root element off the heap and return it; return `None` if heap empty.
    #[inline] pub fn pop(&mut self) -> Option<T> {
        let &mut Heap(_, ref mut v) = self;
        if v.len() == 0 { None } else { slice::pop(Arity::to_usize(), Rel::less, &mut v[..]); v.pop() }
    }

    /// Return a reference to root element, or `None` if heap empty.
    #[inline] pub fn peek(&self) -> Option<&T> {
        let &Heap(_, ref v) = self;
        if v.len() == 0 { None } else { Some(&v[0]) }
    }

    /// Return a mutable reference to root element, or `None` if heap empty.
    #[inline] pub fn peek_mut(&mut self) -> Option<&T> {
        let &mut Heap(_, ref mut v) = self;
        if v.len() == 0 { None } else { Some(&mut v[0]) }
    }

    /// Pops the root and inserts the given value.
    /// `xs` being empty is an error.
    #[inline] pub fn push_pop(&mut self, x: T) -> T {
        let &mut Heap(_, ref mut v) = self;
        slice::replace_root(Arity::to_usize(), Rel::less, &mut v[..], x)
    }

    /// Return a `Vec` of elements of heap in unspecified order.
    #[inline] pub fn into_vec(self) -> Vec<T> { self.1 }

    /// Return a `Vec` of elements of heap in sorted order.
    #[inline] pub fn into_sorted_vec(self) -> Vec<T> {
        let Heap(_, mut v) = self;
        slice::sort(Arity::to_usize(), Rel::less, &mut v[..]);
        v
    }
}
