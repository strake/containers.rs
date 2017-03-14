//! Heaps

use core::marker::PhantomData;
use heap as slice;

use rel::ord::*;
use super::vec::Vec;

/// Growable heap in terms of `Vec`
pub struct Heap<T, Rel: TotalOrderRelation<T> = Ord> {
    φ: PhantomData<(Rel)>,
    arity: usize,
    data: Vec<T>,
}

impl<T, Rel: TotalOrderRelation<T>> Heap<T, Rel> {
    /// Make a new heap.
    #[inline] pub fn new(arity: usize) -> Self {
        Heap { φ: PhantomData, arity: arity, data: Vec::new() }
    }

    /// Make a new heap with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline] pub fn with_capacity(arity: usize, cap: usize) -> Option<Self> {
        Vec::with_capacity(cap).map(|v| Self::from_vec(arity, v))
    }

    /// Return arity.
    #[inline] pub fn arity   (&self) -> usize { self.arity }

    /// Return number of elements in heap.
    #[inline] pub fn length  (&self) -> usize { self.data.len() }

    /// Return number of elements heap can hold before reallocation.
    #[inline] pub fn capacity(&self) -> usize { self.data.capacity() }

    /// Make sure the heap has enough room for at least `n_more` more elements, reallocating if need be.
    ///
    /// # Failures
    ///
    /// Returns `false` if allocation fails, `true` otherwise.
    #[inline] pub fn reserve(&mut self, n_more: usize) -> bool { self.data.reserve(n_more) }

    /// Build a heap of the elements of `v`.
    #[inline] pub fn from_vec(arity: usize, mut v: Vec<T>) -> Self {
        slice::build(arity, Rel::less, &mut v[..]);
        Heap { φ: PhantomData, arity: arity, data: v }
    }

    /// Push an element into the heap.
    #[inline] pub fn push(&mut self, x: T) -> Result<(), T> {
        self.data.push(x).map(|()| slice::push(self.arity, Rel::less, &mut self.data[..]))
    }

    /// Pop the root element off the heap and return it; return `None` if heap empty.
    #[inline] pub fn pop(&mut self) -> Option<T> {
        if self.data.len() == 0 { None } else { slice::pop(self.arity, Rel::less, &mut self.data[..]); self.data.pop() }
    }

    /// Return a reference to root element, or `None` if heap empty.
    #[inline] pub fn peek(&self) -> Option<&T> {
        if self.data.len() == 0 { None } else { Some(&self.data[0]) }
    }

    /// Return a mutable reference to root element, or `None` if heap empty.
    #[inline] pub fn peek_mut(&mut self) -> Option<&T> {
        if self.data.len() == 0 { None } else { Some(&mut self.data[0]) }
    }

    /// Pops the root and inserts the given value.
    /// `xs` being empty is an error.
    #[inline] pub fn push_pop(&mut self, x: T) -> T {
        slice::replace_root(self.arity, Rel::less, &mut self.data[..], x)
    }

    /// Return a `Vec` of elements of heap in unspecified order.
    #[inline] pub fn into_vec(self) -> Vec<T> { self.data }

    /// Return a `Vec` of elements of heap in sorted order.
    #[inline] pub fn into_sorted_vec(mut self) -> Vec<T> {
        slice::sort(self.arity, Rel::less, &mut self.data[..]);
        self.data
    }
}
