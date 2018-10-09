//! Heaps

use alloc::*;
use heap as slice;
use rel::ord::*;
use super::vec::Vec;

/// Growable heap in terms of `Vec`
#[derive(Debug)]
pub struct Heap<T, Rel: TotalOrderRelation<T> = ::rel::Core, A: Alloc = ::DefaultA> {
    rel: Rel,
    arity: usize,
    data: Vec<T, A>,
}

impl<T, Rel: TotalOrderRelation<T>, A: Alloc> Heap<T, Rel, A> {
    /// Make a new heap.
    #[inline] pub fn new_in(a: A, rel: Rel, arity: usize) -> Self {
        Heap { rel: rel, arity: arity, data: Vec::new_in(a) }
    }

    /// Make a new heap with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline] pub fn with_capacity_in(a: A, rel: Rel, arity: usize, cap: usize) -> Option<Self> {
        Vec::with_capacity_in(a, cap).map(|v| Self::from_vec(rel, arity, v))
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
    #[inline] pub fn from_vec(rel: Rel, arity: usize, mut v: Vec<T, A>) -> Self {
        slice::build(arity, |a, b| rel.less(a, b), &mut v[..]);
        Heap { rel: rel, arity: arity, data: v }
    }

    /// Push an element into the heap.
    #[inline] pub fn push(&mut self, x: T) -> Result<(), T> {
        let (arity, (rel, data)) = (self.arity, self.components());
        data.push(x).map(|()| slice::push(arity, |a, b| rel.less(a, b), &mut data[..]))
    }

    /// Pop the root element off the heap and return it; return `None` if heap empty.
    #[inline] pub fn pop(&mut self) -> Option<T> {
        if self.data.len() == 0 { None } else {
            let (arity, (rel, data)) = (self.arity, self.components());
            slice::pop(arity, |a, b| rel.less(a, b), &mut data[..]);
            data.pop()
        }
    }

    /// Return a reference to root element, or `None` if heap empty.
    #[inline] pub fn peek(&self) -> Option<&T> {
        if self.data.len() == 0 { None } else { Some(&self.data[0]) }
    }

    /// Return a mutable reference to root element, or `None` if heap empty.
    #[inline] pub fn peek_mut(&mut self) -> Option<&mut T> {
        if self.data.len() == 0 { None } else { Some(&mut self.data[0]) }
    }

    /// Pops the root and inserts the given value.
    /// `xs` being empty is an error.
    #[inline] pub fn push_pop(&mut self, x: T) -> T {
        let (arity, (rel, data)) = (self.arity, self.components());
        slice::replace_root(arity, |a, b| rel.less(a, b), &mut data[..], x)
    }

    /// Return a `Vec` of elements of heap in unspecified order.
    #[inline] pub fn into_vec(self) -> Vec<T, A> { self.data }

    /// Return a `Vec` of elements of heap in sorted order.
    #[inline] pub fn into_sorted_vec(mut self) -> Vec<T, A> {
        {
            let (arity, (rel, data)) = (self.arity, self.components());
            slice::sort(arity, |a, b| rel.less(a, b), &mut data[..]);
        }
        self.data
    }

    fn components(&mut self) -> (&Rel, &mut Vec<T, A>) { (&self.rel, &mut self.data) }

    #[inline]
    pub unsafe fn alloc_mut(&mut self) -> &mut A { self.data.alloc_mut() }
}
