//! Growable arrays
//!
//! A `Vec` is a dynamically-allocated array which can grow arbitrarily long as elements are
//! added. The cost to insert an element is O(n) in the worst case, if the array must be
//! reallocated, but as each reallocation is r times as big as the prior for some r, is is O(1)
//! on the mean.

use alloc::heap::*;
use core::borrow::{ Borrow, BorrowMut };
use core::cmp::Ordering;
use core::fmt;
use core::hash::{ Hash, Hasher };
use core::mem;
use core::ops;
use core::ops::{ Deref, DerefMut, Index, IndexMut };
use core::ptr;
use core::slice;

use super::raw_vec::RawVec;

/// Growable array
pub struct Vec<T, A: Alloc = Heap> {
    raw: RawVec<T, A>,
    len: usize,
}

unsafe impl<T: Send> Send for Vec<T, Heap> {}
unsafe impl<T: Sync> Sync for Vec<T, Heap> {}

impl<T, A: Alloc> Vec<T, A> {
    /// Make a new array.
    #[inline]
    pub fn new_in(a: A) -> Vec<T, A> { Vec { raw: RawVec::new_in(a), len: 0 } }

    /// Make a new array with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline]
    pub fn with_capacity_in(a: A, cap: usize) -> Option<Vec<T, A>> {
        RawVec::with_capacity_in(a, cap).map(|raw| Vec { raw: raw, len: 0 })
    }

    #[inline] pub unsafe fn set_length(&mut self, len: usize) { self.len = len }

    /// Return number of elements array can hold before reallocation.
    #[inline] pub fn capacity(&self) -> usize { self.raw.capacity() }

    #[inline] pub unsafe fn storage_mut(&mut self) -> &mut [T] { self.raw.storage_mut() }

    #[inline] fn ptr(&self) -> *mut T { self.raw.ptr() }

    /// Make sure the array has enough room for at least `n_more` more elements, reallocating if need be.
    ///
    /// # Failures
    ///
    /// Returns `false` if allocation fails, `true` otherwise.
    #[inline]
    pub fn reserve(&mut self, n_more: usize) -> bool { self.raw.reserve(self.len, n_more) }

    /// Relinquish memory so capacity = length.
    #[inline]
    pub fn relinquish(&mut self) -> bool { self.raw.relinquish(self.len) }

    /// Insert element `x` at position `k`, shifting elements after `k` aftward one position to make room.
    ///
    /// # Failures
    ///
    /// Returns `Err(x)` if allocation fails.
    ///
    /// # Panics
    ///
    /// Panics if `k` is out of bounds.
    #[inline]
    pub fn insert(&mut self, k: usize, x: T) -> Result<(), T> {
        assert!(k <= self.len);
        if !self.reserve(1) { return Err(x) }
        unsafe {
            let ptr = self.ptr().offset(k as isize);
            ptr::copy(&*ptr, ptr.offset(1), self.len - k);
            ptr::write(&mut *ptr, x);
        }
        self.len += 1;
        Ok(())
    }

    /// Delete element at position `k` and return it, shifting elements after `k` forward one position to fill the gap.
    ///
    /// # Panics
    ///
    /// Panics if `k` is out of bounds.
    #[inline]
    pub fn delete(&mut self, k: usize) -> T {
        assert!(k < self.len);
        unsafe {
            let ptr = self.ptr().offset(k as isize);
            let x = ptr::read(ptr);
            ptr::copy(&*ptr.offset(1), ptr, self.len - k - 1);
            self.len -= 1;
            x
        }
    }

    /// Delete element at position `k` and move the last element into the gap.
    ///
    /// # Panics
    ///
    /// Panics if `k` is out of bounds.
    #[inline]
    pub fn delete_swap_last(&mut self, k: usize) -> T {
        assert!(k < self.len);
        let l = self.len - 1;
        self.swap(k, l);
        self.delete(l)
    }

    /// Push `x` onto aft end of array.
    ///
    /// # Failures
    ///
    /// Returns `Err(x)` if allocation fails.
    #[inline]
    pub fn push(&mut self, x: T) -> Result<(), T> { let len = self.len; self.insert(len, x) }

    /// Pop last element off end of array.
    /// Return `None` if array empty.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let len = self.len;
        if len == 0 { None } else { Some(self.delete(len - 1)) }
    }

    /// Append `xs` to the array.
    ///
    /// # Failures
    ///
    /// Returns `Err(xs)` if allocation fails, in which case both `self` and `xs` are unmodified.
    #[inline]
    pub fn append(&mut self, mut xs: Self) -> Result<(), Self> {
        if !self.reserve(xs.len) { return Err(xs) }
        unsafe {
            ptr::copy_nonoverlapping(xs.ptr(), self.ptr().offset(self.len as isize), xs.len);
            self.len += xs.len;
            xs.len = 0;
        }
        Ok(())
    }

    /// Copy `xs` and append it to the array.
    ///
    /// # Failures
    ///
    /// Returns `false` if allocation fails, in which case `self` is unmodified.
    #[inline]
    pub fn append_slice(&mut self, xs: &[T]) -> bool where T: Copy {
        self.reserve(xs.len()) && unsafe {
            ptr::copy_nonoverlapping(xs.as_ptr(), self.ptr().offset(self.len as isize),
                                     xs.len());
            self.len += xs.len();
            true
        }
    }

    /// Add elements of `xs` to aft end of array.
    ///
    /// # Failures
    ///
    /// Returns `Err` of remainder of `xs` if allocation fails.
    #[inline]
    pub fn extend<Ts: IntoIterator<Item = T>>(&mut self, xs: Ts) -> Result<(), Ts::IntoIter> {
        let mut iter = xs.into_iter();
        loop {
            if !self.reserve(1) { return Err(iter) }
            match iter.next() {
                None => return Ok(()),
                Some(x) => self.push(x).unwrap_or(())
            }
        }
    }

    /// Add elements of `xs` to aft end of array.
    ///
    /// # Failures
    ///
    /// Returns `Err` of remainder of `xs` if allocation fails, in which case some elements may have been added to `xs` already.
    #[inline]
    pub fn from_iter_in<Ts: IntoIterator<Item = T>>(a: A, xs: Ts) -> Result<Self, Ts::IntoIter> {
        let mut ys = Vec::new_in(a);
        let mut iter = xs.into_iter();
        loop {
            if !ys.reserve(1) { return Err(iter) }
            match iter.next() {
                None => return Ok(ys),
                Some(x) => ys.push(x).unwrap_or(())
            }
        }
    }

    /// Shorten array to `len` and drop elements beyond.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        for p in &self[len..] { unsafe { ptr::read(p); } }
        self.len = len;
    }
}

impl<T> Vec<T, Heap> {
    /// Make a new array.
    #[inline]
    pub fn new() -> Self { Self::new_in(Heap) }

    /// Make a new array with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline]
    pub fn with_capacity(cap: usize) -> Option<Self> { Self::with_capacity_in(Heap, cap) }

    /// Add elements of `xs` to aft end of array.
    ///
    /// # Failures
    ///
    /// Returns `Err` of remainder of `xs` if allocation fails, in which case some elements may have been added to `xs` already.
    #[inline]
    pub fn from_iter<Ts: IntoIterator<Item = T>>(xs: Ts) -> Result<Self, Ts::IntoIter> {
        Self::from_iter_in(Heap, xs)
    }
}

impl<T, A: Alloc + Clone> Vec<T, A> {
    /// Split off and return the segment of the array from `k` to the aft end, inclusive.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails, in which case `self` is unmodified.
    ///
    /// # Panics
    ///
    /// Panics if `k` is out of bounds.
    #[inline]
    pub fn split_off(&mut self, k: usize) -> Option<Vec<T, A>> {
        assert!(k <= self.len, "out of bounds");
        let mut xs = Vec::with_capacity_in(self.raw.alloc.clone(), self.len - k)?;
        unsafe {
            xs.len = self.len - k;
            self.len = k;
            ptr::copy_nonoverlapping(self.ptr().offset(k as isize), xs.ptr(), xs.len);
        }
        Some(xs)
    }
}

impl<T, A: Alloc> Drop for Vec<T, A> {
    #[inline]
    fn drop(&mut self) {
        unsafe { for p in &mut *self { ptr::drop_in_place(p); } }
    }
}

impl<T> Default for Vec<T, Heap> {
    #[inline]
    fn default() -> Self { Vec::new() }
}

impl<T: PartialEq, A: Alloc> PartialEq for Vec<T, A> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { &self[..] == &other[..] }
}

impl<T: PartialOrd, A: Alloc> PartialOrd for Vec<T, A> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { PartialOrd::partial_cmp(&self[..], &other[..]) }
}

impl<T: Eq, A: Alloc> Eq for Vec<T, A> {}

impl<T: Ord, A: Alloc> Ord for Vec<T, A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering { Ord::cmp(&self[..], &other[..]) }
}

macro_rules! impl_Index {
    ($t: ty) =>
        (impl<T, A: Alloc> Index<$t> for Vec<T, A> {
             type Output = <[T] as Index<$t>>::Output;

             #[inline]
             fn index(&self, k: $t) -> &Self::Output { &self.deref()[k] }
         }

         impl<T, A: Alloc> IndexMut<$t> for Vec<T, A> {
             #[inline]
             fn index_mut(&mut self, k: $t) -> &mut Self::Output { &mut self.deref_mut()[k] }
         })
}

impl_Index!(usize);
impl_Index!(ops::Range<usize>);
impl_Index!(ops::RangeTo<usize>);
impl_Index!(ops::RangeFrom<usize>);
impl_Index!(ops::RangeFull);

impl<T, A: Alloc> Borrow<[T]> for Vec<T, A> {
    #[inline]
    fn borrow(&self) -> &[T] { self }
}

impl<T, A: Alloc> BorrowMut<[T]> for Vec<T, A> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] { self }
}

impl<T, A: Alloc> Deref for Vec<T, A> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &[T] { unsafe { slice::from_raw_parts(self.ptr(), self.len) } }
}

impl<T, A: Alloc> DerefMut for Vec<T, A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
         unsafe { slice::from_raw_parts_mut(self.ptr(), self.len) }
    }
}

impl<T: Hash, A: Alloc> Hash for Vec<T, A> {
    #[inline]
    fn hash<H: Hasher>(&self, h: &mut H) { self[..].hash(h) }
}

impl<T: fmt::Debug, A: Alloc> fmt::Debug for Vec<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(&self[..], f) }
}

impl<T, A: Alloc> IntoIterator for Vec<T, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    #[inline]
    fn into_iter(self) -> IntoIter<T, A> { unsafe {
        let raw = ptr::read(&self.raw);
        let len = self.len;
        let ptr = raw.ptr();
        mem::forget(self);
        IntoIter { raw: raw, ptr: ptr, len: len }
    } }
}

impl<'a, T, A: Alloc> IntoIterator for &'a Vec<T, A> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> slice::Iter<'a, T> { self.iter() }
}

impl<'a, T, A: Alloc> IntoIterator for &'a mut Vec<T, A> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> slice::IterMut<'a, T> { self.iter_mut() }
}

pub struct IntoIter<T, A: Alloc> {
    #[allow(dead_code)] // we need to keep this memory until we finish iterating
    raw: RawVec<T, A>,
    ptr: *const T,
    len: usize,
}

unsafe impl<T: Send> Send for IntoIter<T, Heap> {}
unsafe impl<T: Sync> Sync for IntoIter<T, Heap> {}

impl<T, A: Alloc> Drop for IntoIter<T, A> {
    #[inline]
    fn drop(&mut self) { for _ in self.by_ref() {} }
}

impl<T, A: Alloc> Iterator for IntoIter<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        if self.len == 0 { None } else {
            unsafe {
                self.len -= 1;
                let ptr = self.ptr;
                self.ptr = self.ptr.offset(1);
                Some(ptr::read(ptr))
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) { (self.len, Some(self.len)) }
}

#[cfg(test)] mod tests {
    use core::fmt;
    use core::mem;
    use std;
    use quickcheck as qc;

    use super::*;

    impl<T> From<std::vec::Vec<T>> for Vec<T> {
        fn from(mut xs: std::vec::Vec<T>) -> Vec<T> {
            let ys = Vec {
                raw: unsafe { RawVec::from_raw_parts(xs.as_mut_ptr(), xs.capacity()) },
                len: xs.len(),
            };
            mem::forget(xs);
            ys
        }
    }

    fn test_with_capacity_0<T>() { Vec::with_capacity(0).unwrap() as Vec<T>; }
    #[test] fn with_capacity_0_unit() { test_with_capacity_0::<()>() }
    #[test] fn with_capacity_0_usize() { test_with_capacity_0::<usize>() }

    fn test_from_iter<T: Clone + Eq>(xs: std::vec::Vec<T>) -> bool {
        let ys = Vec::from_iter(xs.clone()).unwrap_or_else(|_| panic!("allocation failed"));
        &xs[..] == &ys[..]
    }
    #[quickcheck] fn from_iter_unit(xs: std::vec::Vec<()>) -> bool { test_from_iter(xs) }
    #[quickcheck] fn from_iter_usize(xs: std::vec::Vec<usize>) -> bool { test_from_iter(xs) }

    fn test_reservation_and_relinquishment<T>(std_xs: std::vec::Vec<T>) -> bool {
        let mut xs = Vec::from(std_xs);
        xs.reserve(1) && xs.capacity() > xs.len() &&
        xs.relinquish() && xs.capacity() == xs.len()
    }
    #[quickcheck] fn reservation_and_relinquishment_unit(std_xs: std::vec::Vec<()>) -> bool { test_reservation_and_relinquishment(std_xs) }
    #[quickcheck] fn reservation_and_relinquishment_usize(std_xs: std::vec::Vec<usize>) -> bool { test_reservation_and_relinquishment(std_xs) }

    fn test_split_off_and_append<T: Clone + Eq + fmt::Debug>(std_xs: std::vec::Vec<T>, n: usize) -> qc::TestResult {
        let xs = Vec::from(std_xs.clone());
        let mut ys = Vec::from(std_xs);
        if n > xs.len() { return qc::TestResult::discard() };
        let zs = ys.split_off(n).unwrap();
        qc::TestResult::from_bool(ys.len() == n && {
            ys.append(zs).unwrap();
            xs == ys
        })
    }
    #[quickcheck] fn split_off_and_append_unit(std_xs: std::vec::Vec<()>, n: usize) -> qc::TestResult { test_split_off_and_append(std_xs, n) }
    #[quickcheck] fn split_off_and_append_usize(std_xs: std::vec::Vec<usize>, n: usize) -> qc::TestResult { test_split_off_and_append(std_xs, n) }
}
