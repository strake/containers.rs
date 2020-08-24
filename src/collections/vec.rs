//! Growable arrays
//!
//! A `Vec` is a dynamically-allocated array which can grow arbitrarily long as elements are
//! added. The cost to insert an element is O(n) in the worst case, if the array must be
//! reallocated, but as each reallocation is r times as big as the prior for some r, is is O(1)
//! on the mean.

use alloc::*;
use core::borrow::{ Borrow, BorrowMut };
use core::cmp::Ordering;
use core::fmt;
use core::hash::{ Hash, Hasher };
use core::iter::*;
use core::mem;
use core::ops;
use core::ops::{ Deref, DerefMut, Index, IndexMut };
use core::ptr;
use core::slice;
use either::{ Either, Left, Right };
use fallible::TryClone;
use unreachable::UncheckedResultExt;

#[cfg(feature = "box")]
use crate::boxed::Box;

use super::raw_vec::RawVec;
use crate::util::*;

/// Growable array
pub struct Vec<T, A: Alloc = crate::DefaultA> {
    raw: RawVec<T, A>,
    len: usize,
}

impl<T, A: Alloc> Vec<T, A> {
    /// Make a new array.
    #[inline]
    pub const fn new_in(a: A) -> Vec<T, A> { Vec { raw: RawVec::new_in(a), len: 0 } }

    /// Make a new array with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline]
    pub fn with_capacity_in(a: A, cap: usize) -> Option<Vec<T, A>> {
        RawVec::with_capacity_in(a, cap).map(|raw| Vec { raw, len: 0 })
    }

    #[inline]
    pub unsafe fn set_length(&mut self, len: usize) { self.len = len }

    /// Return number of elements array can hold before reallocation.
    #[inline]
    pub fn capacity(&self) -> usize { self.raw.capacity() }

    #[inline]
    pub unsafe fn storage_mut(&mut self) -> &mut [T] { self.raw.storage_mut() }

    #[inline]
    fn ptr(&self) -> *mut T { self.raw.ptr() }

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
            let ptr = self.ptr().add(k);
            ptr::copy(&*ptr, ptr.add(1), self.len - k);
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
            let ptr = self.ptr().add(k);
            let x = ptr::read(ptr);
            ptr::copy(&*ptr.add(1), ptr, self.len - k - 1);
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
    pub fn append<B: Alloc>(&mut self, mut xs: Vec<T, B>) -> Result<(), Vec<T, B>> {
        if !self.reserve(xs.len) { return Err(xs) }
        unsafe {
            ptr::copy_nonoverlapping(xs.ptr(), self.ptr().add(self.len), xs.len);
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
            ptr::copy_nonoverlapping(xs.as_ptr(), self.ptr().add(self.len),
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
        if !self.reserve(iter.size_hint().0) { return Err(iter) }
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
        ys.extend(xs)?;
        Ok(ys)
    }

    /// Make of a slice.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline]
    pub fn from_slice_in(a: A, xs: &[T]) -> Option<Self> where T: Copy {
        let mut ys = Vec::new_in(a);
        if ys.append_slice(xs) { Some(ys) } else { None }
    }

    /// Shorten array to `len` and drop elements beyond.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len >= self.len { return; }
        self.len = len;
        unsafe { for p in &mut self.raw.storage_mut()[len..] { ptr::drop_in_place(p) } }
    }

    #[inline]
    pub const fn from_raw(raw: RawVec<T, A>) -> Self { Vec { raw, len: 0 } }

    #[inline]
    pub fn drain<R>(&mut self, r: R) -> Drain<T, A>
      where Self: IndexMut<R, Output = [T]> {
        let (p, l) = { let xs = &mut self[r]; (xs.as_mut_ptr(), xs.len()) };
        let k = ptr_diff(p, self.as_mut_ptr());
        Drain { xs: self, p, q: p.wrapping_add(l), r: k..k+l }
    }

    #[inline]
    pub fn drain_filter<R, F>(&mut self, range: R, filter: F) -> DrainFilter<T, F, A>
      where Self: IndexMut<R, Output = [T]>, F: FnMut(usize, &mut T) -> bool {
        let (p, n) = { let xs = &mut self[range]; (xs.as_mut_ptr(), xs.len()) };
        let a = ptr_diff(p, self.as_ptr());
        DrainFilter { xs: self, a, b: a + n, f: filter }
    }

    #[inline]
    pub unsafe fn alloc_mut(&mut self) -> &mut A { self.raw.alloc_mut() }
}

impl<T, A: Alloc + Default> Vec<T, A> {
    /// Make a new array.
    #[inline]
    pub fn new() -> Self { Self::new_in(A::default()) }

    /// Make a new array with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline]
    pub fn with_capacity(cap: usize) -> Option<Self> {
        Self::with_capacity_in(A::default(), cap)
    }

    /// Add elements of `xs` to aft end of array.
    ///
    /// # Failures
    ///
    /// Returns `Err` of remainder of `xs` if allocation fails, in which case some elements may have been added to `xs` already.
    #[inline]
    pub fn from_iter<Ts: IntoIterator<Item = T>>(xs: Ts) -> Result<Self, Ts::IntoIter> {
        Self::from_iter_in(A::default(), xs)
    }

    /// Make of a slice.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline]
    pub fn from_slice(xs: &[T]) -> Option<Self> where T: Copy {
        Self::from_slice_in(A::default(), xs)
    }
}

impl<T, A: Alloc + TryClone> Vec<T, A> {
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
        let mut xs = Vec::with_capacity_in(self.raw.alloc.try_clone().ok()?, self.len - k)?;
        unsafe {
            xs.len = self.len - k;
            self.len = k;
            ptr::copy_nonoverlapping(self.ptr().add(k), xs.ptr(), xs.len);
        }
        Some(xs)
    }
}

impl<T: TryClone, A: Alloc + TryClone> TryClone for Vec<T, A> {
    type Error = Option<Either<A::Error, T::Error>>;

    #[inline]
    fn try_clone(&self) -> Result<Self, Self::Error> {
        let alloc = self.raw.alloc.try_clone().map_err(Left).map_err(Some)?;
        match Self::with_capacity_in(alloc, self.len) {
            Some(mut new) => {
                new.try_clone_from(self)?;
                Ok(new)
            },
            None => Err(None),
        }
    }

    #[inline]
    fn try_clone_from(&mut self, other: &Self) -> Result<(), Self::Error> {
        if let Some(n_more) = usize::checked_sub(self.capacity(), other.len) {
            if !self.reserve(n_more) { return Err(None); }
        }
        self.truncate(other.len);
        for i in 0..self.len {
            self[i].try_clone_from(&other[i]).map_err(Right).map_err(Some)?;
        }
        for x in &other[self.len..] { unsafe {
            self.push(x.try_clone().map_err(Right).map_err(Some)?).unchecked_unwrap_ok();
        } }
        Ok(())
    }
}

unsafe impl<#[may_dangle] T, A: Alloc> Drop for Vec<T, A> {
    #[inline]
    fn drop(&mut self) {
        unsafe { for p in &mut *self { ptr::drop_in_place(p); } }
    }
}

impl<T, A: Alloc + Default> Default for Vec<T, A> {
    #[inline]
    fn default() -> Self { Vec::new() }
}

#[cfg(feature = "box")]
impl<T, A: Alloc> From<Box<[T], A>> for Vec<T, A> {
    #[inline]
    fn from(xs: Box<[T], A>) -> Self { unsafe {
        let len = xs.len();
        let alloc = ptr::read(&xs.alloc);
        let ptr = xs.into_raw();
        Vec {
            raw: RawVec {
                ptr: ptr.as_ptr().cast().into(),
                cap: len,
                alloc,
            },
            len,
        }
    } }
}

#[cfg(feature = "box")]
impl<T, A: Alloc> From<Vec<T, A>> for Box<[T], A> {
    #[inline]
    fn from(mut xs: Vec<T, A>) -> Self { unsafe {
        let l = xs.len();
        xs.truncate(l);
        let slice = xs.deref_mut().into();
        let alloc = ptr::read(&xs.raw.alloc);
        mem::forget(xs);
        Self::from_raw_in(alloc, slice)
    } }
}

impl<T: PartialEq, A: Alloc> PartialEq for Vec<T, A> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { self[..] == other[..] }
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
        if 0 == mem::size_of::<T>() {
            IntoIter { _raw: raw, p: 0 as _, q: len as _ }
        } else {
            IntoIter { _raw: raw, p: ptr, q: ptr.wrapping_add(len) }
        }
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
    _raw: RawVec<T, A>,
    p: *const T,
    q: *const T,
}

unsafe impl<T: Send, A: Alloc + Send> Send for IntoIter<T, A> {}
unsafe impl<T: Sync, A: Alloc + Sync> Sync for IntoIter<T, A> {}

impl<T: fmt::Debug, A: Alloc> fmt::Debug for IntoIter<T, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { unsafe {
        fmt::Debug::fmt(slice::from_raw_parts(self.p, ptr_diff(self.q, self.p)), f)
    } }
}

impl<T, A: Alloc> Drop for IntoIter<T, A> {
    #[inline]
    fn drop(&mut self) { for _ in self.by_ref() {} }
}

impl<T, A: Alloc> Iterator for IntoIter<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        let len = self.len();
        if 0 == len { None }
        else if 0 == mem::size_of::<T>() { unsafe {
            self.q = (len - 1) as _;
            Some(ptr::read(self.q))
        } }
        else { unsafe {
            let ptr = self.p;
            self.p = self.p.wrapping_offset(1);
            Some(ptr::read(ptr))
        } }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) { (self.len(), Some(self.len())) }
}

impl<T, A: Alloc> ExactSizeIterator for IntoIter<T, A> {
    #[inline]
    fn len(&self) -> usize {
        if 0 == mem::size_of::<T>() { self.q as _ } else { ptr_diff(self.q, self.p) }
    }
}

impl<T, A: Alloc> DoubleEndedIterator for IntoIter<T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        if 0 == self.len() { None } else { unsafe {
            self.q = self.q.wrapping_offset(-1);
            Some(ptr::read(self.q))
        } }
    }
}

#[derive(Debug)]
pub struct Drain<'a, T: 'a, A: 'a + Alloc> {
    xs: &'a mut Vec<T, A>,
    p: *mut T,
    q: *mut T,
    r: ops::Range<usize>,
}

unsafe impl<'a, T: 'a + Send, A: 'a + Alloc + Send> Send for Drain<'a, T, A> {}
unsafe impl<'a, T: 'a + Sync, A: 'a + Alloc + Sync> Sync for Drain<'a, T, A> {}

impl<'a, T: 'a, A: 'a + Alloc> Drop for Drain<'a, T, A> {
    #[inline]
    fn drop(&mut self) {
        for _ in self.by_ref() {}
        unsafe {
            let (p, q) = (self.xs.as_mut_ptr().add(self.r.start),
                          self.xs.as_mut_ptr().add(self.r.end));
            ptr::copy(q, p, self.xs.len - ptr_diff(q, self.xs.as_ptr()));
            let l = self.xs.len() - ptr_diff(q, p);
            self.xs.set_length(l);
        }
    }
}

impl<'a, T: 'a, A: 'a + Alloc> Iterator for Drain<'a, T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        if 0 == self.len() { None } else { unsafe {
            let ptr = self.p;
            self.p = self.p.wrapping_offset(1);
            Some(ptr::read(ptr))
        } }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) { (self.len(), Some(self.len())) }
}

impl<'a, T: 'a, A: 'a + Alloc> ExactSizeIterator for Drain<'a, T, A> {
    #[inline]
    fn len(&self) -> usize { ptr_diff(self.q, self.p) }
}

impl<'a, T: 'a, A: 'a + Alloc> DoubleEndedIterator for Drain<'a, T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        if 0 == self.len() { None } else { unsafe {
            self.q = self.q.wrapping_offset(-1);
            Some(ptr::read(self.q))
        } }
    }
}

#[derive(Debug)]
pub struct DrainFilter<'a, T: 'a, F, A: 'a + Alloc> {
    xs: &'a mut Vec<T, A>,
    a: usize, b: usize, f: F,
}

impl<'a, T: 'a, F: 'a + FnMut(usize, &mut T) -> bool, A: 'a + Alloc> Iterator for DrainFilter<'a, T, F, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        loop {
            if self.a == self.b { return None }
            if (self.f)(self.a, &mut self.xs[self.a]) {
                self.b -= 1;
                return Some(self.xs.delete(self.a))
            } else { self.a += 1 }
        }
    }
}

impl<'a, T: 'a, F: 'a + FnMut(usize, &mut T) -> bool, A: 'a + Alloc> DoubleEndedIterator for DrainFilter<'a, T, F, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        loop {
            if self.a == self.b { return None }
            self.b -= 1;
            if (self.f)(self.b, &mut self.xs[self.b]) {
                return Some(self.xs.delete(self.b));
            }
        }
    }
}

/// ```no_run
/// {
///     let (mut xrefs, x) = (containers::collections::Vec::<_, alloc::NullAllocator>::new(), ());
///     xrefs.push(&x);
/// }
/// ```
#[cfg(doctest)]
struct CanDropVecOfRefs;

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
        let ys = Vec::<_, ::default_allocator::Heap>::from_iter(xs.clone()).unwrap_or_else(|_| panic!("allocation failed"));
        &xs[..] == &ys[..]
    }
    #[quickcheck] fn from_iter_unit(xs: std::vec::Vec<()>) -> bool { test_from_iter(xs) }
    #[quickcheck] fn from_iter_usize(xs: std::vec::Vec<usize>) -> bool { test_from_iter(xs) }

    fn test_into_iter<T: Clone + Eq>(xs: std::vec::Vec<T>) -> bool {
        let ys = Vec::<_, ::default_allocator::Heap>::from_iter(xs.clone()).unwrap_or_else(|_| panic!("allocation failed"));
        Iterator::eq(xs.into_iter(), ys.into_iter())
    }
    #[quickcheck] fn into_iter_unit(xs: std::vec::Vec<()>) -> bool { test_into_iter(xs) }
    #[quickcheck] fn into_iter_usize(xs: std::vec::Vec<usize>) -> bool { test_into_iter(xs) }

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

    #[quickcheck] fn drain_length(std_xs: std::vec::Vec<usize>, r: std::ops::Range<usize>) -> qc::TestResult {
        let mut xs = Vec::from(std_xs);
        let l = xs.len();
        if let None = xs.get(r.clone()) { return qc::TestResult::discard() }
        xs.drain(r.clone());
        qc::TestResult::from_bool(xs.len() + r.len() == l)
    }

    #[quickcheck] fn truncate(std_xs: std::vec::Vec<usize>, n: usize) -> bool {
        let l = std_xs.len();
        let mut xs = Vec::from(std_xs);
        xs.truncate(n);
        xs.len() == usize::min(l, n)
    }
    #[quickcheck] fn truncate_box(std_xs: std::vec::Vec<usize>, n: usize) -> bool {
        let l = std_xs.len();
        let mut xs = Vec::from(std_xs.into_iter().map(std::boxed::Box::new).collect::<std::vec::Vec<_>>());
        xs.truncate(n);
        xs.len() == usize::min(l, n)
    }

    #[quickcheck] fn into_iter(std_xs: std::vec::Vec<usize>) -> bool {
        Iterator::eq(Vec::from(std_xs.clone()).into_iter(), std_xs.into_iter())
    }

    #[quickcheck] fn slice(std_xs: std::vec::Vec<usize>) -> bool {
        Vec::from(std_xs.clone())[..] == std_xs[..]
    }
}
