//! Growable arrays
//!
//! A `Vec` is a dynamically-allocated array which can grow arbitrarily long as elements are
//! added. The cost to insert an element is O(n) in the worst case, if the array must be
//! reallocated, but as each reallocation is r times as big as the prior for some r, is is O(1)
//! on the mean.

use alloc::heap::{ EMPTY, allocate, reallocate, deallocate };
use core::cmp::Ordering;
use core::fmt;
use core::hash::{ Hash, Hasher };
use core::mem;
use core::ops;
use core::ops::{ Deref, DerefMut, Index, IndexMut };
use core::ptr;
use core::ptr::Unique;
use core::slice;

/// Growable array
pub struct Vec<T> {
    ptr: Unique<T>,
    cap: usize,
    len: usize,
}

unsafe impl<T: Send> Send for Vec<T> {}
unsafe impl<T: Sync> Sync for Vec<T> {}

impl<T> Vec<T> {
    /// Make a new array.
    #[inline]
    pub fn new() -> Vec<T> { unsafe { Vec { ptr: Unique::new(EMPTY as *mut T), len: 0, cap: 0 } } }

    /// Make a new array with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline]
    pub fn with_capacity(cap: usize) -> Option<Vec<T>> {
        if mem::size_of::<T>() == 0 {
            Some(unsafe { Vec { ptr: Unique::new(EMPTY as *mut T), len: 0, cap: cap } })
        } else if cap == 0 {
            Some(Vec::new())
        } else {
            let size = tryOpt!(cap.checked_mul(mem::size_of::<T>()));
            let ptr = unsafe { allocate(size, mem::align_of::<T>()) as *mut T };
            if ptr.is_null() { None }
            else { Some(unsafe { Vec { ptr: Unique::new(ptr), len: 0, cap: cap } }) }
        }
    }

    #[inline] pub unsafe fn set_length(&mut self, len: usize) { self.len = len }

    /// Return number of elements array can hold before reallocation.
    #[inline] pub fn capacity(&self) -> usize { self.cap }

    #[inline] pub unsafe fn storage_mut(&mut self) -> &mut [T] {
        slice::from_raw_parts_mut(*self.ptr, self.cap)
    }

    /// Make sure the array has enough room for at least `n_more` more elements, reallocating if need be.
    ///
    /// # Failures
    ///
    /// Returns `false` if allocation fails, `true` otherwise.
    #[inline]
    pub fn reserve(&mut self, n_more: usize) -> bool {
        let len = self.len;
        if self.cap - len < n_more {
            self.grow(match len.checked_add(n_more).and_then(|n| n.checked_next_power_of_two()) {
                          None => return false,
                          Some(cap) => cap,
                      })
        } else { true }
    }

    /// Relinquish memory so capacity = length.
    #[inline]
    pub fn relinquish(&mut self) -> bool {
        if self.cap == self.len { return true }
        if mem::size_of::<T>() > 0 { unsafe {
            if self.len == 0 { dealloc_array(*self.ptr, self.cap) }
            else {
                let ptr = reallocate(*self.ptr as *mut u8,
                                     mem::size_of::<T>()*self.cap,
                                     mem::size_of::<T>()*self.len,
                                     mem::align_of::<T>()) as *mut T;
                if ptr.is_null() { return false; }
                self.ptr = Unique::new(ptr);
            }
        } }
        self.cap = self.len;
        true
    }

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
            let ptr = self.ptr.offset(k as isize);
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
            let ptr = self.ptr.offset(k as isize);
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
        self.len -= 1;
        let len = self.len;
        (*self).swap(k, len);
        self.delete(len)
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
            ptr::copy_nonoverlapping(*xs.ptr, self.ptr.offset(self.len as isize), xs.len);
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
            ptr::copy_nonoverlapping(xs.as_ptr(), self.ptr.offset(self.len as isize), xs.len());
            self.len += xs.len();
            true
        }
    }

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
    pub fn split_off(&mut self, k: usize) -> Option<Vec<T>> {
        assert!(k <= self.len, "out of bounds");
        let mut xs = tryOpt!(Vec::with_capacity(self.len - k));
        unsafe {
            xs.len = self.len - k;
            self.len = k;
            ptr::copy_nonoverlapping(self.ptr.offset(k as isize), *xs.ptr, xs.len);
        }
        Some(xs)
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
    pub fn from_iter<Ts: IntoIterator<Item = T>>(xs: Ts) -> Result<Vec<T>, Ts::IntoIter> {
        let mut ys = Vec::new();
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

    #[inline]
    fn grow(&mut self, cap: usize) -> bool {
        if mem::size_of::<T>() > 0 && cap > self.cap {
            let size = match cap.checked_mul(mem::size_of::<T>()) {
                 None => return false,
                 Some(size) => size,
            };
            unsafe {
                let ptr = alloc_or_realloc(*self.ptr, self.cap * mem::size_of::<T>(), size);
                if ptr.is_null() { return false }
                self.ptr = Unique::new(ptr);
            }
        }
        self.cap = cap;
        true
    }
}

impl<T> Drop for Vec<T> {
    #[inline]
    fn drop(&mut self) {
        if self.cap != 0 {
            unsafe {
                for p in &*self { ptr::read(p); }
                dealloc_array(*self.ptr, self.cap);
            }
        }
    }
}

impl<T> Default for Vec<T> {
    #[inline]
    fn default() -> Vec<T> { Vec::new() }
}

impl<T: PartialEq> PartialEq for Vec<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { &self[..] == &other[..] }
}

impl<T: PartialOrd> PartialOrd for Vec<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { PartialOrd::partial_cmp(&self[..], &other[..]) }
}

impl<T: Eq> Eq for Vec<T> {}

impl<T: Ord> Ord for Vec<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering { Ord::cmp(&self[..], &other[..]) }
}

macro_rules! impl_Index {
    ($t: ty) =>
        (impl<T> Index<$t> for Vec<T> {
             type Output = <[T] as Index<$t>>::Output;

             #[inline]
             fn index(&self, k: $t) -> &Self::Output { &self.deref()[k] }
         }

         impl<T> IndexMut<$t> for Vec<T> {
             #[inline]
             fn index_mut(&mut self, k: $t) -> &mut Self::Output { &mut self.deref_mut()[k] }
         })
}

impl_Index!(usize);
impl_Index!(ops::Range<usize>);
impl_Index!(ops::RangeTo<usize>);
impl_Index!(ops::RangeFrom<usize>);
impl_Index!(ops::RangeFull);

impl<T> Deref for Vec<T> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &[T] { unsafe { slice::from_raw_parts(*self.ptr, self.len) } }
}

impl<T> DerefMut for Vec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] { unsafe { slice::from_raw_parts_mut(*self.ptr, self.len) } }
}

impl<T: Hash> Hash for Vec<T> {
    #[inline]
    fn hash<H: Hasher>(&self, h: &mut H) { self[..].hash(h) }
}

impl<T: fmt::Debug> fmt::Debug for Vec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(&self[..], f) }
}

impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        let ptr = *self.ptr;
        let cap = self.cap;
        let len = self.len;
        mem::forget(self);
        IntoIter { mem: ptr, cap: cap, ptr: ptr, len: len }
    }
}

impl<'a, T> IntoIterator for &'a Vec<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> slice::Iter<'a, T> { self.iter() }
}

impl<'a, T> IntoIterator for &'a mut Vec<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(mut self) -> slice::IterMut<'a, T> { self.iter_mut() }
}

pub struct IntoIter<T> {
    mem: *mut T,
    cap: usize,
    ptr: *const T,
    len: usize,
}

unsafe impl<T: Send> Send for IntoIter<T> {}
unsafe impl<T: Sync> Sync for IntoIter<T> {}

impl<T> Drop for IntoIter<T> {
    #[inline]
    fn drop(&mut self) {
        for _ in self.by_ref() {}
        if self.cap != 0 && mem::size_of::<T>() > 0 { unsafe {
            deallocate(self.mem as *mut u8, mem::size_of::<T>()*self.cap, mem::align_of::<T>());
        } }
    }
}

impl<T> Iterator for IntoIter<T> {
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

unsafe fn dealloc_array<T>(ptr: *mut T, n: usize) {
    if mem::size_of::<T>() > 0 { deallocate(ptr as *mut u8, mem::size_of::<T>()*n, mem::align_of::<T>()) }
}

unsafe fn alloc_or_realloc<T>(ptr: *mut T, old_size: usize, new_size: usize) -> *mut T {
    if old_size == 0 {
        allocate(new_size, mem::align_of::<T>()) as *mut T
    } else {
        reallocate(ptr as *mut u8, old_size, new_size, mem::align_of::<T>()) as *mut T
    }
}

#[cfg(test)] mod tests {
    use core::fmt;
    use core::mem;
    use core::ptr::Unique;
    use std;
    use quickcheck as qc;

    use super::*;

    impl<T> From<std::vec::Vec<T>> for Vec<T> {
        fn from(mut xs: std::vec::Vec<T>) -> Vec<T> {
            let ys = Vec {
                ptr: unsafe { Unique::new(xs.as_mut_ptr()) },
                cap: xs.capacity(),
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
