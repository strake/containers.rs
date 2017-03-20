use alloc::heap::{ EMPTY, allocate, reallocate, deallocate };
use core::mem;
use core::ptr::Unique;
use core::slice;

/// Raw growable array
pub struct RawVec<T> {
    ptr: Unique<T>,
    cap: usize,
}

impl<T> RawVec<T> {
    /// Make a new array.
    #[inline]
    pub fn new() -> Self {
        unsafe { RawVec { ptr: Unique::new(EMPTY as *mut T), cap: 0 } }
    }

    /// Make a new array with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline]
    pub fn with_capacity(cap: usize) -> Option<Self> {
        if mem::size_of::<T>() == 0 {
            Some(unsafe { RawVec { ptr: Unique::new(EMPTY as *mut T), cap: cap } })
        } else if cap == 0 {
            Some(RawVec::new())
        } else {
            let size = tryOpt!(cap.checked_mul(mem::size_of::<T>()));
            let ptr = unsafe { allocate(size, mem::align_of::<T>()) as *mut T };
            if ptr.is_null() { None }
            else { Some(unsafe { RawVec { ptr: Unique::new(ptr), cap: cap } }) }
        }
    }

    /// Return number of elements array can hold before reallocation.
    #[inline] pub fn capacity(&self) -> usize { self.cap }

    #[inline] pub unsafe fn storage_mut(&mut self) -> &mut [T] {
        slice::from_raw_parts_mut(*self.ptr, self.cap)
    }

    #[inline] pub fn ptr(&self) -> *mut T { unsafe { self.ptr.get() as *const T as *mut T } }

    #[cfg(test)]
    #[inline] pub unsafe fn from_raw_parts(ptr: *mut T, cap: usize) -> Self {
        RawVec { ptr: Unique::new(ptr), cap: cap }
    }

    /// Make sure the array has enough room for at least `n_more` more elements, assuming it
    /// already holds `n`, reallocating if need be.
    ///
    /// # Failures
    ///
    /// Returns `false` if allocation fails, `true` otherwise.
    #[inline]
    pub fn reserve(&mut self, n: usize, n_more: usize) -> bool {
        if self.cap - n < n_more {
            self.grow(match n.checked_add(n_more).and_then(|n| n.checked_next_power_of_two()) {
                          None => return false,
                          Some(cap) => cap,
                      })
        } else { true }
    }

    /// Relinquish memory so capacity = `n`.
    #[inline]
    pub fn relinquish(&mut self, n: usize) -> bool {
        if self.cap == n { return true }
        if mem::size_of::<T>() > 0 { unsafe {
            if 0 == n { dealloc_array(*self.ptr, self.cap) }
            else {
                let ptr = reallocate(*self.ptr as *mut u8,
                                     mem::size_of::<T>()*self.cap,
                                     mem::size_of::<T>()*n,
                                     mem::align_of::<T>()) as *mut T;
                if ptr.is_null() { return false; }
                self.ptr = Unique::new(ptr);
            }
        } }
        self.cap = n;
        true
    }

    #[inline]
    pub fn grow(&mut self, cap: usize) -> bool {
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

impl<T> Drop for RawVec<T> {
    #[inline]
    fn drop(&mut self) {
        unsafe { if self.cap != 0 { dealloc_array(*self.ptr, self.cap); } }
    }
}

impl<T> Default for RawVec<T> {
    #[inline]
    fn default() -> RawVec<T> { RawVec::new() }
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
