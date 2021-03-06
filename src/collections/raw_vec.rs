use alloc::*;
use core::{marker::PhantomData, mem::{self, MaybeUninit}, ptr::NonNull, slice};
use ptr::Unique;

/// Raw growable array, a low-level utility type to allocate a buffer of memory and not need to worry about edge cases
///
/// It never inspects the memory it holds; it merely allocates enough memory to hold however many elements, and deallocates on `drop` but not `drop`s its contents.
#[allow(missing_debug_implementations)]
pub struct RawVec<T, A: Alloc = crate::DefaultA> {
    pub(crate) ptr: Unique<T>,
    pub(crate) cap: usize,
    pub(crate) alloc: A
}

impl<T, A: Alloc> RawVec<T, A> {
    /// Make a new array.
    #[inline]
    pub const fn new_in(a: A) -> Self { RawVec { ptr: Unique::empty(), cap: 0, alloc: a } }

    /// Make a new array with enough room to hold at least `cap` elements.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline]
    pub fn with_capacity_in(mut a: A, cap: usize) -> Option<Self> {
        if mem::size_of::<T>() == 0 {
            Some(RawVec { ptr: Unique::empty(), cap, alloc: a })
        } else if cap == 0 {
            Some(RawVec::new_in(a))
        } else { a.alloc_array(cap).ok().map(|(ptr, cap)| RawVec { ptr, cap, alloc: a }) }
    }

    /// Return number of elements array can hold before reallocation.
    #[inline]
    pub fn capacity(&self) -> usize { self.cap }

    #[inline]
    pub unsafe fn storage_mut(&mut self) -> &mut [T] {
        slice::from_raw_parts_mut(self.ptr.as_ptr().as_ptr(), self.cap)
    }

    #[inline]
    pub unsafe fn storage(&self) -> &[T] {
        slice::from_raw_parts(self.ptr.as_ptr().as_ptr(), self.cap)
    }

    #[inline]
    pub fn ptr(&self) -> *mut T { self.ptr.as_ptr().as_ptr() as *const T as *mut T }

    /// Make sure the array has enough room for at least `n_more` more elements, assuming it
    /// already holds `n`, reallocating if need be.
    ///
    /// # Failures
    ///
    /// Returns `false` if allocation fails, `true` otherwise.
    pub fn reserve(&mut self, n: usize, n_more: usize) -> bool {
        if mem::size_of::<T>() > 0 && self.cap - n < n_more {
            self.grow(match n.checked_add(n_more).and_then(|n| n.checked_next_power_of_two()) {
                          None => return false,
                          Some(cap) => cap,
                      })
        } else { true }
    }

    /// Relinquish memory so capacity = `n`.
    pub fn relinquish(&mut self, n: usize) -> bool {
        if self.cap == n { return true }
        if mem::size_of::<T>() > 0 { unsafe {
            if 0 == n { let _ = self.alloc.dealloc_array(self.ptr, self.cap); }
            else { match self.alloc.realloc_array(self.ptr, self.cap, n) {
                Ok((ptr, _)) => self.ptr = ptr,
                Err(_) => return false,
            } }
        } }
        self.cap = n;
        true
    }

    pub fn grow(&mut self, cap: usize) -> bool {
        if mem::size_of::<T>() > 0 && cap > self.cap {
            unsafe { match alloc_or_realloc(&mut self.alloc, self.ptr, self.cap, cap) {
                Ok((ptr, cap)) => { self.ptr = ptr; self.cap = cap; },
                Err(_) => return false,
            } }
        }
        true
    }

    #[inline]
    pub unsafe fn from_raw_parts_in(alloc: A, ptr: *mut T, cap: usize) -> Self {
        RawVec { ptr: Unique::new_unchecked(ptr), cap, alloc }
    }

    #[inline]
    pub unsafe fn alloc_mut(&mut self) -> &mut A { &mut self.alloc }
}

#[derive(Debug)]
pub struct FixedStorage<'a, T: 'a>(PhantomData<&'a mut [T]>);
unsafe impl<'a, T> Alloc for FixedStorage<'a, T> {
    #[inline]
    unsafe fn alloc(&mut self, _: Layout) -> Result<NonNull<u8>, AllocErr> { Err(AllocErr::Unsupported { details: "" }) }

    #[inline]
    unsafe fn dealloc(&mut self, _: NonNull<u8>, _: Layout) {}
}

impl<'a, T> RawVec<T, FixedStorage<'a, T>> {
    #[inline]
    pub const fn from_storage(xs: &'a mut [MaybeUninit<T>]) -> Self { unsafe {
        RawVec { ptr: Unique::new_unchecked(xs.as_ptr() as *const T as *mut T), cap: xs.len(),
                 alloc: FixedStorage(PhantomData) }
    } }
}

impl<'a, T: 'a> RawVec<T, FixedStorage<'a, T>> {
    pub const empty: Self = RawVec { ptr: Unique::empty(), cap: 0,
                                     alloc: FixedStorage(PhantomData) };
}

impl<T, A: Alloc + Default> RawVec<T, A> {
    /// Make a new array.
    #[inline]
    pub fn new() -> Self { Self::new_in(A::default()) }

    #[inline]
    pub unsafe fn from_raw_parts(ptr: *mut T, cap: usize) -> Self {
        Self::from_raw_parts_in(A::default(), ptr, cap)
    }
}

unsafe impl<#[may_dangle] T, A: Alloc> Drop for RawVec<T, A> {
    #[inline]
    fn drop(&mut self) {
        unsafe { if self.cap != 0 { let _ = self.alloc.dealloc_array(self.ptr, self.cap); } }
    }
}

impl<T, A: Alloc + Default> Default for RawVec<T, A> {
    #[inline]
    fn default() -> Self { RawVec::new() }
}

#[inline]
unsafe fn alloc_or_realloc<T, A: Alloc>(a: &mut A, ptr: Unique<T>, m: usize, n: usize) -> Result<(Unique<T>, usize), AllocErr> {
    if 0 == m { a.alloc_array(n) } else { a.realloc_array(ptr, m, n) }
}
