use alloc::*;
use core::{marker::PhantomData, mem, ptr::NonNull, slice};
use slot::Slot;
use ::ptr::Unique;

/// Raw growable array, a low-level utility type to allocate a buffer of memory and not need to worry about edge cases
///
/// It never inspects the memory it holds; it merely allocates enough memory to hold however many elements, and deallocates on `drop` but not `drop`s its contents.
#[allow(missing_debug_implementations)]
pub struct RawVec<T, A: Alloc = ::DefaultA> {
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
    #[inline] pub fn capacity(&self) -> usize { self.cap }

    #[inline] pub unsafe fn storage_mut(&mut self) -> &mut [T] {
        slice::from_raw_parts_mut(self.ptr.as_ptr().as_ptr(), self.cap)
    }

    #[inline] pub unsafe fn storage(&self) -> &[T] {
        slice::from_raw_parts(self.ptr.as_ptr().as_ptr(), self.cap)
    }

    #[inline] pub fn ptr(&self) -> *mut T { self.ptr.as_ptr().as_ptr() as *const T as *mut T }

    /// Make sure the array has enough room for at least `n_more` more elements, assuming it
    /// already holds `n`, reallocating if need be.
    ///
    /// # Failures
    ///
    /// Returns `false` if allocation fails, `true` otherwise.
    #[inline]
    pub fn reserve(&mut self, n: usize, n_more: usize) -> bool {
        0 == mem::size_of::<T>() ||
        unsafe { self.as_raw_raw_mut().reserve(Layout::new::<T>(), n, n_more) }
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

    #[inline]
    pub fn grow(&mut self, cap: usize) -> bool {
        0 == mem::size_of::<T>() ||
        unsafe { self.as_raw_raw_mut().grow(Layout::new::<T>(), cap) }
    }

    #[inline]
    pub unsafe fn from_raw_parts_in(alloc: A, ptr: *mut T, cap: usize) -> Self {
        RawVec { ptr: Unique::new_unchecked(ptr), cap, alloc }
    }

    #[inline]
    pub unsafe fn alloc_mut(&mut self) -> &mut A { &mut self.alloc }

    #[inline]
    unsafe fn as_raw_raw_mut(&mut self) -> &mut RawRawVec<A> { mem::transmute(self) }
}

struct RawRawVec<A: Alloc> {
    ptr: NonNull<u8>,
    cap: usize,
    alloc: A
}

impl<A: Alloc> RawRawVec<A> {
    fn reserve(&mut self, layout: Layout, n: usize, n_more: usize) -> bool {
        self.cap - n >= n_more ||
        self.grow(layout, match n.checked_add(n_more).and_then(|n| n.checked_next_power_of_two()) {
                      None => return false,
                      Some(cap) => cap,
                  })
    }

    fn grow(&mut self, layout: Layout, cap: usize) -> bool {
        if cap > self.cap {
            unsafe { match realloc_array_layout(&mut self.alloc, layout, self.ptr, self.cap, cap) {
                Some((ptr, cap)) => { self.ptr = ptr; self.cap = cap; },
                None => return false,
            } }
        }
        true
    }
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
    pub const fn from_storage(xs: &'a mut [Slot<T>]) -> Self { unsafe {
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

impl<T, A: Alloc> Drop for RawVec<T, A> {
    #[inline]
    fn drop(&mut self) {
        unsafe { if self.cap != 0 { let _ = self.alloc.dealloc_array(self.ptr, self.cap); } }
    }
}

impl<T, A: Alloc + Default> Default for RawVec<T, A> {
    #[inline]
    fn default() -> Self { RawVec::new() }
}

unsafe fn realloc_array_layout<A: Alloc>(a: &mut A, layout: Layout, ptr: NonNull<u8>, m: usize, n: usize) -> Option<(NonNull<u8>, usize)> {
    let new_array_layout = layout.repeat(n)?.0;
    if 0 == m { a.alloc_excess(new_array_layout) } else {
        let old_array_layout = layout.repeat(m)?.0;
        a.realloc_excess(ptr, old_array_layout, new_array_layout.size())
    }.ok().map(|Excess(p, n)| (p, n / layout.size()))
}
