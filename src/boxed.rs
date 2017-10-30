//! Type of dynamically-allocated data

#[cfg(any(test, feature = "default_allocator"))]
extern crate default_allocator;

use alloc::*;
use core::mem;
use core::ops::{ Deref, DerefMut };
use core::ptr::{ self, Unique };

/// Pointer to heap-allocated value
#[cfg_attr(not(test), lang = "owned_box")]
#[fundamental]
pub struct Box<T: ?Sized, A: Alloc = ::DefaultA> {
    ptr: Unique<T>,
    alloc: A,
}

impl<T, A: Alloc> Box<T, A> {
    #[inline]
    pub fn new_in(mut a: A, x: T) -> Result<Self, T> {
        if 0 == mem::size_of::<T>() { Ok(Unique::empty()) } else { match a.alloc_one() {
            Ok(ptr) => unsafe { ptr::write(ptr.as_ptr(), x); Ok(ptr) },
            Err(_) => Err(x),
        } }.map(|ptr| Box { ptr: ptr, alloc: a })
    }
}

impl<T, A: Alloc + Default> Box<T, A> {
    /// Allocate memory on the heap and then move `x` into it.
    #[inline]
    pub fn new(x: T) -> Result<Self, T> { Self::new_in(A::default(), x) }
}

impl<T: ?Sized, A: Alloc> Box<T, A> {
    /// Make a `Box` of a raw pointer.
    /// After calling this, the `Box` it returns owns the raw pointer.
    /// This means the `Box` destructor will drop the `T` and free the memory.
    /// As allocation technique of `Box` is unspecified, the only valid
    /// argument to this is `Box::into_raw(_)`.
    #[inline]
    pub unsafe fn from_raw_in(a: A, ptr: *mut T) -> Self { Box { ptr: Unique::new_unchecked(ptr), alloc: a } }

    /// Consume a `Box` and return its raw pointer.
    /// The caller owns the memory the `Box` owned. This means the caller must
    /// make sure the `T` is dropped and the memory is deallocated. The proper
    /// way to do so is to call `Box::from_raw` to make a new `Box` of the
    /// pointer.
    #[inline]
    pub unsafe fn into_raw(self) -> *mut T { self.ptr.as_ptr() }
}

impl<T: ?Sized, A: Alloc + Default> Box<T, A> {
    /// Make a `Box` of a raw pointer.
    /// After calling this, the `Box` it returns owns the raw pointer.
    /// This means the `Box` destructor will drop the `T` and free the memory.
    /// As allocation technique of `Box` is unspecified, the only valid
    /// argument to this is `Box::into_raw(_)`.
    #[inline]
    pub unsafe fn from_raw(ptr: *mut T) -> Self { Self::from_raw_in(A::default(), ptr) }
}

impl<T: ?Sized, A: Alloc> Deref for Box<T, A> {
    type Target = T;

    fn deref(&self) -> &T { unsafe { self.ptr.as_ref() } }
}

impl<T: ?Sized, A: Alloc> DerefMut for Box<T, A> {
    fn deref_mut(&mut self) -> &mut T { unsafe { self.ptr.as_mut() } }
}

impl<T: ?Sized, A: Alloc> Drop for Box<T, A> {
    fn drop(&mut self) {
        if 0 != mem::size_of_val(self.deref()) { unsafe {
            ptr::drop_in_place(self.ptr.as_ptr());
            self.alloc.dealloc(self.ptr.as_ptr() as _, Layout::for_value(self.ptr.as_ref()));
        } }
    }
}

#[cfg(test)] mod tests {
    extern crate default_allocator;

    use core::{mem, ptr};
    use core::ops::Deref;

    type Box<T> = super::Box<T, default_allocator::Heap>;

    #[test]
    fn drop() {
        struct T<'a>(&'a mut bool);
        impl<'a> Drop for T<'a> {
            fn drop(&mut self) {
                *self.0 = true;
            }
        }

        let mut c = false;
        {
            let _ = Box::new(T(&mut c));
        }
        assert!(c);
    }

    #[test]
    fn keeps_value() {
        let mut b = Box::new(0).unwrap();
        assert_eq!(0, *b);
        *b += 1;
        assert_eq!(1, *b);
    }

    #[test]
    fn zero_size() {
        let b = Box::new(()).unwrap();
        assert_eq!((), *b);
        assert_ne!(ptr::null(), &b as *const _);
        b.deref();
        mem::forget(b);
    }
}
