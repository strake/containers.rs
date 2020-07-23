//! Type of dynamically-allocated data

#[cfg(any(test, feature = "default_allocator"))]
extern crate default_allocator;

use alloc::*;
use core::{any::Any, fmt, marker::Unsize, mem, ops::{CoerceUnsized, Deref, DerefMut}, ptr};
use ptr::Unique;

/// Pointer to heap-allocated value
#[fundamental]
pub struct Box<T: ?Sized, A: Alloc = ::DefaultA> {
    pub(crate) ptr: Unique<T>,
    pub(crate) alloc: A,
}

impl<T: ?Sized + fmt::Debug, A: Alloc> fmt::Debug for Box<T, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(self.deref(), f) }
}

impl<T, A: Alloc> Box<T, A> {
    #[inline]
    pub fn new_in(mut a: A, x: T) -> Result<Self, T> {
        if 0 == mem::size_of::<T>() { Ok(Unique::empty()) } else { match a.alloc_one() {
            Ok(ptr) => unsafe { ptr::write(ptr.as_ptr().as_ptr(), x); Ok(ptr) },
            Err(_) => Err(x),
        } }.map(|ptr| Box { ptr, alloc: a })
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
    pub unsafe fn from_raw_in(a: A, ptr: Unique<T>) -> Self { Box { ptr, alloc: a } }

    /// Consume a `Box` and return its raw pointer.
    /// The caller owns the memory the `Box` owned. This means the caller must
    /// make sure the `T` is dropped and the memory is deallocated. The proper
    /// way to do so is to call `Box::from_raw` to make a new `Box` of the
    /// pointer.
    #[inline]
    pub unsafe fn into_raw(self) -> Unique<T> { let Self { ptr, alloc: _ } = self; ptr }

    #[inline]
    pub unsafe fn alloc_mut(&mut self) -> &mut A { &mut self.alloc }
}

impl<T: ?Sized, A: Alloc + Default> Box<T, A> {
    /// Make a `Box` of a raw pointer.
    /// After calling this, the `Box` it returns owns the raw pointer.
    /// This means the `Box` destructor will drop the `T` and free the memory.
    /// As allocation technique of `Box` is unspecified, the only valid
    /// argument to this is `Box::into_raw(_)`.
    #[inline]
    pub unsafe fn from_raw(ptr: Unique<T>) -> Self { Self::from_raw_in(A::default(), ptr) }
}

impl<T: ?Sized, A: Alloc> Deref for Box<T, A> {
    type Target = T;

    fn deref(&self) -> &T { unsafe { self.ptr.as_ref() } }
}

impl<T: ?Sized, A: Alloc> DerefMut for Box<T, A> {
    fn deref_mut(&mut self) -> &mut T { unsafe { self.ptr.as_mut() } }
}

impl<T: ?Sized, A: Alloc> Drop for Box<T, A> {
    fn drop(&mut self) { unsafe {
        ptr::drop_in_place(self.ptr.as_ptr().as_ptr());
        if 0 != mem::size_of_val(self.deref()) {
            self.alloc.dealloc(self.ptr.as_ptr().cast(), Layout::for_value(self.ptr.as_ref()));
        }
    } }
}

impl<S: ?Sized + Unsize<T>, T: ?Sized, A: Alloc> CoerceUnsized<Box<T, A>> for Box<S, A> {}

impl<T: ?Sized, A: Alloc> Unpin for Box<T, A> {}

impl Box<dyn Any> {
    #[inline]
    pub fn downcast<T: Any>(self) -> Result<Box<T>, Self> {
        if self.is::<T>() {
            let Box { ptr, alloc } = self;
            Ok(Box { alloc, ptr: ptr.as_ptr().cast().into() })
        } else { Err(self) }
    }
}

#[cfg(test)]
mod tests {
    extern crate default_allocator;

    use core::ops::Deref;
    use core::{mem, ptr};

    type Box<T> = super::Box<T, default_allocator::Heap>;

    #[test]
    fn drop() {
        struct T<'a>(&'a mut bool);
        impl<'a> Drop for T<'a> {
            fn drop(&mut self) { *self.0 = true; }
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
        let _ = b.deref();
        mem::forget(b);
    }
}
