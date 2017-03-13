//! Type of heap-allocated data

use alloc::heap::*;
use core::mem;
use core::ops::{ Deref, DerefMut };
use core::ptr::{ self, Unique };

/// Pointer to heap-allocated value
pub struct Box<T: ?Sized>(Unique<T>);

impl<T> Box<T> {
    /// Allocate memory on the heap and then move `x` into it.
    #[inline]
    pub fn new(x: T) -> Option<Self> {
        unsafe {
            let p = allocate(mem::size_of::<T>(), mem::align_of::<T>()) as *mut T;
            if p.is_null() { return None };
            ptr::write(p, x);
            Some(Box(Unique::new(p)))
        }
    }
}

impl<T: ?Sized> Box<T> {
    /// Make a `Box` of a raw pointer.
    /// After calling this, the `Box` it returns owns the raw pointer.
    /// This means the `Box` destructor will drop the `T` and free the memory.
    /// As allocation technique of `Box` is unspecified, the only valid
    /// argument to this is `Box::into_raw(_)`.
    #[inline]
    pub unsafe fn from_raw(ptr: *mut T) -> Self { Box(Unique::new(ptr)) }

    /// Consume a `Box` and return its raw pointer.
    /// The caller owns the memory the `Box` owned. This means the caller must
    /// make sure the `T` is dropped and the memory is deallocated. The proper
    /// way to do so is to call `Box::from_raw` to make a new `Box` of the
    /// pointer.
    #[inline]
    pub unsafe fn into_raw(self) -> *mut T { *self.0 }
}

impl<T: ?Sized> Deref for Box<T> {
    type Target = T;

    fn deref(&self) -> &T { unsafe { self.0.get() } }
}

impl<T: ?Sized> DerefMut for Box<T> {
    fn deref_mut(&mut self) -> &mut T { unsafe { self.0.get_mut() } }
}

impl<T: ?Sized> Drop for Box<T> {
    fn drop(&mut self) {
        let ptr = *self.0;
        unsafe {
            ptr::drop_in_place(ptr);
            deallocate(ptr as *mut u8, mem::size_of_val(&*ptr), mem::align_of_val(&*ptr));
        }
    }
}

#[cfg(test)] mod tests {
    use super::*;

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

    #[quickcheck]
    fn keeps_value() {
        let mut b = Box::new(0).unwrap();
        assert_eq!(0, *b);
        *b += 1;
        assert_eq!(1, *b);
    }
}
