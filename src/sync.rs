#![allow(unused_unsafe)]

use alloc::{Alloc, Layout};
use core::{fmt, marker::Unsize, mem, ptr};
use core::ops::{Deref, CoerceUnsized};
use core::sync::atomic::{AtomicUsize, Ordering as Memord, fence};
use ptr::Shared;

use boxed::Box;

pub struct Arc<T: ?Sized, A: Alloc = ::DefaultA> {
    ptr: Shared<ArcInner<T>>,
    alloc: A,
}

impl<T: ?Sized + fmt::Debug, A: Alloc> fmt::Debug for Arc<T, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(self.deref(), f) }
}

struct ArcInner<T: ?Sized> {
    strong: AtomicUsize,
    weak: AtomicUsize,
    value: T,
}

impl<T: ?Sized, A: Alloc> Arc<T, A> {
    #[inline]
    fn inner(&self) -> &ArcInner<T> { unsafe { self.ptr.as_ref() } }

    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        ptr::drop_in_place(&mut self.ptr.as_mut().value);
        if 1 == self.inner().weak.fetch_sub(1, Memord::Release) {
            fence(Memord::Acquire);
            self.alloc.dealloc(self.ptr.as_ptr().cast(), Layout::for_value(self.ptr.as_ref()));
        }
    }
}

impl<T: ?Sized, A: Alloc + Clone> Arc<T, A> {
    #[inline]
    pub fn downgrade(&self) -> Weak<T, A> {
        self.inner().weak.fetch_add(1, Memord::Acquire);
        Weak { ptr: self.ptr, alloc: self.alloc.clone() }
    }
}

impl<T, A: Alloc> Arc<T, A> {
    #[inline]
    pub fn new_in(a: A, x: T) -> Result<Self, T> {
        let x = Box::new_in(a, ArcInner {
            strong: AtomicUsize::new(1),
            weak: AtomicUsize::new(1),
            value: x,
        }).map_err(|ArcInner { value, .. }| value)?;
        let (ptr, alloc) = unsafe {
            let alloc = ptr::read(&x.alloc);
            let ptr = x.ptr;
            mem::forget(x);
            (ptr, alloc)
        };
        Ok(Arc { ptr: ptr.as_ptr().into(), alloc })
    }
}

impl<T, A: Alloc + Default> Arc<T, A> {
    #[inline]
    pub fn new(x: T) -> Result<Self, T> { Self::new_in(Default::default(), x) }
}

impl<T: ?Sized, A: Alloc> Drop for Arc<T, A> {
    #[inline]
    fn drop(&mut self) {
        if 1 != self.inner().strong.fetch_sub(1, Memord::Release) { return }
        fence(Memord::Acquire);
        unsafe { self.drop_slow() };
    }
}

impl<T: ?Sized, A: Alloc> Deref for Arc<T, A> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T { &self.inner().value }
}

impl<T: ?Sized, A: Alloc + Clone> Clone for Arc<T, A> {
    #[inline]
    fn clone(&self) -> Self {
        if self.inner().strong.fetch_add(1, Memord::Relaxed) > ::core::isize::MAX as _ { unsafe { ::core::intrinsics::abort() } }
        Self { ptr: self.ptr, alloc: self.alloc.clone() }
    }
}

impl<S: ?Sized + Unsize<T>, T: ?Sized, A: Alloc> CoerceUnsized<Arc<T, A>> for Arc<S, A> {}

impl<T: ?Sized, A: Alloc> Unpin for Arc<T, A> {}

pub struct Weak<T: ?Sized, A: Alloc = ::DefaultA> {
    ptr: Shared<ArcInner<T>>,
    alloc: A,
}

impl<T: ?Sized, A: Alloc> Weak<T, A> {
    #[inline]
    fn inner(&self) -> &ArcInner<T> { unsafe { self.ptr.as_ref() } }
}

impl<T: ?Sized + fmt::Debug, A: Alloc> fmt::Debug for Weak<T, A> {
    #[inline]
    fn fmt(&self, _fmt: &mut fmt::Formatter) -> fmt::Result { Ok(()) }
}

impl<T: ?Sized, A: Alloc + Clone> Weak<T, A> {
    #[inline]
    pub fn upgrade(&self) -> Option<Arc<T, A>> {
        let mut n = self.inner().strong.load(Memord::Relaxed);
        loop {
            if 0 == n { return None }
            if n > ::core::isize::MAX as _ { unsafe { core::intrinsics::abort() } }
            match self.inner().strong.compare_exchange_weak(n, n+1, Memord::Relaxed, Memord::Relaxed) {
                Ok(_) => return Some(Arc { ptr: self.ptr, alloc: self.alloc.clone() }),
                Err(m) => n = m,
            }
        }
    }
}

impl<T: ?Sized, A: Alloc + Clone> Clone for Weak<T, A> {
    #[inline]
    fn clone(&self) -> Self {
        if self.inner().weak.fetch_add(1, Memord::Relaxed) > ::core::isize::MAX as _ { unsafe { ::core::intrinsics::abort() } }
        Self { ptr: self.ptr, alloc: self.alloc.clone() }
    }
}

impl<T: ?Sized, A: Alloc> Drop for Weak<T, A> {
    #[inline]
    fn drop(&mut self) {
        if 1 == self.inner().weak.fetch_sub(1, Memord::Release) {
            fence(Memord::Acquire);
            unsafe { self.alloc.dealloc(self.ptr.as_ptr().cast(), Layout::for_value(self.ptr.as_ref())); }
        }
    }
}
