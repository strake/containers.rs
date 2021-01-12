use abort::abort;
use alloc::{Alloc, Layout};
use core::{cell::Cell, fmt, marker::Unsize, ops::{CoerceUnsized, Deref}, ptr::{self, NonNull}};

use crate::boxed::Box;

pub struct Rc<T: ?Sized, A: Alloc = crate::DefaultA> {
    ptr: NonNull<RcInner<T>>,
    alloc: A,
}

#[derive(Debug)]
struct RcInner<T: ?Sized> {
    strong: Cell<usize>,
    weak: Cell<usize>,
    value: T,
}

impl<T, A: Alloc> Rc<T, A> {
    #[inline]
    pub fn new_in(alloc: A, x: T) -> Result<Self, T> {
        let x = Box::new_in(alloc, RcInner {
            strong: Cell::new(1),
            weak: Cell::new(1),
            value: x,
        }).map_err(|RcInner { value, .. }| value)?;
        unsafe {
            let alloc = ptr::read(&x.alloc);
            Ok(Self { ptr: x.into_raw().as_ptr(), alloc })
        }
    }
}

impl<T, A: Alloc + Default> Rc<T, A> {
    #[inline]
    pub fn new(x: T) -> Result<Self, T> { Self::new_in(A::default(), x) }
}

impl<T: ?Sized, A: Alloc> Rc<T, A> {
    #[cfg(foobar)]
    #[inline]
    pub unsafe fn emplace_new_in<Init: FnOnce(NonNull<T>) -> Result<(), E>, E>(a: A, layout: Layout, init: Init) -> Result<Self, Option<E>> {
        let layout = Layout::new::<RcInner<()>>().extend(layout).map_err(|_| None)?;
        match a.alloc(layout).map(|ptr| ptr as NonNull<RcInner<T>>) {
            Ok(ptr) => init(ptr as _).map(|()| ptr.into()).map_err(Some),
            Err(_) => Err(None),
        }.map(|ptr| Box { ptr, alloc: a })
    }

    #[inline]
    fn inner(&self) -> &RcInner<T> { unsafe { self.ptr.as_ref() } }

    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        ptr::drop_in_place(&mut self.ptr.as_mut().value);
        let k = self.inner().weak.get();
        self.inner().weak.set(k - 1);
        if 1 == k {
            self.alloc.dealloc(self.ptr.cast(), Layout::for_value(self.ptr.as_ref()));
        }
    }
}

impl<T: ?Sized, A: Alloc> Deref for Rc<T, A> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T { &self.inner().value }
}

impl<T: ?Sized, A: Alloc + Clone> Clone for Rc<T, A> {
    #[inline]
    fn clone(&self) -> Self {
        const MAX_REFCOUNT: usize = isize::max_value() as _;
        let old_size = self.inner().strong.get();
        self.inner().strong.set(old_size + 1);
        if old_size > MAX_REFCOUNT { abort() }
        Self { ptr: self.ptr, alloc: self.alloc.clone() }
    }
}

impl<T: ?Sized, A: Alloc> Drop for Rc<T, A> {
    #[inline]
    fn drop(&mut self) {
        let k = self.inner().strong.get();
        self.inner().strong.set(k - 1);
        if 1 != k { return }
        unsafe { self.drop_slow() }
    }
}

impl<T: ?Sized + fmt::Debug, A: Alloc> fmt::Debug for Rc<T, A> {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.deref().fmt(fmt)
    }
}

impl<S: ?Sized + Unsize<T>, T: ?Sized, A: Alloc> CoerceUnsized<Rc<T, A>> for Rc<S, A> {}

impl<T: ?Sized, A: Alloc> Unpin for Rc<T, A> {}
