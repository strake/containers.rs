use abort::abort;
use alloc::{Alloc, Layout};
use core::{fmt, marker::Unsize, mem, ptr::{self, NonNull}};
use core::ops::{Deref, CoerceUnsized};
use core::sync::atomic::{AtomicUsize, Ordering as Memord, fence};
use fallible::TryClone;
use ::ptr::Shared;

use crate::boxed::Box;

pub struct Arc<T: ?Sized, A: Alloc = crate::DefaultA> {
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

unsafe impl<T: ?Sized + Sync + Send> Send for ArcInner<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for ArcInner<T> {}

impl<T: ?Sized, A: Alloc> Arc<T, A> {
    #[inline]
    fn inner(&self) -> &ArcInner<T> { unsafe { self.ptr.as_ref() } }

    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        // Destroy the data now, even tho we may not free the box allocation itself
        // (weak pointers may yet be lying about).
        ptr::drop_in_place(&mut self.ptr.as_mut().value);
        if 1 == self.inner().weak.fetch_sub(1, Memord::Release) {
            fence(Memord::Acquire);
            self.alloc.dealloc(self.ptr.as_ptr().cast(), Layout::for_value(self.ptr.as_ref()));
        }
    }

    #[inline]
    pub fn ptr_eq(this: &Self, that: &Self) -> bool { this.ptr.as_ptr() == that.ptr.as_ptr() }

    /// Returns a mutable reference into the given `Arc`, if there are
    /// no other `Arc` or [`Weak`] pointers to the same allocation.
    ///
    /// Returns [`None`] otherwise, because it is not safe to
    /// mutate a shared value.
    ///
    /// See also [`make_mut`][make_mut], which will [`clone`][clone]
    /// the inner value when there are other pointers.
    ///
    /// [make_mut]: Arc::make_mut
    /// [clone]: Clone::clone
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    ///
    /// let mut x = Arc::new(3);
    /// *Arc::get_mut(&mut x).unwrap() = 4;
    /// assert_eq!(*x, 4);
    ///
    /// let _y = Arc::clone(&x);
    /// assert!(Arc::get_mut(&mut x).is_none());
    /// ```
    #[inline]
    pub fn get_mut(x: &mut Self) -> Option<&mut T> {
        if x.is_unique() {
            // This unsafety is ok because we're guaranteed that the pointer
            // returned is the *only* pointer that will ever be returned to T. Our
            // reference count is guaranteed to be 1 at this point, and we required
            // the Arc itself to be `mut`, so we're returning the only possible
            // reference to the inner data.
            unsafe { Some(Self::get_mut_unchecked(x)) }
        } else {
            None
        }
    }

    /// Returns a mutable reference into the given `Arc`, with no check.
    ///
    /// See also [`get_mut`], which is safe and does appropriate checks.
    ///
    /// [`get_mut`]: Arc::get_mut
    ///
    /// # Safety
    ///
    /// Any other `Arc` or [`Weak`] pointers to the same allocation must not be dereferenced
    /// for the duration of the returned borrow.
    /// This is trivially the case if no such pointers exist,
    /// for example immediately after `Arc::new`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(get_mut_unchecked)]
    ///
    /// use std::sync::Arc;
    ///
    /// let mut x = Arc::new(String::new());
    /// unsafe {
    ///     Arc::get_mut_unchecked(&mut x).push_str("foo")
    /// }
    /// assert_eq!(*x, "foo");
    /// ```
    #[inline]
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut T {
        // We are careful to *not* create a reference covering the "count" fields, as
        // this would alias with concurrent access to the reference counts (e.g. by `Weak`).
        &mut (*this.ptr.as_ptr().as_ptr()).value
    }

    /// Determine whether this is the unique reference (including weak refs) to its referent.
    ///
    /// Note: requires locking the weak ref count.
    fn is_unique(&mut self) -> bool {
        // lock the weak pointer count if we appear to be the sole weak pointer
        // holder.
        //
        // The acquire label here ensures a happens-before relationship with any
        // writes to `strong` (in particular in `Weak::upgrade`) prior to decrements
        // of the `weak` count (via `Weak::drop`, which uses release).  If the upgraded
        // weak ref was never dropped, the CAS here will fail so we do not care to synchronize.
        if self.inner().weak.compare_exchange(1, usize::MAX, Memord::Acquire, Memord::Relaxed).is_ok() {
            // This needs to be an `Acquire` to synchronize with the decrement of the `strong`
            // counter in `drop` -- the only access that happens when any but the last reference
            // is being dropped.
            let unique = self.inner().strong.load(Memord::Acquire) == 1;

            // The release write here synchronizes with a read in `downgrade`,
            // effectively preventing the above read of `strong` from happening
            // after the write.
            self.inner().weak.store(1, Memord::Release); // release the lock
            unique
        } else {
            false
        }
    }
}

impl<T: TryClone, A: Alloc + Clone> Arc<T, A> {
    #[inline]
    pub fn make_mut(&mut self) -> Result<&mut T, Option<<T as TryClone>::Error>> {
        // Note that we hold both a strong reference and a weak reference.
        // Thus, releasing our strong reference only will not, by itself, cause
        // the memory to be deallocated.
        //
        // Use Acquire to ensure that we see any writes to `weak` that happen
        // before release writes (i.e., decrements) to `strong`. Since we hold a
        // weak count, there's no chance the ArcInner itself could be
        // deallocated.
        if self.inner().strong.compare_exchange(1, 0, Memord::Acquire, Memord::Relaxed).is_err() {
            // Another strong pointer exists, so we must clone.
            // Pre-allocate memory to allow writing the cloned value directly.
            let mut arc = Place::new_in(self.alloc.clone()).map_err(|()| None)?;
            unsafe {
                let data = Place::<T, _>::get_mut_unchecked(&mut arc);
                ptr::write(data, T::try_clone(self.deref())?);
                *self = arc.assume_init();
            }
        } else if self.inner().weak.load(Memord::Relaxed) != 1 {
            // Relaxed suffices in the above because this is fundamentally an
            // optimization: we are always racing with weak pointers being
            // dropped. Worst case, we end up allocated a new Arc unnecessarily.

            // We removed the last strong ref, but there are additional weak
            // refs remaining. We'll move the contents to a new Arc, and
            // invalidate the other weak refs.

            // Note that it is not possible for the read of `weak` to yield
            // usize::MAX (i.e., locked), since the weak count can only be
            // locked by a thread with a strong reference.

            // Materialize our own implicit weak pointer, so that it can clean
            // up the ArcInner as needed.
            let _weak = Weak { ptr: self.ptr.as_ptr() };

            // Can just steal the data, all that's left is Weaks
            let mut arc = Place::new_in(self.alloc.clone()).map_err(|()| None)?;
            unsafe {
                let data = Place::<T, _>::get_mut_unchecked(&mut arc);
                (data as *mut T).copy_from_nonoverlapping(&**self, 1);
                ptr::write(self, arc.assume_init());
            }
        } else {
            // We were the sole reference of either kind; bump back up the
            // strong ref count.
            self.inner().strong.store(1, Memord::Release);
        }

        // As with `get_mut()`, the unsafety is ok because our reference was
        // either unique to begin with, or became one upon cloning the contents.
        unsafe { Ok(Self::get_mut_unchecked(self)) }
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
        if self.inner().strong.fetch_add(1, Memord::Relaxed) > ::core::isize::MAX as _ { abort() }
        Self { ptr: self.ptr, alloc: self.alloc.clone() }
    }
}

impl<S: ?Sized + Unsize<T>, T: ?Sized, A: Alloc> CoerceUnsized<Arc<T, A>> for Arc<S, A> {}

impl<T: ?Sized, A: Alloc> Unpin for Arc<T, A> {}

pub struct Place<T: ?Sized, A: Alloc = crate::DefaultA>(crate::boxed::Place<ArcInner<T>, A>);

impl<T: ?Sized, A: Alloc> fmt::Debug for Place<T, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt("<place>", f) }
}

impl<T, A: Alloc> Place<T, A> {
    #[inline]
    pub fn emplace(self, x: T) -> Arc<T, A> { unsafe {
        ptr::write(self.0.ptr.as_ptr().as_ptr(), ArcInner {
            strong: AtomicUsize::new(1),
            weak: AtomicUsize::new(1),
            value: x,
        });
        self.assume_init()
    } }

    #[inline]
    pub fn new_in(a: A) -> Result<Self, ()> {
        crate::boxed::Place::new_in(a).map(Place)
    }
}

impl<T, A: Alloc + Default> Place<T, A> {
    #[inline]
    pub fn new() -> Result<Self, ()> { Self::new_in(A::default()) }
}

impl<T: ?Sized, A: Alloc> Place<T, A> {
    #[inline]
    pub fn as_mut_ptr(&mut self) -> NonNull<T> { unsafe {
        NonNull::new_unchecked(memoffset::raw_field!(self.0.ptr.as_ptr().as_ptr(), ArcInner<T>, value) as _)
    } }

    #[inline]
    pub unsafe fn assume_init(self) -> Arc<T, A> {
        Arc { ptr: self.0.ptr.into(), alloc: self.0.alloc }
    }

    #[inline]
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut T {
        // We are careful to *not* create a reference covering the "count" fields, as
        // this would alias with concurrent access to the reference counts (e.g. by `Weak`).
        &mut (*this.0.ptr.as_ptr().as_ptr()).value
    }
}

pub struct Weak<T: ?Sized> {
    // This is a `NonNull` to allow optimizing the size of this type in enums,
    // but it is not necessarily a valid pointer.
    // `Weak::new` sets this to `usize::MAX` so that it doesn’t need
    // to allocate space on the heap.  That's not a value a real pointer
    // will ever have because RcBox has alignment at least 2.
    // This is only possible when `T: Sized`; unsized `T` never dangle.
    ptr: NonNull<ArcInner<T>>,
}

unsafe impl<T: ?Sized + Sync + Send> Send for Weak<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Weak<T> {}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Weak<U>> for Weak<T> {}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Weak<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(Weak)")
    }
}

impl<T> Weak<T> {
    /// Constructs a new `Weak<T>`, without allocating any memory.
    /// Calling [`upgrade`] on the return value always gives [`None`].
    ///
    /// [`upgrade`]: Weak::upgrade
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Weak;
    ///
    /// let empty: Weak<i64> = Weak::new();
    /// assert!(empty.upgrade().is_none());
    /// ```
    #[must_use]
    pub fn new() -> Weak<T> {
        Weak { ptr: NonNull::new(usize::MAX as _).expect("MAX is not 0") }
    }
}

impl<T: ?Sized> Weak<T> {
    /// Returns `None` when the pointer is dangling and there is no allocated `ArcInner`,
    /// (i.e., when this `Weak` was created by `Weak::new`).
    #[inline]
    fn inner(&self) -> Option<WeakInner<'_>> {
        if usize::MAX == self.ptr.as_ptr() as *mut () as _ {
            None
        } else {
            // We are careful to *not* create a reference covering the "data" field, as
            // the field may be mutated concurrently (for example, if the last `Arc`
            // is dropped, the data field will be dropped in-place).
            Some(unsafe {
                let ptr = self.ptr.as_ptr();
                WeakInner { strong: &(*ptr).strong, weak: &(*ptr).weak }
            })
        }
    }
}

/// Helper type to allow accessing the reference counts without
/// making any assertions about the data field.
struct WeakInner<'a> {
    weak: &'a AtomicUsize,
    strong: &'a AtomicUsize,
}

impl<T: ?Sized> Clone for Weak<T> {
    /// Makes a clone of the `Weak` pointer that points to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::{Arc, Weak};
    ///
    /// let weak_five = Arc::downgrade(&Arc::new(5));
    ///
    /// let _ = Weak::clone(&weak_five);
    /// ```
    #[inline]
    fn clone(&self) -> Weak<T> {
        let inner = if let Some(inner) = self.inner() {
            inner
        } else {
            return Weak { ptr: self.ptr };
        };
        // See comments in Arc::clone() for why this is relaxed.  This can use a
        // fetch_add (ignoring the lock) because the weak count is only locked
        // where are *no other* weak pointers in existence. (So we can't be
        // running this code in that case).
        let old_size = inner.weak.fetch_add(1, Memord::Relaxed);

        // See comments in Arc::clone() for why we do this (for mem::forget).
        if old_size > ::core::isize::MAX as _ { abort() }

        Weak { ptr: self.ptr }
    }
}

impl<T> Default for Weak<T> {
    /// Constructs a new `Weak<T>`, without allocating memory.
    /// Calling [`upgrade`] on the return value always
    /// gives [`None`].
    ///
    /// [`upgrade`]: Weak::upgrade
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Weak;
    ///
    /// let empty: Weak<i64> = Default::default();
    /// assert!(empty.upgrade().is_none());
    /// ```
    fn default() -> Weak<T> {
        Weak::new()
    }
}
