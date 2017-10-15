use core::mem;
use core::ptr;

#[cfg(test)] mod abc;
#[cfg(test)] pub use self::abc::*;

#[inline] pub fn mutate<T, F: FnOnce(T) -> T>(p: &mut T, f: F) { unsafe { ptr::write(p, f(ptr::read(p))) } }

#[inline] pub fn mutate2<S, T, F: FnOnce(S, T) -> (S, T)>(p: &mut S, q: &mut T, f: F) { unsafe {
    let (x, y) = f(ptr::read(p), ptr::read(q));
    ptr::write(p, x);
    ptr::write(q, y);
} }

#[inline] pub fn align_mut_ptr<S, T>(ptr: *mut S) -> *mut T { align(mem::align_of::<T>(), ptr as usize) as *mut T }

#[inline] pub fn align(a: usize, n: usize) -> usize { assert_eq!(0, a&(a-1)); (n+a-1)&!(a-1) }
