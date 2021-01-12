use core::mem;
use core::ptr;

#[cfg(test)] mod abc;
#[cfg(test)] pub use self::abc::*;

#[inline]
pub fn mutate<T, F: FnOnce(T) -> T>(p: &mut T, f: F) { unsafe {
    let x = ptr::read(p);
    let x = abort_on_unwind(move || f(x));
    ptr::write(p, x)
} }

#[inline]
pub fn mutate2<S, T, F: FnOnce(S, T) -> (S, T)>(p: &mut S, q: &mut T, f: F) { unsafe {
    let (x, y) = (ptr::read(p), ptr::read(q));
    let (x, y) = abort_on_unwind(move || f(x, y));
    ptr::write(p, x);
    ptr::write(q, y);
} }

#[inline]
pub fn align_mut_ptr<S, T>(ptr: *mut S) -> *mut T { align(mem::align_of::<T>(), ptr as usize) as *mut T }

#[inline]
pub fn align(a: usize, n: usize) -> usize { assert_eq!(0, a&(a-1)); (n+a-1)&!(a-1) }

#[inline]
pub fn ptr_diff<T>(p: *const T, q: *const T) -> usize {
    use core::num::Wrapping as w;
    (w(p as usize) - w(q as usize)).0/mem::size_of::<T>()
}

struct AbortOnDrop;

impl Drop for AbortOnDrop {
    #[inline(always)]
    fn drop(&mut self) { ::core::intrinsics::abort() }
}

#[inline(always)]
fn abort_on_unwind<F: FnOnce() -> T, T>(f: F) -> T {
    let guard = AbortOnDrop;
    let x = f();
    mem::forget(guard);
    x
}
