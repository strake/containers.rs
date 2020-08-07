#![no_std]

#![deny(missing_debug_implementations)]

#![feature(non_ascii_idents)]
#![feature(coerce_unsized)]
#![feature(core_intrinsics)]
#![feature(const_fn)]
#![feature(unsize)]

#![cfg_attr(feature = "box", feature(fundamental))]

#[cfg(test)]
#[macro_use]
extern crate quickcheck_macros;
#[cfg(test)]
extern crate std;

#[cfg(feature = "box")]
pub mod boxed;
pub mod collections;
#[cfg(feature = "box")]
pub mod rc;
#[cfg(feature = "box")]
pub mod sync;

mod util;

#[cfg(not(any(test, feature = "default_allocator")))]
type DefaultA = alloc::NullAllocator;

#[cfg(any(test, feature = "default_allocator"))]
type DefaultA = default_allocator::Heap;
