#![no_std]

#![deny(missing_debug_implementations)]

#![feature(coerce_unsized)]
#![feature(const_fn_trait_bound)]
#![feature(const_mut_refs)]
#![feature(dropck_eyepatch)]
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
