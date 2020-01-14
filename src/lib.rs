#![no_std]

#![deny(missing_debug_implementations)]

#![feature(non_ascii_idents)]
#![feature(const_fn)]

#![cfg_attr(feature = "box", feature(fundamental))]

extern crate loca as alloc;
extern crate either;
extern crate fallible;
extern crate heap;
extern crate ptr;
extern crate rel;
extern crate unreachable;

#[cfg(any(test, feature = "default_allocator"))]
extern crate default_allocator;

#[cfg(test)] extern crate quickcheck;
#[cfg(test)] #[macro_use]
             extern crate quickcheck_macros;
#[cfg(test)] extern crate rand;
#[cfg(test)] extern crate std;

#[cfg(feature = "box")]
pub mod boxed;
pub mod collections;

mod util;

#[cfg(not(any(test, feature = "default_allocator")))]
type DefaultA = alloc::NullAllocator;

#[cfg(any(test, feature = "default_allocator"))]
type DefaultA = default_allocator::Heap;
