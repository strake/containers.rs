#![no_std]

#![feature(non_ascii_idents)]

#![cfg_attr(feature = "box", feature(fundamental))]
#![cfg_attr(feature = "box", feature(lang_items))]

#![cfg_attr(test, feature(custom_attribute))]
#![cfg_attr(test, feature(plugin))]

#![cfg_attr(test, plugin(quickcheck_macros))]

extern crate loca as alloc;
extern crate either;
extern crate fallible;
extern crate heap;
extern crate ptr;
extern crate rel;
extern crate slot;
extern crate unreachable;

#[cfg(any(test, feature = "default_allocator"))]
extern crate default_allocator;

#[cfg(test)] extern crate quickcheck;
#[cfg(test)] extern crate std;

#[cfg(feature = "box")]
pub mod boxed;
pub mod collections;

mod util;

#[cfg(not(any(test, feature = "default_allocator")))]
type DefaultA = alloc::NullAllocator;

#[cfg(any(test, feature = "default_allocator"))]
type DefaultA = default_allocator::Heap;
