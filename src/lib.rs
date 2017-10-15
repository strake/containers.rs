#![feature(alloc)]
#![feature(allocator_api)]
#![feature(heap_api)]
#![feature(non_ascii_idents)]
#![feature(unique)]

#![cfg_attr(test, feature(custom_attribute))]
#![cfg_attr(test, feature(plugin))]

#![no_std]

#![cfg_attr(test, plugin(quickcheck_macros))]

extern crate loca as alloc;
extern crate heap;
extern crate rel;
extern crate typenum;

#[cfg(test)] extern crate quickcheck;
#[cfg(test)] extern crate std;

pub use alloc::boxed;
pub mod collections;

mod util;
