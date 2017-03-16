#![feature(alloc)]
#![feature(heap_api)]
#![feature(non_ascii_idents)]
#![feature(unique)]

#![cfg_attr(test, feature(plugin))]

#![no_std]

#![cfg_attr(test, plugin(quickcheck_macros))]

extern crate alloc;
extern crate heap;
extern crate rel;
extern crate typenum;

#[cfg(test)] extern crate quickcheck;
#[cfg(test)] extern crate std;

macro_rules! tryOpt {
    ($x: expr) => (match $x { None => return None, Some(x) => x })
}

pub mod boxed;
pub mod collections;

mod util;
