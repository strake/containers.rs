#![feature(non_ascii_idents)]
#![feature(unique)]

#![cfg_attr(feature = "box", feature(fundamental))]
#![cfg_attr(feature = "box", feature(lang_items))]

#![cfg_attr(test, feature(custom_attribute))]
#![cfg_attr(test, feature(plugin))]

#![no_std]

#![cfg_attr(test, plugin(quickcheck_macros))]

extern crate loca as alloc;
extern crate heap;
extern crate rel;
extern crate siphasher;
extern crate typenum;

#[cfg(any(test, feature = "default_allocator"))]
extern crate default_allocator;

use siphasher::sip;

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
