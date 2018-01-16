#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate containers;
extern crate default_allocator as defalloc;
extern crate rel;
extern crate siphasher as sip;

use defalloc::Heap;
use containers::collections::*;
use sip::sip::SipHasher;

fuzz_target!(|data: &[u8]| {
    if 0 == data.len() { return; }
    let log_cap = (data[0] >> 5) as u32;
    let data = &data[1..];
    if let Some(mut t) = HashTable::<_, _, _, Heap>::new(log_cap, SipHasher::new()) {
        for xs in data.windows(2) {
            let (c, x) = (xs[0], xs[1]);
            match c % 3 {
                0 => { let _ = t.insert(x, ()); },
                1 => { t.delete(&x); },
                _ => { t.find(&x); },
            }
        }
    }
});
