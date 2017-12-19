#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate containers;
extern crate default_allocator as defalloc;
extern crate rel;

use b_tree::Which::*;
use defalloc::Heap;
use containers::collections::*;

fuzz_target!(|data: &[u8]| {
    if 0 == data.len() { return; }
    let b = data[0] as usize;
    let data = &data[1..];
    if let Some(mut t) = BTree::<_, _, _, Heap>::new(::rel::Core, b) {
        for xs in data.windows(2) {
            let (c, x) = (xs[0], xs[1]);
            let which = match c % 3 {
                0 => Key(&x),
                1 => Min,
                _ => Max,
            };
            match (c / 3) % 3 {
                0 => { let _ = t.insert(x, ()); },
                1 => { t.delete_which(which); },
                _ => match which {
                    Key(k) => { t.find(k); },
                    Min    => { t.min(); },
                    Max    => { t.max(); },
                },
            }
        }
    }
});
