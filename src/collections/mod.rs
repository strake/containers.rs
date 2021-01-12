//! Collection types

pub mod b_tree;
mod hash_table;
mod heap;
mod raw_vec;
mod vec;

pub use self::b_tree::BTree;
pub use self::hash_table::HashTable;
pub use self::heap::Heap;
pub use self::raw_vec::{RawVec, FixedStorage};
pub use self::vec::Vec;

#[macro_export]
macro_rules! vec {
    // ($x:expr; $n:expr) => ($crate::collections::Vec::replicate($x, $n));
    () => (Some($crate::collections::Vec::new()));
    ($x:expr; $n:expr) => ({
        let mut xs = $crate::collections::Vec::with_capacity($n);
        if let Some(xs) = &mut xs { for _ in 0..$n { xs.push($x); } }
        xs
    });
    ($($x:expr),+ $(,)?) => ($crate::boxed::Box::new([$($x),+]).and_then($crate::collections::Vec::from).ok());
}

/// ```
/// let x = vec![0u8, 1, 5];
/// let y = vec![0u8; 16];
/// ```
#[cfg(doctest)]
struct VecMacro;
