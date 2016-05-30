use core::cmp::*;
use core::mem;
use core::ops::Add;

use util::*;

pub struct ByteSize {
    pub align : usize,
    pub length: usize,
}

impl Add for ByteSize {
    type Output = Self;
    #[inline] fn add(self, other: Self) -> Self {
        ByteSize {
            align: max(self.align, other.align),
            length: align(other.align, self.length) + other.length,
        }
    }
}

impl ByteSize {
    #[inline] pub fn array<T>(n: usize) -> Self { ByteSize { align: mem::align_of::<T>(), length: mem::size_of::<T>()*n } }
}
