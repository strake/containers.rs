//! Hash tables

extern crate hash_table as ht;

use alloc::*;
use core::{fmt, mem, ptr, slice};
use core::borrow::Borrow;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ops::{Index, IndexMut, RangeFull};
use core::ptr::NonNull;
use slot::Slot;

use util::*;

pub use self::ht::{DefaultHasher, IterWithIx, IterMutWithIx};

use self::mem::ManuallyDrop as M;

pub struct HashTable<K: Eq + Hash, T, H: Clone + Hasher = DefaultHasher, A: Alloc = ::DefaultA> {
    φ: PhantomData<(K, T)>,
    ptr: NonNull<u8>,
    log_cap: u32,
    table: M<ht::HashTable<K, T, SliceMut<usize>, SliceMut<Slot<(K, T)>>, H>>,
    alloc: A,
}

unsafe impl<K: Send + Eq + Hash, T: Send, H: Send + Clone + Hasher, A: Alloc + Send> Send for HashTable<K, T, H, A> {}
unsafe impl<K: Sync + Eq + Hash, T: Sync, H: Sync + Clone + Hasher, A: Alloc + Sync> Sync for HashTable<K, T, H, A> {}

impl<K: Eq + Hash, T, H: Clone + Hasher, A: Alloc + Default> HashTable<K, T, H, A> {
    #[inline]
    pub fn new(log_cap: u32, hasher: H) -> Option<Self> { Self::new_in(A::default(), log_cap, hasher) }
}

#[inline]
unsafe fn components_mut<'a, A>(ptr: *mut u8, log_cap: u32) -> (&'a mut [usize], &'a mut [A]) {
        let cap = 1<<log_cap;
        let elms_ptr: *mut A = ptr as _;
        let hash_ptr: *mut usize = align_mut_ptr(elms_ptr.add(cap));
        (slice::from_raw_parts_mut(hash_ptr, cap),
         slice::from_raw_parts_mut(elms_ptr, cap))
}

impl<K: Eq + Hash, T, H: Clone + Hasher, A: Alloc> HashTable<K, T, H, A> {
    #[inline]
    pub fn new_in(mut a: A, log_cap: u32, hasher: H) -> Option<Self> {
        if log_cap > (hash_flag | dead_flag).trailing_zeros() { return None; }
        unsafe { a.alloc(Self::layout(log_cap)?).ok().map(|ptr| {
            let (hs, es) = components_mut(ptr.as_ptr(), log_cap);
            let (hs, es) = (SliceMut::from_mut_slice(hs), SliceMut::from_mut_slice(es));
            HashTable { φ: PhantomData, ptr, log_cap, alloc: a,
                        table: M::new(ht::HashTable::from_parts(hs, es, hasher)) }
        }) }
    }

    fn layout(log_cap: u32) -> Option<Layout> {
        let cap = 1<<log_cap;
        Some(Layout::new::<()>().extend(Layout::array::<(K, T)>(cap)?)?.0
                                .extend(Layout::array::<usize>(cap)?)?.0)
    }

    fn components_mut(&mut self) -> (&mut [usize], &mut [Slot<(K, T)>], &mut A) {
        let (hs, es) = unsafe { components_mut(self.ptr.as_ptr(), self.log_cap) };
        (hs, es, &mut self.alloc)
    }

    fn components(&self) -> (&[usize], &[Slot<(K, T)>]) {
        let (hashes, elms, _) = unsafe {
            (self as *const Self as *mut Self).as_mut().unwrap().components_mut()
        };
        (hashes, elms)
    }

    #[inline]
    pub fn find_with_ix<Q: ?Sized>(&self, k: &Q) -> Option<(usize, &K, &T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.table.find_with_ix(k)
    }

    #[inline]
    pub fn find_mut_with_ix<Q: ?Sized>(&mut self, k: &Q) -> Option<(usize, &K, &mut T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.table.find_mut_with_ix(k)
    }

    #[inline]
    pub fn find<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.table.find(k)
    }

    #[inline]
    pub fn find_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<(&K, &mut T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.table.find_mut(k)
    }

    #[inline]
    pub fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, k: K, f: F) -> Result<(usize, &K, &mut T), (K, F)> {
        self.table.insert_with(k, f)
    }

    #[inline]
    pub fn grow(&mut self) -> bool { unsafe {
        let new_ptr = match self.alloc.alloc(Self::layout(self.log_cap + 1).unwrap()) {
            Ok(ptr) => ptr,
            _ => return false,
        };
        let (ptr, log_cap, hasher, alloc) = (self.ptr, self.log_cap,
                                             self.table.hasher().clone(),
                                             ptr::read(&self.alloc));
        let (hs, es) = components_mut(ptr.as_ptr(), log_cap);
        let (hs, es) = (SliceMut::from_mut_slice(hs), SliceMut::from_mut_slice(es));
        let mut new = HashTable { ptr: new_ptr, log_cap: log_cap + 1, alloc,φ: PhantomData,
                                  table: M::new(ht::HashTable::from_parts(hs, es, hasher)) };
        for i in 0..1<<log_cap {
            use unreachable::UncheckedResultExt;
            let (hashes, elms, _) = self.components_mut();
            if 0 == hashes[i] || is_dead(hashes[i]) { continue; }
            let (k, x) = ptr::read(&elms[i].x);
            new.insert(k, x).unchecked_unwrap_ok();
        }
        new.alloc.dealloc(ptr, Self::layout(log_cap).unwrap());
        mem::forget(mem::replace(self, new));
        true
    } }

    #[inline]
    pub fn insert_with_ix(&mut self, k: K, x: T) -> Result<(usize, Option<T>), (K, T)> {
        self.table.insert_with_ix(k, x)
    }

    #[inline]
    pub fn insert(&mut self, k: K, x: T) -> Result<Option<T>, (K, T)> {
        self.table.insert(k, x)
    }

    #[inline]
    pub fn delete<Q: ?Sized>(&mut self, k: &Q) -> Option<T> where K: Borrow<Q>, Q: Eq + Hash {
        self.table.delete(k)
    }

    #[inline]
    pub fn iter_with_ix(&self) -> IterWithIx<K, T> {
        self.table.iter_with_ix()
    }

    #[inline]
    pub fn iter_mut_with_ix(&mut self) -> IterMutWithIx<K, T> {
        self.table.iter_mut_with_ix()
    }

    #[inline]
    pub unsafe fn alloc_mut(&mut self) -> &mut A { &mut self.alloc }
}

impl<K: fmt::Debug + Eq + Hash, T: fmt::Debug, H: Clone + Hasher, A: Alloc> fmt::Debug for HashTable<K, T, H, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use core::fmt::Write;
        f.write_char('[')?;
        for i in 0..1<<self.log_cap {
            if i > 0 { f.write_str(", ")?; }
            match self.components().0[i] {
                0 => f.write_str("EMPTY")?,
                h if is_dead(h) => f.write_str("DEAD")?,
                h => unsafe {
                    let (ref k, ref x) = self.components().1[i].x;
                    write!(f, "{{ hash: {:016X}, key: {:?}, value: {:?} }}", h & !hash_flag, k, x)
                }?,
            }
        }
        f.write_char(']')?;
        Ok(())
    }
}

#[inline]
fn is_dead(h: usize) -> bool { 0 != h & dead_flag }

const dead_flag: usize = !(!0>>1);
const hash_flag: usize = dead_flag>>1;

impl<K: Eq + Hash, T, H: Clone + Hasher, A: Alloc> Drop for HashTable<K, T, H, A> {
    #[inline]
    fn drop(&mut self) {
        let ptr = self.ptr;
        let log_cap = self.log_cap;
        unsafe {
            M::drop(&mut self.table);
            self.alloc.dealloc(ptr, Self::layout(log_cap).unwrap());
        }
    }
}

struct SliceMut<A>(*mut A, usize);

impl<A> Index<usize> for SliceMut<A> {
    type Output = A;
    #[inline]
    fn index(&self, k: usize) -> &A { &self[..][k] }
}

impl<A> IndexMut<usize> for SliceMut<A> {
    #[inline]
    fn index_mut(&mut self, k: usize) -> &mut A { &mut self[..][k] }
}

impl<A> Index<RangeFull> for SliceMut<A> {
    type Output = [A];
    #[inline]
    fn index(&self, _: RangeFull) -> &[A] { unsafe { slice::from_raw_parts(self.0, self.1) } }
}

impl<A> IndexMut<RangeFull> for SliceMut<A> {
    #[inline]
    fn index_mut(&mut self, _: RangeFull) -> &mut [A] { unsafe { slice::from_raw_parts_mut(self.0, self.1) } }
}

impl<A> SliceMut<A> {
    #[inline]
    unsafe fn from_mut_slice(xs: &mut [A]) -> Self { SliceMut(xs.as_mut_ptr(), xs.len()) }
}

#[cfg(test)] mod tests {
    use std::hash::*;
    use std::vec::Vec;

    use util::*;

    use super::*;

    fn nub_by_0<S: Ord, T>(v: &mut Vec<(S, T)>) {
        // Only last element of test input vector with each key is kept in table, so we must delete the others.
        // We can not merely sort by reverse comparison rather than sort and reverse as we rely on stability.
        v.sort_by(|&(ref i, _), &(ref j, _)| Ord::cmp(i, j));
        v.reverse();
        let mut i = 1;
        while i < v.len() {
            while i < v.len() && v[i-1].0 == v[i].0 { v.remove(i); }
            i += 1;
        }
    }

    #[derive(Clone)]
    struct XorBytesHasher(u64);
    impl Hasher for XorBytesHasher {
        fn finish(&self) -> u64 { match self { &XorBytesHasher(h) => h } }
        fn write(&mut self, bs: &[u8]) { mutate(self, |XorBytesHasher(mut h)| {
                                                          for &b in bs { h ^= b as u64; }
                                                          XorBytesHasher(h)
                                                      }) }
    }

    #[derive(Clone)]
    struct NullHasher;
    impl Hasher for NullHasher {
        fn finish(&self) -> u64 { 0 }
        fn write(&mut self, _: &[u8]) {}
    }

    #[quickcheck] fn insertion_sans_collision(mut v: Vec<u64>) -> bool {
        v.truncate(0x100);
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, XorBytesHasher>::new(log_cap, XorBytesHasher(0)).unwrap();
        for (k, &x) in v.iter().enumerate() { t.insert(k as u8, x).unwrap(); }
        v.iter().enumerate().all(|(k, x)| t.find(&(k as u8)) == Some((&(k as u8), &x)))
    }

    #[quickcheck] fn insertion_with_collision(mut v: Vec<(u8, u64)>) -> bool {
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, NullHasher>::new(log_cap, NullHasher).unwrap();
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&k) == Some((&k, &x)))
    }

    #[quickcheck] fn deletion_sans_collision(mut v: Vec<u64>) -> bool {
        v.truncate(0x100);
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, XorBytesHasher>::new(log_cap, XorBytesHasher(0)).unwrap();
        for (k, &x) in v.iter().enumerate() { t.insert(k as u8, x).unwrap(); }
        v.iter().enumerate().all(|(k, &x)| t.find(&(k as u8)) == Some((&(k as u8), &x)) && t.delete(&(k as u8)) == Some(x) && t.find(&(k as u8)) == None)
    }

    #[quickcheck] fn deletion_with_collision(mut v: Vec<(u8, u64)>) -> bool {
        v.truncate(8);
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, NullHasher>::new(log_cap, NullHasher).unwrap();
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&(k as u8)) == Some((&k, &x)) && t.delete(&k) == Some(x) && t.find(&k) == None)
    }

    #[quickcheck] fn growth(mut v: Vec<u64>) -> bool {
        v.truncate(0x100);
        let log_cap = 7;
        let mut t = HashTable::<u8, u64, XorBytesHasher>::new(log_cap, XorBytesHasher(0)).unwrap();
        for (k, &x) in v.iter().enumerate() { match t.insert(k as u8, x) {
            Ok(_) => (),
            Err((k, x)) => {
                assert!(t.grow());
                t.insert(k, x).unwrap();
            },
        } }
        v.iter().enumerate().all(|(k, x)| t.find(&(k as u8)) == Some((&(k as u8), &x)))
    }

    #[quickcheck] fn growth_box(mut v: Vec<::std::boxed::Box<u64>>) -> bool {
        v.truncate(0x100);
        let log_cap = 7;
        let mut t = HashTable::<u8, ::std::boxed::Box<u64>, XorBytesHasher>::new(log_cap, XorBytesHasher(0)).unwrap();
        for (k, x) in v.clone().into_iter().enumerate() { match t.insert(k as u8, x) {
            Ok(_) => (),
            Err((k, x)) => {
                assert!(t.grow());
                t.insert(k, x).unwrap();
            },
        } }
        v.iter().enumerate().all(|(k, x)| t.find(&(k as u8)) == Some((&(k as u8), &x)))
    }
}
