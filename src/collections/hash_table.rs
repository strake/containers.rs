//! Hash tables

use alloc::*;
use core::borrow::Borrow;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem;
use core::ptr;
use core::slice;

use util::*;

#[derive(Clone)]
pub struct DefaultHasher(::sip::SipHasher);

impl Default for DefaultHasher {
    #[inline] fn default() -> Self { DefaultHasher(Default::default()) }
}

impl Hasher for DefaultHasher {
    #[inline] fn finish(&self) -> u64 { self.0.finish() }
    #[inline] fn write(&mut self, bs: &[u8]) { self.0.write(bs) }
}

pub struct HashTable<K: Eq + Hash, T, H: Clone + Hasher = DefaultHasher, A: Alloc = ::DefaultA> {
    φ: PhantomData<(K, T)>,
    ptr: *mut u8,
    log_cap: u32,
    hasher: H,
    alloc: A,
    free_n: usize,
}

unsafe impl<K: Send + Eq + Hash, T: Send, H: Send + Clone + Hasher, A: Alloc + Send> Send for HashTable<K, T, H, A> {}
unsafe impl<K: Sync + Eq + Hash, T: Sync, H: Sync + Clone + Hasher, A: Alloc + Sync> Sync for HashTable<K, T, H, A> {}

impl<K: Eq + Hash, T, H: Clone + Hasher, A: Alloc + Default> HashTable<K, T, H, A> {
    #[inline] pub fn new(log_cap: u32, hasher: H) -> Option<Self> { Self::new_in(A::default(), log_cap, hasher) }
}

impl<K: Eq + Hash, T, H: Clone + Hasher, A: Alloc> HashTable<K, T, H, A> {
    #[inline] pub fn new_in(mut a: A, log_cap: u32, hasher: H) -> Option<Self> {
        unsafe { a.alloc(Self::layout(log_cap)?).ok().map(|p| {
            let mut new = HashTable { φ: PhantomData, ptr: p, log_cap: log_cap, hasher: hasher,
                                      alloc: a, free_n: 1<<log_cap };
            for i in 0..1<<log_cap { new.components_mut().0[i] = 0; }
            new
        }) }
    }

    fn layout(log_cap: u32) -> Option<Layout> {
        let cap = 1<<log_cap;
        Some(Layout::new::<()>().extend(Layout::array::<T>(cap)?)?.0
                                .extend(Layout::array::<K>(cap)?)?.0
                                .extend(Layout::array::<usize>(cap)?)?.0)
    }

    fn components_mut(&mut self) -> (&mut [usize], &mut [K], &mut [T], &mut A) {
        let cap = 1<<self.log_cap;
        unsafe {
            let vals_ptr = self.ptr as *mut T;
            let keys_ptr = align_mut_ptr(vals_ptr.offset(cap as isize) as *mut K);
            let hash_ptr = align_mut_ptr(keys_ptr.offset(cap as isize) as *mut usize);
            (slice::from_raw_parts_mut(hash_ptr, cap),
             slice::from_raw_parts_mut(keys_ptr, cap),
             slice::from_raw_parts_mut(vals_ptr, cap),
             &mut self.alloc)
        }
    }

    fn components(&self) -> (&[usize], &[K], &[T]) {
        let (hashes, keys, vals, _) = unsafe {
            (self as *const Self as *mut Self).as_mut().unwrap().components_mut()
        };
        (hashes, keys, vals)
    }

    fn hash<Q: ?Sized>(&self, k: &Q) -> usize where Q: Hash {
        let mut h = self.hasher.clone();
        k.hash(&mut h);
        h.finish() as usize
    }

    fn find_ix<Q: ?Sized>(&self, k: &Q) -> Option<usize> where K: Borrow<Q>, Q: Eq + Hash {
        let wrap_mask = (1<<self.log_cap)-1;
        let hash_mask = wrap_mask|!(!0>>1);
        let mut i = self.hash(k)&wrap_mask;
        let h = i|!(!0>>1);
        let (hashes, keys, _) = self.components();
        while hashes[i]&hash_mask != h {
            if hashes[i] == 0 { return None };
            i = (i+1)&wrap_mask;
        }
        while hashes[i]&hash_mask == h && keys[i].borrow() != k { i = (i+1)&wrap_mask; }
        if hashes[i]&hash_mask == h { Some(i) } else { None }
    }

    #[inline]
    pub fn find_with_ix<Q: ?Sized>(&self, k: &Q) -> Option<(usize, &K, &T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| { let (_, keys, vals) = self.components(); (i, &keys[i], &vals[i]) })
    }

    #[inline]
    pub fn find_mut_with_ix<Q: ?Sized>(&mut self, k: &Q) -> Option<(usize, &K, &mut T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| { let (_, keys, vals, _) = self.components_mut(); (i, &keys[i], &mut vals[i]) })
    }

    #[inline]
    pub fn find<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_with_ix(k).map(|(_, k, x)| (k, x))
    }

    #[inline]
    pub fn find_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<(&K, &mut T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_mut_with_ix(k).map(|(_, k, x)| (k, x))
    }

    #[inline]
    pub fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, mut k: K, f: F) -> Result<(usize, &mut K, &mut T), (K, F)> {
        if 0 == self.free_n && !self.grow() { return Err((k, f)); }

        let cap = 1<<self.log_cap;
        let mut h = self.hash(&k)|!(!0>>1);
        let mut i = h&(cap-1);
        let mut psl = 0;
        let (hashes, keys, vals, _) = self.components_mut();
        loop {
            if hashes[i] == 0 {
                hashes[i] = h;
                unsafe {
                    ptr::write(&mut keys[i], k);
                    ptr::write(&mut vals[i], f(None));
                }
                return Ok((i, &mut keys[i], &mut vals[i]))
            }

            if hashes[i]&(cap-1) == h&(cap-1) && keys[i] == k {
                mutate(&mut vals[i], |x| f(Some(x)));
                return Ok((i, &mut keys[i], &mut vals[i]))
            }

            if psl > compute_psl(hashes, i) {
                let mut x = f(None);
                loop {
                    mem::swap(&mut h, &mut hashes[i]);
                    mem::swap(&mut k, &mut keys[i]);
                    mem::swap(&mut x, &mut vals[i]);
                    if h == 0 {
                        mem::forget((k, x));
                        return Ok((i, &mut keys[i], &mut vals[i]));
                    };
                    i = (i+1)&(cap-1);
                }
            }

            i = (i+1)&(cap-1);
            psl += 1;
        }
    }

    fn grow(&mut self) -> bool { false }

    #[inline]
    pub fn insert_with_ix(&mut self, k: K, x: T) -> Result<(usize, Option<T>), (K, T)> {
        let mut opt_y = None;
        self.insert_with(k, |opt_x| { opt_y = opt_x; x })
            .map_err(|(k, f)| (k, f(None))).map(|(k, _, _)| (k, opt_y))
    }

    #[inline]
    pub fn insert(&mut self, k: K, x: T) -> Result<Option<T>, (K, T)> {
        self.insert_with_ix(k, x).map(|(_, opt_y)| opt_y)
    }

    #[inline]
    pub fn delete<Q: ?Sized>(&mut self, k: &Q) -> Option<T> where K: Borrow<Q>, Q: Eq + Hash {
        let cap = 1<<self.log_cap;
        self.find_ix(k).map(move |mut i| unsafe {
            let (hashes, keys, vals, _) = self.components_mut();
            let (_, x) = (ptr::read(&keys[i]), ptr::read(&vals[i]));
            loop {
                let j = (i+1)&(cap-1);
                if hashes[j] == 0 || compute_psl(hashes, j) == 0 { hashes[i] = 0; break; }
                hashes[i] = hashes[j];
                ptr::copy(&keys[j], &mut keys[i], 1);
                ptr::copy(&vals[j], &mut vals[i], 1);
                i = j;
            }
            x
        })
    }

    #[inline]
    pub fn iter_with_ix(&self) -> IterWithIx<K, T> {
        let (hashes, keys, vals) = self.components();
        IterWithIx {
            φ: PhantomData,
            hash_ptr: &hashes[0],
            keys_ptr: &keys[0],
            vals_ptr: &vals[0],
            hash_end: (&hashes[0] as *const _).wrapping_offset(hashes.len() as _),
        }
    }

    #[inline]
    pub fn iter_mut_with_ix(&mut self) -> IterMutWithIx<K, T> {
        let (hashes, keys, vals, _) = self.components_mut();
        IterMutWithIx {
            φ: PhantomData,
            hash_ptr: &hashes[0],
            keys_ptr: &keys[0],
            vals_ptr: &mut vals[0],
            hash_end: (&hashes[0] as *const _).wrapping_offset(hashes.len() as _),
        }
    }
}

#[derive(Clone, Copy)]
pub struct IterWithIx<'a, K, T> {
    φ: PhantomData<&'a ()>,
    hash_ptr: *const usize,
    keys_ptr: *const K,
    vals_ptr: *const T,
    hash_end: *const usize,
}

impl<'a, K: 'a, T: 'a> Iterator for IterWithIx<'a, K, T> {
    type Item = (usize, &'a K, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut r = None;
        while r.is_none() && self.hash_ptr != self.hash_end { unsafe {
            if 0 != ptr::read(self.hash_ptr) { r = Some((ptr_diff(self.hash_ptr, self.hash_end),
                                                         self.keys_ptr.as_ref().unwrap(),
                                                         self.vals_ptr.as_ref().unwrap())); }
            self.hash_ptr = self.hash_ptr.wrapping_offset(1);
            self.keys_ptr = self.keys_ptr.offset(1);
            self.vals_ptr = self.vals_ptr.offset(1);
        } }
        r
    }
}

unsafe impl<'a, K: Sync, T: Sync> Send for IterWithIx<'a, K, T> {}
unsafe impl<'a, K: Sync, T: Sync> Sync for IterWithIx<'a, K, T> {}

pub struct IterMutWithIx<'a, K, T> {
    φ: PhantomData<&'a ()>,
    hash_ptr: *const usize,
    keys_ptr: *const K,
    vals_ptr: *mut T,
    hash_end: *const usize,
}

unsafe impl<'a, K: Sync, T: Send> Send for IterMutWithIx<'a, K, T> {}

impl<'a, K: 'a, T: 'a> Iterator for IterMutWithIx<'a, K, T> {
    type Item = (usize, &'a K, &'a mut T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut r = None;
        while r.is_none() && self.hash_ptr != self.hash_end { unsafe {
            if 0 != ptr::read(self.hash_ptr) { r = Some((ptr_diff(self.hash_ptr, self.hash_end),
                                                         self.keys_ptr.as_ref().unwrap(),
                                                         self.vals_ptr.as_mut().unwrap())); }
            self.hash_ptr = self.hash_ptr.wrapping_offset(1);
            self.keys_ptr = self.keys_ptr.offset(1);
            self.vals_ptr = self.vals_ptr.offset(1);
        } }
        r
    }
}

#[inline(always)]
fn ptr_diff<T>(p: *const T, q: *const T) -> usize {
    use ::core::num::Wrapping;
    (Wrapping(p as usize) - Wrapping(q as usize)).0/mem::size_of::<T>()
}

#[inline] fn compute_psl(hs: &[usize], i: usize) -> usize { usize::wrapping_sub(i, hs[i])&(hs.len()-1) }

impl<K: Eq + Hash, T, H: Clone + Hasher, A: Alloc> Drop for HashTable<K, T, H, A> {
    #[inline] fn drop(&mut self) {
        let ptr = self.ptr;
        let log_cap = self.log_cap;
        let (hashes, keys, vals, alloc) = self.components_mut();
        unsafe {
            for i in 0..1<<log_cap {
                if hashes[i] != 0 {
                    ptr::drop_in_place(&mut keys[i]);
                    ptr::drop_in_place(&mut vals[i]);
                }
            }
            alloc.dealloc(ptr, Self::layout(log_cap).unwrap());
        }
    }
}

#[cfg(test)] mod tests {
    use quickcheck::{ Arbitrary, Gen };
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

    // ¬([_; 0x100]: Copy + Clone). Grr. *irritation*
    #[derive(Copy, Clone, Debug)]
    struct ArrayOf0x100<T: Copy>([[T; 0x10]; 0x10]);
    impl<T: Arbitrary + Copy> Arbitrary for ArrayOf0x100<T> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            use std::mem;
            use std::ptr;
            unsafe {
                let mut a: [[T; 0x10]; 0x10] = mem::uninitialized();
                for i in 0..0x10 { for j in 0..0x10 { ptr::write(&mut a[i][j], T::arbitrary(g)); } }
                ArrayOf0x100(a)
            }
        }
    }

    #[derive(Clone)]
    struct ArrayOf0x100Hasher([[u64; 0x10]; 0x10], u64);
    impl Hasher for ArrayOf0x100Hasher {
        fn finish(&self) -> u64 { match self { &ArrayOf0x100Hasher(_, h) => h } }
        fn write(&mut self, bs: &[u8]) { mutate(self, |ArrayOf0x100Hasher(a, mut h)| {
                                                          for &b in bs { h ^= a[b as usize>>4][b as usize&0x0F]; }
                                                          ArrayOf0x100Hasher(a, h)
                                                      }) }
    }

    #[quickcheck] fn insertion_sans_collision(mut v: Vec<u64>) -> bool {
        v.truncate(0x100);
        let log_cap = v.len().next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, XorBytesHasher>::new(log_cap, XorBytesHasher(0)).unwrap();
        for (k, &x) in v.iter().enumerate() { t.insert(k as u8, x).unwrap(); }
        v.iter().enumerate().all(|(k, x)| t.find(&(k as u8)) == Some((&(k as u8), &x)))
    }

    #[quickcheck] fn insertion_with_collision(mut v: Vec<(u8, u64)>) -> bool {
        let log_cap = v.len().next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, NullHasher>::new(log_cap, NullHasher).unwrap();
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&k) == Some((&k, &x)))
    }

    #[quickcheck] fn insertion_with_random_hash(a: ArrayOf0x100<u64>, mut v: Vec<(u8, u64)>) -> bool {
        let ArrayOf0x100(a) = a;

        let log_cap = v.len().next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, ArrayOf0x100Hasher>::new(log_cap, ArrayOf0x100Hasher(a, 0)).unwrap();
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&k) == Some((&k, &x)))
    }

    #[quickcheck] fn deletion_sans_collision(mut v: Vec<u64>) -> bool {
        v.truncate(0x100);
        let log_cap = v.len().next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, XorBytesHasher>::new(log_cap, XorBytesHasher(0)).unwrap();
        for (k, &x) in v.iter().enumerate() { t.insert(k as u8, x).unwrap(); }
        v.iter().enumerate().all(|(k, &x)| t.find(&(k as u8)) == Some((&(k as u8), &x)) && t.delete(&(k as u8)) == Some(x) && t.find(&(k as u8)) == None)
    }

    #[quickcheck] fn deletion_with_collision(mut v: Vec<(u8, u64)>) -> bool {
        v.truncate(8);
        let log_cap = v.len().next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, NullHasher>::new(log_cap, NullHasher).unwrap();
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&(k as u8)) == Some((&k, &x)) && t.delete(&k) == Some(x) && t.find(&k) == None)
    }

    #[quickcheck] fn deletion_with_random_hash(a: ArrayOf0x100<u64>, mut v: Vec<(u8, u64)>) -> bool {
        let ArrayOf0x100(a) = a;

        let log_cap = v.len().next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, ArrayOf0x100Hasher>::new(log_cap, ArrayOf0x100Hasher(a, 0)).unwrap();
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&k) == Some((&k, &x)) && t.delete(&k) == Some(x) && t.find(&k) == None)
    }

    #[quickcheck] fn iter(v: Vec<(u8, u64)>) -> bool {
        let log_cap = v.len().next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64>::new(log_cap, Default::default()).unwrap();
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        t.iter_with_ix().all(|(_, &i, &x)| v.iter().any(|&(j, y)| (i, x) == (j, y)))
    }
}
