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
        Some(Layout::new::<()>().extend(Layout::array::<(K, T)>(cap)?)?.0
                                .extend(Layout::array::<usize>(cap)?)?.0)
    }

    fn components_mut(&mut self) -> (&mut [usize], &mut [(K, T)], &mut A) {
        let cap = 1<<self.log_cap;
        unsafe {
            let elms_ptr: *mut (K, T) = self.ptr as _;
            let hash_ptr: *mut usize = align_mut_ptr(elms_ptr.offset(cap as isize));
            (slice::from_raw_parts_mut(hash_ptr, cap),
             slice::from_raw_parts_mut(elms_ptr, cap),
             &mut self.alloc)
        }
    }

    fn components(&self) -> (&[usize], &[(K, T)]) {
        let (hashes, elms, _) = unsafe {
            (self as *const Self as *mut Self).as_mut().unwrap().components_mut()
        };
        (hashes, elms)
    }

    fn hash<Q: ?Sized>(&self, k: &Q) -> usize where Q: Hash {
        let mut h = self.hasher.clone();
        k.hash(&mut h);
        h.finish() as usize
    }

    fn find_ix<Q: ?Sized>(&self, k: &Q) -> Option<usize> where K: Borrow<Q>, Q: Eq + Hash {
        debug_assert!(self.free_n >= 1);
        let wrap_mask = (1<<self.log_cap)-1;
        let hash_mask = wrap_mask|!(!0>>1);
        let mut i = self.hash(k)&wrap_mask;
        let h = i|!(!0>>1);
        let (hashes, elms) = self.components();
        while hashes[i]&hash_mask != h {
            if hashes[i] == 0 { return None };
            i = (i+1)&wrap_mask;
            debug_assert_ne!(h & wrap_mask, i);
        }
        while hashes[i]&hash_mask == h && elms[i].0.borrow() != k { i = (i+1)&wrap_mask; }
        if hashes[i]&hash_mask == h { Some(i) } else { None }
    }

    #[inline]
    pub fn find_with_ix<Q: ?Sized>(&self, k: &Q) -> Option<(usize, &K, &T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| { let (_, elms) = self.components(); (i, &elms[i].0, &elms[i].1) })
    }

    #[inline]
    pub fn find_mut_with_ix<Q: ?Sized>(&mut self, k: &Q) -> Option<(usize, &K, &mut T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| { let (_, elms, _) = self.components_mut(); (i, &elms[i].0, &mut elms[i].1) })
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
    pub fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, k: K, f: F) -> Result<(usize, &mut K, &mut T), (K, F)> {
        if 1 >= self.free_n && !self.grow() { return Err((k, f)); }
        self.free_n -= 1;

        let cap = 1<<self.log_cap;
        let mut h = self.hash(&k)|!(!0>>1);
        let mut i = h&(cap-1);
        let mut psl = 0;
        let (hashes, elms, _) = self.components_mut();
        loop {
            if hashes[i] == 0 {
                hashes[i] = h;
                unsafe { ptr::write(&mut elms[i], (k, f(None))); }
                return Ok((i, &mut elms[i].0, &mut elms[i].1))
            }

            if hashes[i]&(cap-1) == h&(cap-1) && elms[i].0 == k {
                mutate(&mut elms[i].1, |x| f(Some(x)));
                return Ok((i, &mut elms[i].0, &mut elms[i].1))
            }

            if psl > compute_psl(hashes, i) {
                let mut e = (k, f(None));
                loop {
                    mem::swap(&mut h, &mut hashes[i]);
                    mem::swap(&mut e, &mut elms[i]);
                    if h == 0 {
                        mem::forget(e);
                        return Ok((i, &mut elms[i].0, &mut elms[i].1));
                    };
                    i = (i+1)&(cap-1);
                }
            }

            i = (i+1)&(cap-1);
            debug_assert_ne!(h&(cap-1), i);
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
            self.free_n += 1;
            debug_assert!(1 << self.log_cap >= self.free_n);
            let (hashes, elms, _) = self.components_mut();
            let (_, x) = ptr::read(&elms[i]);
            loop {
                let j = (i+1)&(cap-1);
                if hashes[j] == 0 || compute_psl(hashes, j) == 0 { hashes[i] = 0; break; }
                hashes[i] = hashes[j];
                ptr::copy(&elms[j], &mut elms[i], 1);
                i = j;
            }
            x
        })
    }

    #[inline]
    pub fn iter_with_ix(&self) -> IterWithIx<K, T> {
        let (hashes, elms) = self.components();
        IterWithIx {
            φ: PhantomData,
            hash_ptr: &hashes[0],
            elms_ptr: &elms[0],
            hash_end: hashes.as_ptr().wrapping_offset(hashes.len() as _),
        }
    }

    #[inline]
    pub fn iter_mut_with_ix(&mut self) -> IterMutWithIx<K, T> {
        let (hashes, elms, _) = self.components_mut();
        IterMutWithIx {
            φ: PhantomData,
            hash_ptr: &hashes[0],
            elms_ptr: &mut elms[0],
            hash_end: hashes.as_mut_ptr().wrapping_offset(hashes.len() as _),
        }
    }
}

#[derive(Clone, Copy)]
pub struct IterWithIx<'a, K, T> {
    φ: PhantomData<&'a ()>,
    hash_ptr: *const usize,
    elms_ptr: *const (K, T),
    hash_end: *const usize,
}

impl<'a, K: 'a, T: 'a> Iterator for IterWithIx<'a, K, T> {
    type Item = (usize, &'a K, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut r = None;
        while r.is_none() && self.hash_ptr != self.hash_end { unsafe {
            if 0 != ptr::read(self.hash_ptr) { r = Some((ptr_diff(self.hash_ptr, self.hash_end),
                                                         &(*self.elms_ptr).0,
                                                         &(*self.elms_ptr).1)); }
            self.hash_ptr = self.hash_ptr.wrapping_offset(1);
            self.elms_ptr = self.elms_ptr.offset(1);
        } }
        r
    }
}

unsafe impl<'a, K: Sync, T: Sync> Send for IterWithIx<'a, K, T> {}
unsafe impl<'a, K: Sync, T: Sync> Sync for IterWithIx<'a, K, T> {}

pub struct IterMutWithIx<'a, K, T> {
    φ: PhantomData<&'a ()>,
    hash_ptr: *const usize,
    elms_ptr: *mut (K, T),
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
                                                         &    (*self.elms_ptr).0,
                                                         &mut (*self.elms_ptr).1)); }
            self.hash_ptr = self.hash_ptr.wrapping_offset(1);
            self.elms_ptr = self.elms_ptr.offset(1);
        } }
        r
    }
}

#[inline] fn compute_psl(hs: &[usize], i: usize) -> usize { usize::wrapping_sub(i, hs[i])&(hs.len()-1) }

impl<K: Eq + Hash, T, H: Clone + Hasher, A: Alloc> Drop for HashTable<K, T, H, A> {
    #[inline] fn drop(&mut self) {
        let ptr = self.ptr;
        let log_cap = self.log_cap;
        let (hashes, elms, alloc) = self.components_mut();
        unsafe {
            for i in 0..1<<log_cap {
                if hashes[i] != 0 { ptr::drop_in_place(&mut elms[i]); }
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

    #[quickcheck] fn insertion_with_random_hash(a: ArrayOf0x100<u64>, mut v: Vec<(u8, u64)>) -> bool {
        let ArrayOf0x100(a) = a;

        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, ArrayOf0x100Hasher>::new(log_cap, ArrayOf0x100Hasher(a, 0)).unwrap();
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

    #[quickcheck] fn deletion_with_random_hash(a: ArrayOf0x100<u64>, mut v: Vec<(u8, u64)>) -> bool {
        let ArrayOf0x100(a) = a;

        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64, ArrayOf0x100Hasher>::new(log_cap, ArrayOf0x100Hasher(a, 0)).unwrap();
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&k) == Some((&k, &x)) && t.delete(&k) == Some(x) && t.find(&k) == None)
    }

    #[quickcheck] fn iter(v: Vec<(u8, u64)>) -> bool {
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = HashTable::<u8, u64>::new(log_cap, Default::default()).unwrap();
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        t.iter_with_ix().all(|(_, &i, &x)| v.iter().any(|&(j, y)| (i, x) == (j, y)))
    }

    #[test] fn full_table_forbidden() {
        let mut t = HashTable::<u8, ()>::new(1, Default::default()).unwrap();
        t.insert(0, ()).unwrap();
        assert!(t.insert(1, ()).is_err());
    }
}
