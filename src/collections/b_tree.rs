//! Balanced search trees

use alloc::heap::*;
use core::cmp::{ max, min };
use core::cmp::Ordering::*;
use core::fmt;
use core::marker::PhantomData;
use core::mem;
use core::ptr;
use core::slice;

use util::byte_size::ByteSize;
use rel::ord::*;
use typenum::consts as N;
use typenum::uint::Unsigned;
use util::*;

struct BNode<B: Unsigned, Rel: TotalOrderRelation<K>, K, T> {
    φ: PhantomData<(B, Rel, K, T)>,
    m: usize,
    p: *mut u8,
}

impl<B: Unsigned, Rel: TotalOrderRelation<K>, K, T> BNode<B, Rel, K, T> {
    fn new(depth: usize) -> Option<Self> { if depth == 0 { Self::new_leaf() } else { Self::new_stem() } }

    fn new_stem() -> Option<Self> {
        let p = unsafe { allocate(Self::stem_size(), Self::stem_align()) };
        if p.is_null() { None } else {
            Some(BNode { φ: PhantomData, m: 0, p: p })
        }
    }

    fn new_leaf() -> Option<Self> {
        let p = if Self::leaf_size() == 0 { EMPTY as *mut _ }
                else { unsafe { allocate(Self::leaf_size(), Self::leaf_align()) } };
        if p.is_null() { None } else {
            Some(BNode { φ: PhantomData, m: 0, p: p })
        }
    }

    unsafe fn dealloc(ptr: *mut u8, depth: usize) {
        if depth == 0 && Self::leaf_size() == 0 { return };
        deallocate(ptr,
                   if depth == 0 { Self::leaf_size () } else { Self::stem_size () },
                   if depth == 0 { Self::leaf_align() } else { Self::stem_align() });
    }

    fn stem_align() -> usize { mem::align_of::<(K, T, Self)>() }

    fn leaf_align() -> usize { mem::align_of::<(K, T)>() }

    fn stem_size() -> usize {
        let n_max = B::to_usize()<<1;
        (ByteSize::array::<T>(n_max-1) + ByteSize::array::<K>(n_max-1) + ByteSize::array::<Self>(n_max)).length
    }

    fn leaf_size() -> usize {
        let n_max = B::to_usize()<<1;
        (ByteSize::array::<T>(n_max-1) + ByteSize::array::<K>(n_max-1)).length
    }

    unsafe fn component_arrays_mut(&mut self) -> (&mut [K], &mut [T], &mut [Self]) {
        let n_max = B::to_usize()<<1;
        let vals_ptr = self.p as *mut T;
        let keys_ptr = align_mut_ptr(vals_ptr.offset(n_max as isize-1) as *mut K);
        let children_ptr = align_mut_ptr(keys_ptr.offset(n_max as isize-1) as *mut Self);
        (slice::from_raw_parts_mut(keys_ptr, n_max-1),
         slice::from_raw_parts_mut(vals_ptr, n_max-1),
         slice::from_raw_parts_mut(children_ptr, n_max))
    }

    fn components_mut(&mut self, depth: usize) -> (&mut [K], &mut [T], &mut [Self]) {
        let m = self.m;
        let n = if depth == 0 { 0 } else { m+1 };
        let (keys, vals, children) = unsafe { self.component_arrays_mut() };
        (&mut keys[0..m], &mut vals[0..m], &mut children[0..n])
    }

    #[allow(mutable_transmutes)]
    unsafe fn component_arrays(&self) -> (&[K], &[T], &[Self]) {
        let (keys, vals, children) = mem::transmute::<&Self, &mut Self>(self).component_arrays_mut();
        (keys, vals, children)
    }

    unsafe fn val_array(&self) -> &[T] { self.component_arrays().1 }

    fn vals(&self) -> &[T] { &(unsafe { self.val_array() })[0..self.m] }

    unsafe fn val_array_mut(&mut self) -> &mut [T] { self.component_arrays_mut().1 }

    fn vals_mut(&mut self) -> &mut [T] { self.components_mut(0).1 }

    unsafe fn key_array(&self) -> &[K] { self.component_arrays().0 }

    fn keys(&self) -> &[K] { &(unsafe { self.key_array() })[0..self.m] }

    unsafe fn key_array_mut(&mut self) -> &mut [K] { self.component_arrays_mut().0 }

    fn keys_mut(&mut self) -> &mut [K] { self.components_mut(0).0 }

    unsafe fn child_array(&self) -> &[Self] { self.component_arrays().2 }

    fn children(&self, depth: usize) -> &[Self] { &(unsafe { self.child_array() })[0..if depth == 0 { 0 } else { self.m+1 }] }

    unsafe fn child_array_mut(&mut self) -> &mut [Self] { self.component_arrays_mut().2 }

    fn children_mut(&mut self, depth: usize) -> &mut [Self] { self.components_mut(depth).2 }

    fn insert_here_leaf_at(&mut self, i: usize, k: K, x: T) {
        unsafe {
            let k_ptr: *mut K = &mut self.key_array_mut()[i];
            ptr::copy(k_ptr, k_ptr.offset(1), self.m-i);
            ptr::write(k_ptr, k);
            let x_ptr: *mut T = &mut self.val_array_mut()[i];
            ptr::copy(x_ptr, x_ptr.offset(1), self.m-i);
            ptr::write(x_ptr, x);
        }
        self.m += 1;
    }

    fn insert_here_at(&mut self, i: usize, k: K, x: T, child: Self) {
        unsafe {
            let ptr: *mut Self = &mut self.child_array_mut()[i+1];
            ptr::copy(ptr, ptr.offset(1), self.m-i);
            ptr::write(ptr, child);
        }
        self.insert_here_leaf_at(i, k, x);
    }

    fn delete_here_leaf_at(&mut self, i: usize) -> (K, T) {
        self.m -= 1;
        unsafe {
            let k_ptr: *mut K = &mut self.key_array_mut()[i];
            let k = ptr::read(k_ptr);
            ptr::copy(k_ptr.offset(1), k_ptr, self.m-i);
            let x_ptr: *mut T = &mut self.val_array_mut()[i];
            let x = ptr::read(x_ptr);
            ptr::copy(x_ptr.offset(1), x_ptr, self.m-i);
            (k, x)
        }
    }

    fn delete_here_at(&mut self, i: usize) -> (K, T, Self) {
        let (k, x) = self.delete_here_leaf_at(i);
        unsafe {
            let ptr: *mut Self = &mut self.child_array_mut()[i+1];
            let node = ptr::read(ptr);
            ptr::copy(ptr.offset(1), ptr, self.m-i);
            (k, x, node)
        }
    }

    fn find(&self, depth: usize, k: &K) -> Option<&T> {
        match self.keys().binary_search_by(|i| Rel::cmp(i, k)) {
            Ok(i) => Some(&self.vals()[i]),
            Err(i) => if depth == 0 { None } else { self.children(depth)[i].find(depth-1, k) },
        }
    }

    fn find_mut(&mut self, depth: usize, k: &K) -> Option<&mut T> {
        match self.keys().binary_search_by(|i| Rel::cmp(i, k)) {
            Ok(i) => Some(&mut self.vals_mut()[i]),
            Err(i) => if depth == 0 { None } else { self.children_mut(depth)[i].find_mut(depth-1, k) },
        }
    }

    fn min(&self, depth: usize) -> (&K, &T) {
        debug_assert!(self.m != 0);
        if depth == 0 { (&self.keys()[0], &self.vals()[0]) } else { self.children(depth)[0].min(depth-1) }
    }

    fn min_mut(&mut self, depth: usize) -> (&mut K, &mut T) {
        debug_assert!(self.m != 0);
        let (keys, vals, children) = self.components_mut(depth);
        if depth == 0 { (&mut keys[0], &mut vals[0]) } else { children[0].min_mut(depth-1) }
    }

    fn max(&self, depth: usize) -> (&K, &T) {
        debug_assert!(self.m != 0);
        if depth == 0 { (&self.keys()[self.m-1], &self.vals()[self.m-1]) } else { self.children(depth)[self.m].max(depth-1) }
    }

    fn max_mut(&mut self, depth: usize) -> (&mut K, &mut T) {
        let m = self.m;
        debug_assert!(m != 0);
        let (keys, vals, children) = self.components_mut(depth);
        if depth == 0 { (&mut keys[m-1], &mut vals[m-1]) } else { children[m].max_mut(depth-1) }
    }

    fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, depth: usize, k: K, f: F) -> Result<Option<(K, T, Self)>, (K, T)> {
        let n_max = B::to_usize()<<1;
        match self.keys().binary_search_by(|i| Rel::cmp(&i, &k)) {
            Ok(i) => {
                mutate(&mut self.vals_mut()[i], |x| f(Some(x)));
                Ok(None)
            },
            Err(i) => {
                if self.m == n_max-1 { // full
                    match self.split(depth) {
                        Err(()) => Err((k, f(None))),
                        Ok((i, y, mut other)) => {
                            match if Rel::less(&k, &i) { self.insert_with(depth, k, f) } else { other.insert_with(depth, k, f) } {
                                Err(e) => {
                                    self.merge(other, depth, i, y);
                                    Err(e)
                                },
                                Ok(Some(_)) => panic!("impossible"),
                                Ok(None) => Ok(Some((i, y, other))),
                            }
                        },
                    }
                } else {
                    if depth == 0 { // we are a leaf
                        self.insert_here_leaf_at(i, k, f(None));
                        Ok(None)
                    } else {
                        match self.children_mut(depth)[i].insert_with(depth-1, k, f) {
                            Err(e) => Err(e),
                            Ok(None) => Ok(None),
                            Ok(Some((k, x, child))) => {
                                self.insert_here_at(i, k, x, child);
                                Ok(None)
                            },
                        }
                    }
                }
            },
        }
    }

    fn delete_from_child(&mut self, depth: usize, i: usize, k: &K) -> Option<(K, T)> {
        let opt_k_x = self.children_mut(depth)[i].delete(depth-1, k);
        if opt_k_x.is_some() && self.children(depth)[i].m < B::to_usize() {
            let j = if i == 0 { 1 } else { i-1 };
            if self.children(depth)[j].m < B::to_usize() {
                // TODO: balance on other side rather than merge if possible
                let (l, y, node) = self.delete_here_at(min(i, j));
                self.children_mut(depth)[min(i, j)].merge(node, depth-1, l, y);
            } else {
                let (keys, vals, children) = self.components_mut(depth);
                let (l, r) = children.split_at_mut(max(i, j));
                mutate2(&mut keys[min(i, j)], &mut vals[min(i, j)], |k, x| Self::balance(l.last_mut().unwrap(), r.first_mut().unwrap(), depth-1, k, x));
            }
        }
        opt_k_x
    }

    fn delete(&mut self, depth: usize, k: &K) -> Option<(K, T)> {
        match (depth, self.keys().binary_search_by(|i| Rel::cmp(&i, &k))) {
            (0, Ok(i))  => Some(self.delete_here_leaf_at(i)),
            (0, Err(_)) => None,
            (_, Ok(i))  => {
                {
                    let (keys, vals, children) = self.components_mut(depth);
                    let (j, y) = children[i].max_mut(depth-1);
                    mem::swap(j, &mut keys[i]);
                    mem::swap(y, &mut vals[i]);
                }
                self.delete_from_child(depth, i, k)
            },
            (_, Err(i)) => self.delete_from_child(depth, i, k),
        }
    }

    fn split(&mut self, depth: usize) -> Result<(K, T, Self), ()> {
        debug_assert!(self.m & 1 != 0);
        match Self::new(depth) {
            None => Err(()),
            Some(mut other) => Ok(unsafe {
                self.m >>= 1;
                other.m = self.m;
                ptr::copy(&self.key_array()[self.m+1], &mut other.key_array_mut()[0], self.m);
                ptr::copy(&self.val_array()[self.m+1], &mut other.val_array_mut()[0], self.m);
                if depth != 0 { ptr::copy(&self.child_array()[self.m+1], &mut other.child_array_mut()[0], self.m+1); }
                (ptr::read(&self.key_array()[self.m]),
                 ptr::read(&self.val_array()[self.m]),
                 other)
            }),
        }
    }

    fn merge(&mut self, other: Self, depth: usize, k: K, x: T) {
        debug_assert!(self.m + other.m + 1 < B::to_usize()<<1);
        let m = self.m;
        unsafe {
            ptr::write(&mut self.key_array_mut()[m], k);
            ptr::write(&mut self.val_array_mut()[m], x);
            ptr::copy(&other.key_array()[0], &mut self.key_array_mut()[m+1], other.m);
            ptr::copy(&other.val_array()[0], &mut self.val_array_mut()[m+1], other.m);
            if depth != 0 { ptr::copy(&other.children(depth)[0], &mut self.child_array_mut()[m+1], other.m+1); }
            self.m += other.m + 1;
            Self::dealloc(other.p, depth);
        }
    }

    fn balance(l: &mut Self, r: &mut Self, depth: usize, k: K, x: T) -> (K, T) { Self::shunt((l.m as isize-r.m as isize)>>1, l, r, depth, k, x) }

    fn shunt(s_n: isize, l: &mut Self, r: &mut Self, depth: usize, k: K, x: T) -> (K, T) {
        let n = s_n.abs() as usize;
        let (ml, mr) = (l.m, r.m);
        l.m = l.m.wrapping_sub(s_n as usize);
        r.m = r.m.wrapping_add(s_n as usize);
        debug_assert!(l.m < B::to_usize()<<1 && r.m < B::to_usize()<<1);
        match Ord::cmp(&s_n, &0) {
            Greater => unsafe {
                ptr::copy(&r.key_array()[0], &mut r.key_array_mut()[n], mr);
                ptr::copy(&r.val_array()[0], &mut r.val_array_mut()[n], mr);
                if depth != 0 { ptr::copy(&r.child_array()[0], &mut r.child_array_mut()[n], mr+1); }
                ptr::write(&mut r.key_array_mut()[n-1], k);
                ptr::write(&mut r.val_array_mut()[n-1], x);
                ptr::copy(l.key_array().get_unchecked(ml-n+1), &mut r.key_array_mut()[0], n-1);
                ptr::copy(l.val_array().get_unchecked(ml-n+1), &mut r.val_array_mut()[0], n-1);
                if depth != 0 { ptr::copy(&l.child_array()[ml-n+1], &mut r.child_array_mut()[0], n); }
                (ptr::read(&l.key_array()[ml-n]),
                 ptr::read(&l.val_array()[ml-n]))
            },
            Equal => (k, x),
            Less => unsafe {
                ptr::write(&mut l.key_array_mut()[ml], k);
                ptr::write(&mut l.val_array_mut()[ml], x);
                ptr::copy(&r.key_array()[0], &mut l.key_array_mut()[ml+1], n-1);
                ptr::copy(&r.val_array()[0], &mut l.val_array_mut()[ml+1], n-1);
                if depth != 0 { ptr::copy(&r.child_array()[0], &mut l.child_array_mut()[ml+1], n); }
                let (i, y) = (ptr::read(&r.key_array()[n-1]),
                              ptr::read(&r.val_array()[n-1]));
                ptr::copy(&r.key_array()[n], &mut r.key_array_mut()[0], mr-n);
                ptr::copy(&r.val_array()[n], &mut r.val_array_mut()[0], mr-n);
                if depth != 0 { ptr::copy(&r.child_array()[n], &mut r.child_array_mut()[0], mr-n+1); }
                (i, y)
            },
        }
    }

    fn size(&self, depth: usize) -> usize {
        self.m + if depth == 0 { 0 } else { self.children(depth).iter().map(|child| child.size(depth-1)).sum() }
    }

    fn foldl_with_key<A, F: Fn(A, &K, &T) -> A>(&self, depth: usize, z0: A, f: &F) -> A {
        if depth == 0 { return Iterator::zip(self.keys().iter(), self.vals().iter()).fold(z0, |z, (k, v)| f(z, k, v)) }
        let mut z = z0;
        for i in 0..self.m { z = f(self.children(depth)[i].foldl_with_key(depth-1, z, f), &self.keys()[i], &self.vals()[i]); }
        self.children(depth)[self.m].foldl_with_key(depth-1, z, f)
    }

    fn foldr_with_key<A, F: Fn(A, &K, &T) -> A>(&self, depth: usize, z0: A, f: &F) -> A {
        if depth == 0 { return Iterator::zip(self.keys().iter(), self.vals().iter()).rev().fold(z0, |z, (k, v)| f(z, k, v)) }
        let mut z = z0;
        z = self.children(depth)[self.m].foldr_with_key(depth-1, z, f);
        for i in (0..self.m).rev() { z = self.children(depth)[i].foldr_with_key(depth-1, f(z, &self.keys()[i], &self.vals()[i]), f); }
        z
    }

    fn drop(self, depth: usize) {
        debug_assert!(!self.p.is_null());
        unsafe {
            for p in self.vals() { ptr::read(p as *const T); }
            for p in self.keys() { ptr::read(p as *const K); }
            for p in self.children(depth) { ptr::read(p as *const Self).drop(depth-1); }
            Self::dealloc(self.p, depth);
        }
    }
}

impl<B: Unsigned, Rel: TotalOrderRelation<K>, K: fmt::Debug, T: fmt::Debug> BNode<B, Rel, K, T> {
    fn debug_fmt(&self, depth: usize, fmt: &mut fmt::Formatter) -> fmt::Result {
        try!(fmt::Debug::fmt(&self.p, fmt));
        try!(fmt.write_str(":["));
        for i in 0..self.m {
            if depth != 0 {
                try!(self.children(depth)[i].debug_fmt(depth-1, fmt));
            }
            try!(fmt.write_fmt(format_args!(",{:?}:{:?},", self.keys()[i], self.vals()[i])))
        }
        if depth != 0 { try!(self.children(depth)[self.m].debug_fmt(depth-1, fmt)); }
        try!(fmt.write_str("]"));
        Ok(())
    }
}

/// A B-node has `m` key-value pairs, and `m+1` children if it is a stem, with the keys between
/// the children so each key is greater than all keys in its left subtree and less than all keys
/// in its right subtree.
/// A node other than the root has `b-1 ≤ m ≤ 2b-1`, where `b` is the branching parametre of the
/// tree; the root may have fewer.
pub struct BTree<K, T, B: Unsigned = N::U2, Rel: TotalOrderRelation<K> = Ord> {
    root: BNode<B, Rel, K, T>,
    depth: usize,
}

impl<K, T, B: Unsigned, Rel: TotalOrderRelation<K>> BTree<K, T, B, Rel> {
    /// Make a new tree.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline] pub fn new() -> Option<Self> { BNode::new_leaf().map(|root| BTree { root: root, depth: 0 }) }

    /// Return number of elements.
    #[inline] pub fn size(&self) -> usize { self.root.size(self.depth) }

    /// Find value with given key `k`.
    #[inline] pub fn find(&self, k: &K) -> Option<&T> { self.root.find(self.depth, k) }

    /// Find value with given key `k`.
    #[inline] pub fn find_mut(&mut self, k: &K) -> Option<&mut T> { self.root.find_mut(self.depth, k) }

    /// Find value with minimum key.
    /// Return `None` if tree empty.
    #[inline] pub fn min(&self) -> Option<(&K, &T)> { if self.root.m == 0 { None } else { Some(self.root.min(self.depth)) } }

    /// Find value with maximum key.
    /// Return `None` if tree empty.
    #[inline] pub fn max(&self) -> Option<(&K, &T)> { if self.root.m == 0 { None } else { Some(self.root.max(self.depth)) } }

    /// Find value with minimum key.
    /// Return `None` if tree empty.
    #[inline] pub fn min_mut(&mut self) -> Option<(&K, &mut T)> { if self.root.m == 0 { None } else { let (k, x) = self.root.min_mut(self.depth); Some((&*k, x)) } }

    /// Find value with maximum key.
    /// Return `None` if tree empty.
    #[inline] pub fn max_mut(&mut self) -> Option<(&K, &mut T)> { if self.root.m == 0 { None } else { let (k, x) = self.root.max_mut(self.depth); Some((&*k, x)) } }

    /// Seek `k`; if not found, insert `f(None)` there; if found, modify the value there from `x` to `f(Some(x))`.
    ///
    /// # Failures
    ///
    /// Returns `Err` if allocation fails.
    #[inline] pub fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, k: K, f: F) -> Result<(), (K, T)> {
        let p = unsafe { allocate(BNode::<B, Rel, K, T>::stem_size(), BNode::<B, Rel, K, T>::stem_align()) };
        if p.is_null() { return Err((k, f(None))) }
        let d = || unsafe { deallocate(p, BNode::<B, Rel, K, T>::stem_size(), BNode::<B, Rel, K, T>::stem_align()) };
        match self.root.insert_with(self.depth, k, f) {
            Err(e) => { d(); Err(e) },
            Ok(None) => { d(); Ok(()) },
            Ok(Some((k, x, new))) => {
                let mut new_root = BNode { φ: PhantomData, m: 0, p: p };
                unsafe { ptr::write(&mut new_root.child_array_mut()[0], mem::replace(&mut self.root, new_root)); }
                self.depth += 1;
                self.root.insert_here_at(0, k, x, new);
                Ok(())
            },
        }
    }

    #[deprecated(since = "0.7.1", note = "now called `insert`")]
    #[inline] pub fn replace(&mut self, k: K, x: T) -> Result<Option<T>, (K, T)> { self.insert(k, x) }

    /// Insert `x` at `k` and return `Some(x)` if there was already a value `x` there.
    ///
    /// # Failures
    ///
    /// Returns `Err` if allocation fails.
    #[inline] pub fn insert(&mut self, k: K, x: T) -> Result<Option<T>, (K, T)> {
        let mut opt_y = None;
        self.insert_with(k, |opt_x| { opt_y = opt_x; x }).map(|()| opt_y)
    }

    /// Seek `k`; if found, delete it and value `x` there and return `Some((k, x))`.
    #[inline] pub fn delete(&mut self, k: &K) -> Option<(K, T)> {
        let opt_k_x = self.root.delete(self.depth, k);
        if self.root.m == 0 && self.depth != 0 {
            let node = mem::replace(&mut self.root.children_mut(self.depth)[0], BNode { φ: PhantomData, m: 0, p: ptr::null_mut() });
            unsafe { BNode::<B, Rel, K, T>::dealloc(mem::replace(&mut self.root, node).p, self.depth) };
            self.depth -= 1;
        }
        opt_k_x
    }

    #[deprecated(since = "0.10.3", note = "now called `foldl_with_key`")]
    #[inline] pub fn fold_with_key<A, F: Fn(A, &K, &T) -> A>(&self, z0: A, f: F) -> A { self.root.foldl_with_key(self.depth, z0, &f) }

    /// Fold elements in forward order.
    #[inline] pub fn foldl_with_key<A, F: Fn(A, &K, &T) -> A>(&self, z0: A, f: F) -> A { self.root.foldl_with_key(self.depth, z0, &f) }

    /// Fold elements in backward order.
    #[inline] pub fn foldr_with_key<A, F: Fn(A, &K, &T) -> A>(&self, z0: A, f: F) -> A { self.root.foldr_with_key(self.depth, z0, &f) }
}

unsafe impl<K: Send, T: Send, B: Unsigned, Rel: TotalOrderRelation<K>> Send for BTree<K, T, B, Rel> {}
unsafe impl<K: Sync, T: Sync, B: Unsigned, Rel: TotalOrderRelation<K>> Sync for BTree<K, T, B, Rel> {}

impl<K, T, B: Unsigned, Rel: TotalOrderRelation<K>> Drop for BTree<K, T, B, Rel> {
    #[inline] fn drop(&mut self) { mem::replace(&mut self.root, BNode { φ: PhantomData, m: 0, p: ptr::null_mut() }).drop(self.depth) }
}

impl<K: fmt::Debug, T: fmt::Debug, B: Unsigned, Rel: TotalOrderRelation<K>> fmt::Debug for BTree<K, T, B, Rel> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if cfg!(test) { self.root.debug_fmt(self.depth, fmt) }
        else { self.foldl_with_key(fmt.debug_map(), |mut d, k, x| { d.entry(k, x); d }).finish() }
    }
}

#[cfg(test)] mod tests {
    use core::fmt;
    use quickcheck::*;
    use std::vec::*;

    use ::rel;
    use ::typenum::consts as N;
    use ::util::*;
    use super::*;

    fn test_size<T: Copy + Ord + fmt::Debug>(mut kv: Vec<T>) -> bool {
        let mut t = BTree::<_, _>::new().unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        kv.sort();
        kv.dedup();
        t.size() == kv.len()
    }
    #[quickcheck] fn size_unit(kv: Vec<()>) -> bool { test_size(kv) }
    #[quickcheck] fn size_bool(kv: Vec<bool>) -> bool { test_size(kv) }
    #[quickcheck] fn size_abc(kv: Vec<ABC>) -> bool { test_size(kv) }
    #[quickcheck] fn size_usize(kv: Vec<usize>) -> bool { test_size(kv) }

    fn test_order<T: Copy + Ord + fmt::Debug>(kv: Vec<T>) {
        let mut t = BTree::<_, _>::new().unwrap();
        for k in kv { t.insert(k, ()).unwrap(); }
        t.foldl_with_key(None, |opt_m, &n, &()| {
                             match opt_m { None => (), Some(m) => if m > n { panic!("out of order") } };
                             Some(n)
                         });
    }
    #[quickcheck] fn order_unit(kv: Vec<()>) { test_order(kv) }
    #[quickcheck] fn order_bool(kv: Vec<bool>) { test_order(kv) }
    #[quickcheck] fn order_abc(kv: Vec<ABC>) { test_order(kv) }
    #[quickcheck] fn order_usize(kv: Vec<usize>) { test_order(kv) }

    fn test_find<T: Copy + Ord + fmt::Debug>(kv: Vec<T>) -> bool {
        let mut t = BTree::<_, _>::new().unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        kv.iter().all(|&k| t.find(&k).is_some())
    }
    #[quickcheck] fn find_unit(kv: Vec<()>) -> bool { test_find(kv) }
    #[quickcheck] fn find_bool(kv: Vec<bool>) -> bool { test_find(kv) }
    #[quickcheck] fn find_abc(kv: Vec<ABC>) -> bool { test_find(kv) }
    #[quickcheck] fn find_usize(kv: Vec<usize>) -> bool { test_find(kv) }

    fn test_min_max<T: Copy + Ord + fmt::Debug>(kv: Vec<T>) -> bool {
        let mut t = BTree::<_, _>::new().unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        t.min().map(|k_x| k_x.0) == kv.iter().min() &&
        t.max().map(|k_x| k_x.0) == kv.iter().max()
    }
    #[quickcheck] fn min_max_unit(kv: Vec<()>) -> bool { test_min_max(kv) }
    #[quickcheck] fn min_max_bool(kv: Vec<bool>) -> bool { test_min_max(kv) }
    #[quickcheck] fn min_max_abc(kv: Vec<ABC>) -> bool { test_min_max(kv) }
    #[quickcheck] fn min_max_usize(kv: Vec<usize>) -> bool { test_min_max(kv) }

    fn test_deletion<T: Copy + Ord + fmt::Debug>(kv: Vec<T>) -> TestResult {
        if kv.len() == 0 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new().unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        t.delete(&kv[0]);
        TestResult::from_bool(t.find(&kv[0]).is_none())
    }
    #[quickcheck] fn deletion_unit(kv: Vec<()>) -> TestResult { test_deletion(kv) }
    #[quickcheck] fn deletion_bool(kv: Vec<bool>) -> TestResult { test_deletion(kv) }
    #[quickcheck] fn deletion_abc(kv: Vec<ABC>) -> TestResult { test_deletion(kv) }
    #[quickcheck] fn deletion_usize(kv: Vec<usize>) -> TestResult { test_deletion(kv) }

    fn test_total_deletion<T: Copy + Ord + fmt::Debug>(kv: Vec<T>) -> TestResult {
        let mut t = BTree::<_, _>::new().unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        for &k in kv.iter() { t.delete(&k); }
        TestResult::from_bool(kv.iter().all(|k| t.find(k).is_none()))
    }
    #[quickcheck] fn total_deletion_unit(kv: Vec<()>) -> TestResult { test_total_deletion(kv) }
    #[quickcheck] fn total_deletion_bool(kv: Vec<bool>) -> TestResult { test_total_deletion(kv) }
    #[quickcheck] fn total_deletion_abc(kv: Vec<ABC>) -> TestResult { test_total_deletion(kv) }
    #[quickcheck] fn total_deletion_usize(kv: Vec<usize>) -> TestResult { test_total_deletion(kv) }
}
