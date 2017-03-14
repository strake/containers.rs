//! Balanced search trees

use alloc::heap::*;
use core::borrow::Borrow;
use core::cmp::{ max, min };
use core::cmp::Ordering::*;
use core::fmt;
use core::marker::PhantomData;
use core::mem;
use core::ptr;
use core::slice;

use util::byte_size::ByteSize;
use rel::ord::*;
use util::*;

struct BNode<Rel: TotalOrderRelation<K>, K, T> {
    φ: PhantomData<(Rel, K, T)>,
    m: usize,
    p: *mut u8,
}

enum Which<K> { Min, Max, Key(K), }
use self::Which::*;

impl<Rel: TotalOrderRelation<K>, K, T> BNode<Rel, K, T> {
    fn new(b: usize, depth: usize) -> Option<Self> { if depth == 0 { Self::new_leaf(b) } else { Self::new_stem(b) } }

    fn new_stem(b: usize) -> Option<Self> {
        let p = unsafe { allocate(Self::stem_size(b), Self::stem_align()) };
        if p.is_null() { None } else {
            Some(BNode { φ: PhantomData, m: 0, p: p })
        }
    }

    fn new_leaf(b: usize) -> Option<Self> {
        let p = if Self::leaf_size(b) == 0 { EMPTY as *mut _ }
                else { unsafe { allocate(Self::leaf_size(b), Self::leaf_align()) } };
        if p.is_null() { None } else {
            Some(BNode { φ: PhantomData, m: 0, p: p })
        }
    }

    unsafe fn dealloc(ptr: *mut u8, b: usize, depth: usize) {
        if depth == 0 && Self::leaf_size(b) == 0 { return };
        deallocate(ptr,
                   if depth == 0 { Self::leaf_size (b) } else { Self::stem_size (b) },
                   if depth == 0 { Self::leaf_align( ) } else { Self::stem_align( ) });
    }

    fn stem_align() -> usize { mem::align_of::<(K, T, Self)>() }

    fn leaf_align() -> usize { mem::align_of::<(K, T)>() }

    fn stem_size(b: usize) -> usize {
        let n_max = b<<1;
        (ByteSize::array::<T>(n_max-1) + ByteSize::array::<K>(n_max-1) + ByteSize::array::<Self>(n_max)).length
    }

    fn leaf_size(b: usize) -> usize {
        let n_max = b<<1;
        (ByteSize::array::<T>(n_max-1) + ByteSize::array::<K>(n_max-1)).length
    }

    unsafe fn component_arrays_mut(&mut self, b: usize) -> (&mut [K], &mut [T], &mut [Self]) {
        let n_max = b<<1;
        let vals_ptr = self.p as *mut T;
        let keys_ptr = align_mut_ptr(vals_ptr.offset(n_max as isize-1) as *mut K);
        let children_ptr = align_mut_ptr(keys_ptr.offset(n_max as isize-1) as *mut Self);
        (slice::from_raw_parts_mut(keys_ptr, n_max-1),
         slice::from_raw_parts_mut(vals_ptr, n_max-1),
         slice::from_raw_parts_mut(children_ptr, n_max))
    }

    fn components_mut(&mut self, b: usize, depth: usize) -> (&mut [K], &mut [T], &mut [Self]) {
        let m = self.m;
        let n = if depth == 0 { 0 } else { m+1 };
        let (keys, vals, children) = unsafe { self.component_arrays_mut(b) };
        (&mut keys[0..m], &mut vals[0..m], &mut children[0..n])
    }

    #[allow(mutable_transmutes)]
    unsafe fn component_arrays(&self, b: usize) -> (&[K], &[T], &[Self]) {
        let (keys, vals, children) = mem::transmute::<&Self, &mut Self>(self).component_arrays_mut(b);
        (keys, vals, children)
    }

    unsafe fn val_array(&self, b: usize) -> &[T] { self.component_arrays(b).1 }

    fn vals(&self, b: usize) -> &[T] { &(unsafe { self.val_array(b) })[0..self.m] }

    unsafe fn val_array_mut(&mut self, b: usize) -> &mut [T] { self.component_arrays_mut(b).1 }

    fn vals_mut(&mut self, b: usize) -> &mut [T] { self.components_mut(b, 0).1 }

    unsafe fn key_array(&self, b: usize) -> &[K] { self.component_arrays(b).0 }

    fn keys(&self, b: usize) -> &[K] { &(unsafe { self.key_array(b) })[0..self.m] }

    unsafe fn key_array_mut(&mut self, b: usize) -> &mut [K] { self.component_arrays_mut(b).0 }

    fn keys_mut(&mut self, b: usize) -> &mut [K] { self.components_mut(b, 0).0 }

    unsafe fn child_array(&self, b: usize) -> &[Self] { self.component_arrays(b).2 }

    fn children(&self, b: usize, depth: usize) -> &[Self] { &(unsafe { self.child_array(b) })[0..if depth == 0 { 0 } else { self.m+1 }] }

    unsafe fn child_array_mut(&mut self, b: usize) -> &mut [Self] { self.component_arrays_mut(b).2 }

    fn children_mut(&mut self, b: usize, depth: usize) -> &mut [Self] { self.components_mut(b, depth).2 }

    fn insert_here_leaf_at(&mut self, b: usize, i: usize, k: K, x: T) {
        unsafe {
            let k_ptr: *mut K = &mut self.key_array_mut(b)[i];
            ptr::copy(k_ptr, k_ptr.offset(1), self.m-i);
            ptr::write(k_ptr, k);
            let x_ptr: *mut T = &mut self.val_array_mut(b)[i];
            ptr::copy(x_ptr, x_ptr.offset(1), self.m-i);
            ptr::write(x_ptr, x);
        }
        self.m += 1;
    }

    fn insert_here_at(&mut self, b: usize, i: usize, k: K, x: T, child: Self) {
        unsafe {
            let ptr: *mut Self = &mut self.child_array_mut(b)[i+1];
            ptr::copy(ptr, ptr.offset(1), self.m-i);
            ptr::write(ptr, child);
        }
        self.insert_here_leaf_at(b, i, k, x);
    }

    fn delete_here_leaf_at(&mut self, b: usize, i: usize) -> (K, T) {
        self.m -= 1;
        unsafe {
            let k_ptr: *mut K = &mut self.key_array_mut(b)[i];
            let k = ptr::read(k_ptr);
            ptr::copy(k_ptr.offset(1), k_ptr, self.m-i);
            let x_ptr: *mut T = &mut self.val_array_mut(b)[i];
            let x = ptr::read(x_ptr);
            ptr::copy(x_ptr.offset(1), x_ptr, self.m-i);
            (k, x)
        }
    }

    fn delete_here_at(&mut self, b: usize, i: usize) -> (K, T, Self) {
        let (k, x) = self.delete_here_leaf_at(b, i);
        unsafe {
            let ptr: *mut Self = &mut self.child_array_mut(b)[i+1];
            let node = ptr::read(ptr);
            ptr::copy(ptr.offset(1), ptr, self.m-i);
            (k, x, node)
        }
    }

    fn find<Q: ?Sized>(&self, b: usize, depth: usize, k: &Q) -> Option<&T>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        match self.keys(b).binary_search_by(|i| Rel::cmp(i.borrow(), k)) {
            Ok(i) => Some(&self.vals(b)[i]),
            Err(i) => if depth == 0 { None } else { self.children(b, depth)[i].find(b, depth-1, k) },
        }
    }

    fn find_mut<Q: ?Sized>(&mut self, b: usize, depth: usize, k: &Q) -> Option<&mut T>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        match self.keys(b).binary_search_by(|i| Rel::cmp(i.borrow(), k)) {
            Ok(i) => Some(&mut self.vals_mut(b)[i]),
            Err(i) => if depth == 0 { None } else { self.children_mut(b, depth)[i].find_mut(b, depth-1, k) },
        }
    }

    fn min(&self, b: usize, depth: usize) -> (&K, &T) {
        debug_assert_ne!(0, self.m);
        if depth == 0 { (&self.keys(b)[0], &self.vals(b)[0]) } else { self.children(b, depth)[0].min(b, depth-1) }
    }

    fn min_mut(&mut self, b: usize, depth: usize) -> (&mut K, &mut T) {
        debug_assert_ne!(0, self.m);
        let (keys, vals, children) = self.components_mut(b, depth);
        if depth == 0 { (&mut keys[0], &mut vals[0]) } else { children[0].min_mut(b, depth-1) }
    }

    fn max(&self, b: usize, depth: usize) -> (&K, &T) {
        debug_assert_ne!(0, self.m);
        if depth == 0 { (&self.keys(b)[self.m-1], &self.vals(b)[self.m-1]) } else { self.children(b, depth)[self.m].max(b, depth-1) }
    }

    fn max_mut(&mut self, b: usize, depth: usize) -> (&mut K, &mut T) {
        let m = self.m;
        debug_assert_ne!(0, m);
        let (keys, vals, children) = self.components_mut(b, depth);
        if depth == 0 { (&mut keys[m-1], &mut vals[m-1]) } else { children[m].max_mut(b, depth-1) }
    }

    fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, b: usize, depth: usize, k: K, f: F) -> Result<Option<(K, T, Self)>, (K, T)> {
        let n_max = b<<1;
        match self.keys(b).binary_search_by(|i| Rel::cmp(&i, &k)) {
            Ok(i) => {
                mutate(&mut self.vals_mut(b)[i], |x| f(Some(x)));
                Ok(None)
            },
            Err(i) => {
                if self.m == n_max-1 { // full
                    match self.split(b, depth) {
                        Err(()) => Err((k, f(None))),
                        Ok((i, y, mut other)) => {
                            match if Rel::less(&k, &i) { self.insert_with(b, depth, k, f) } else { other.insert_with(b, depth, k, f) } {
                                Err(e) => {
                                    self.merge(other, b, depth, i, y);
                                    Err(e)
                                },
                                Ok(Some(_)) => panic!("impossible"),
                                Ok(None) => Ok(Some((i, y, other))),
                            }
                        },
                    }
                } else {
                    if depth == 0 { // we are a leaf
                        self.insert_here_leaf_at(b, i, k, f(None));
                        Ok(None)
                    } else {
                        match self.children_mut(b, depth)[i].insert_with(b, depth-1, k, f) {
                            Err(e) => Err(e),
                            Ok(None) => Ok(None),
                            Ok(Some((k, x, child))) => {
                                self.insert_here_at(b, i, k, x, child);
                                Ok(None)
                            },
                        }
                    }
                }
            },
        }
    }

    fn delete_which_from_child<Q: ?Sized>(&mut self, b: usize, depth: usize, i: usize,
                                          which: Which<&Q>) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        let opt_k_x = self.children_mut(b, depth)[i].delete_which(b, depth-1, which);
        if opt_k_x.is_some() && self.children(b, depth)[i].m < b {
            let j = if i == 0 { 1 } else { i-1 };
            if self.children(b, depth)[j].m < b {
                // TODO: balance on other side rather than merge if possible
                let (l, y, node) = self.delete_here_at(b, min(i, j));
                self.children_mut(b, depth)[min(i, j)].merge(node, b, depth-1, l, y);
            } else {
                let (keys, vals, children) = self.components_mut(b, depth);
                let (l, r) = children.split_at_mut(max(i, j));
                mutate2(&mut keys[min(i, j)], &mut vals[min(i, j)],
                        |k, x| Self::balance(l.last_mut().unwrap(), r.first_mut().unwrap(),
                                             b, depth-1, k, x));
            }
        }
        opt_k_x
    }

    fn delete<Q: ?Sized>(&mut self, b: usize, depth: usize, k: &Q) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        match (depth, self.keys(b).binary_search_by(|i| Rel::cmp(i.borrow(), k))) {
            (0, Ok(i))  => Some(self.delete_here_leaf_at(b, i)),
            (0, Err(_)) => None,
            (_, Ok(i))  => {
                {
                    let (keys, vals, children) = self.components_mut(b, depth);
                    let (j, y) = children[i].max_mut(b, depth-1);
                    mem::swap(j, &mut keys[i]);
                    mem::swap(y, &mut vals[i]);
                }
                self.delete_which_from_child(b, depth, i, Key(k))
            },
            (_, Err(i)) => self.delete_which_from_child(b, depth, i, Key(k)),
        }
    }

    fn delete_min(&mut self, b: usize, depth: usize) -> Option<(K, T)> {
        if 0 == self.m { None } else if 0 == depth { Some(self.delete_here_leaf_at(b, 0)) }
                                     else { self.delete_which_from_child(b, depth, 0, Min) }
    }

    fn delete_max(&mut self, b: usize, depth: usize) -> Option<(K, T)> {
        let m = self.m;
        if 0 == self.m { None } else if 0 == depth { Some(self.delete_here_leaf_at(b, m-1)) }
                                     else { self.delete_which_from_child(b, depth, m, Max) }
    }

    fn delete_which<Q: ?Sized>(&mut self, b: usize, depth: usize, which: Which<&Q>) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        match which {
            Min => self.delete_min(b, depth),
            Max => self.delete_max(b, depth),
            Key(k) => self.delete(b, depth, k),
        }
    }

    fn split(&mut self, b: usize, depth: usize) -> Result<(K, T, Self), ()> {
        debug_assert_ne!(0, self.m & 1);
        match Self::new(b, depth) {
            None => Err(()),
            Some(mut other) => Ok(unsafe {
                self.m >>= 1;
                other.m = self.m;
                ptr::copy(&self.key_array(b)[self.m+1], &mut other.key_array_mut(b)[0], self.m);
                ptr::copy(&self.val_array(b)[self.m+1], &mut other.val_array_mut(b)[0], self.m);
                if depth != 0 { ptr::copy(&self.child_array(b)[self.m+1], &mut other.child_array_mut(b)[0], self.m+1); }
                (ptr::read(&self.key_array(b)[self.m]),
                 ptr::read(&self.val_array(b)[self.m]),
                 other)
            }),
        }
    }

    fn merge(&mut self, other: Self, b: usize, depth: usize, k: K, x: T) {
        debug_assert!(self.m + other.m + 1 < b<<1);
        let m = self.m;
        unsafe {
            ptr::write(&mut self.key_array_mut(b)[m], k);
            ptr::write(&mut self.val_array_mut(b)[m], x);
            ptr::copy(&other.key_array(b)[0], &mut self.key_array_mut(b)[m+1], other.m);
            ptr::copy(&other.val_array(b)[0], &mut self.val_array_mut(b)[m+1], other.m);
            if depth != 0 { ptr::copy(&other.children(b, depth)[0], &mut self.child_array_mut(b)[m+1], other.m+1); }
            self.m += other.m + 1;
            Self::dealloc(other.p, b, depth);
        }
    }

    fn balance(l: &mut Self, r: &mut Self, b: usize, depth: usize, k: K, x: T) -> (K, T) {
        Self::shunt((l.m as isize-r.m as isize)>>1, l, r, b, depth, k, x)
    }

    fn shunt(s_n: isize, l: &mut Self, r: &mut Self, b: usize, depth: usize, k: K, x: T) -> (K, T) {
        let n = s_n.abs() as usize;
        let (ml, mr) = (l.m, r.m);
        l.m = l.m.wrapping_sub(s_n as usize);
        r.m = r.m.wrapping_add(s_n as usize);
        debug_assert!(l.m < b<<1 && r.m < b<<1);
        match Ord::cmp(&s_n, &0) {
            Greater => unsafe {
                ptr::copy(&r.key_array(b)[0], &mut r.key_array_mut(b)[n], mr);
                ptr::copy(&r.val_array(b)[0], &mut r.val_array_mut(b)[n], mr);
                if depth != 0 { ptr::copy(&r.child_array(b)[0], &mut r.child_array_mut(b)[n], mr+1); }
                ptr::write(&mut r.key_array_mut(b)[n-1], k);
                ptr::write(&mut r.val_array_mut(b)[n-1], x);
                ptr::copy(l.key_array(b).get_unchecked(ml-n+1), &mut r.key_array_mut(b)[0], n-1);
                ptr::copy(l.val_array(b).get_unchecked(ml-n+1), &mut r.val_array_mut(b)[0], n-1);
                if depth != 0 { ptr::copy(&l.child_array(b)[ml-n+1], &mut r.child_array_mut(b)[0], n); }
                (ptr::read(&l.key_array(b)[ml-n]),
                 ptr::read(&l.val_array(b)[ml-n]))
            },
            Equal => (k, x),
            Less => unsafe {
                ptr::write(&mut l.key_array_mut(b)[ml], k);
                ptr::write(&mut l.val_array_mut(b)[ml], x);
                ptr::copy(&r.key_array(b)[0], &mut l.key_array_mut(b)[ml+1], n-1);
                ptr::copy(&r.val_array(b)[0], &mut l.val_array_mut(b)[ml+1], n-1);
                if depth != 0 { ptr::copy(&r.child_array(b)[0], &mut l.child_array_mut(b)[ml+1], n); }
                let (i, y) = (ptr::read(&r.key_array(b)[n-1]),
                              ptr::read(&r.val_array(b)[n-1]));
                ptr::copy(&r.key_array(b)[n], &mut r.key_array_mut(b)[0], mr-n);
                ptr::copy(&r.val_array(b)[n], &mut r.val_array_mut(b)[0], mr-n);
                if depth != 0 { ptr::copy(&r.child_array(b)[n], &mut r.child_array_mut(b)[0], mr-n+1); }
                (i, y)
            },
        }
    }

    fn size(&self, b: usize, depth: usize) -> usize {
        self.m + if depth == 0 { 0 } else { self.children(b, depth).iter().map(|child| child.size(b, depth-1)).sum() }
    }

    fn foldl_with_key<A, F: FnMut(A, &K, &T) -> A>(&self, b: usize, depth: usize, z0: A, f: &mut F) -> A {
        if depth == 0 { return Iterator::zip(self.keys(b).iter(), self.vals(b).iter()).fold(z0, |z, (k, v)| f(z, k, v)) }
        let mut z = z0;
        for i in 0..self.m {
            z = self.children(b, depth)[i].foldl_with_key(b, depth-1, z, f);
            z = f(z, &self.keys(b)[i], &self.vals(b)[i]);
        }
        self.children(b, depth)[self.m].foldl_with_key(b, depth-1, z, f)
    }

    fn foldr_with_key<A, F: FnMut(A, &K, &T) -> A>(&self, b: usize, depth: usize, z0: A, f: &mut F) -> A {
        if depth == 0 { return Iterator::zip(self.keys(b).iter(), self.vals(b).iter()).rev().fold(z0, |z, (k, v)| f(z, k, v)) }
        let mut z = z0;
        z = self.children(b, depth)[self.m].foldr_with_key(b, depth-1, z, f);
        for i in (0..self.m).rev() {
            z = f(z, &self.keys(b)[i], &self.vals(b)[i]);
            z = self.children(b, depth)[i].foldr_with_key(b, depth-1, z, f);
        }
        z
    }

    fn drop(self, b: usize, depth: usize) {
        debug_assert!(!self.p.is_null());
        unsafe {
            for p in self.vals(b) { ptr::read(p as *const T); }
            for p in self.keys(b) { ptr::read(p as *const K); }
            for p in self.children(b, depth) { ptr::read(p as *const Self).drop(b, depth-1); }
            Self::dealloc(self.p, b, depth);
        }
    }
}

impl<Rel: TotalOrderRelation<K>, K: fmt::Debug, T: fmt::Debug> BNode<Rel, K, T> {
    fn debug_fmt(&self, b: usize, depth: usize, fmt: &mut fmt::Formatter) -> fmt::Result {
        try!(fmt::Debug::fmt(&self.p, fmt));
        try!(fmt.write_str(":["));
        for i in 0..self.m {
            if depth != 0 {
                try!(self.children(b, depth)[i].debug_fmt(b, depth-1, fmt));
            }
            try!(fmt.write_fmt(format_args!(",{:?}:{:?},", self.keys(b)[i], self.vals(b)[i])))
        }
        if depth != 0 { try!(self.children(b, depth)[self.m].debug_fmt(b, depth-1, fmt)); }
        try!(fmt.write_str("]"));
        Ok(())
    }
}

/// A B-node has `m` key-value pairs, and `m+1` children if it is a stem, with the keys between
/// the children so each key is greater than all keys in its left subtree and less than all keys
/// in its right subtree.
/// A node other than the root has `b-1 ≤ m ≤ 2b-1`, where `b` is the branching parametre of the
/// tree; the root may have fewer.
pub struct BTree<K, T, Rel: TotalOrderRelation<K> = Ord> {
    root: BNode<Rel, K, T>,
    depth: usize,
    b: usize,
}

impl<K, T, Rel: TotalOrderRelation<K>> BTree<K, T, Rel> {
    /// Make a new tree.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline] pub fn new(b: usize) -> Option<Self> { BNode::new_leaf(b).map(|root| BTree { root: root, depth: 0, b: b }) }

    /// Return number of elements.
    #[inline] pub fn size(&self) -> usize { self.root.size(self.b, self.depth) }

    /// Find value with given key `k`.
    #[inline] pub fn find<Q: ?Sized>(&self, k: &Q) -> Option<&T>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> { self.root.find(self.b, self.depth, k) }

    /// Find value with given key `k`.
    #[inline] pub fn find_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut T>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> { self.root.find_mut(self.b, self.depth, k) }

    /// Find value with minimum key.
    /// Return `None` if tree empty.
    #[inline] pub fn min(&self) -> Option<(&K, &T)> { if self.root.m == 0 { None } else { Some(self.root.min(self.b, self.depth)) } }

    /// Find value with maximum key.
    /// Return `None` if tree empty.
    #[inline] pub fn max(&self) -> Option<(&K, &T)> { if self.root.m == 0 { None } else { Some(self.root.max(self.b, self.depth)) } }

    /// Find value with minimum key.
    /// Return `None` if tree empty.
    #[inline] pub fn min_mut(&mut self) -> Option<(&K, &mut T)> { if self.root.m == 0 { None } else { let (k, x) = self.root.min_mut(self.b, self.depth); Some((&*k, x)) } }

    /// Find value with maximum key.
    /// Return `None` if tree empty.
    #[inline] pub fn max_mut(&mut self) -> Option<(&K, &mut T)> { if self.root.m == 0 { None } else { let (k, x) = self.root.max_mut(self.b, self.depth); Some((&*k, x)) } }

    /// Seek `k`; if not found, insert `f(None)` there; if found, modify the value there from `x` to `f(Some(x))`.
    ///
    /// # Failures
    ///
    /// Returns `Err` if allocation fails.
    #[inline] pub fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, k: K, f: F) -> Result<(), (K, T)> {
        let b = self.b;
        let p = unsafe { allocate(BNode::<Rel, K, T>::stem_size(b), BNode::<Rel, K, T>::stem_align()) };
        if p.is_null() { return Err((k, f(None))) }
        let d = || unsafe { deallocate(p, BNode::<Rel, K, T>::stem_size(b), BNode::<Rel, K, T>::stem_align()) };
        match self.root.insert_with(b, self.depth, k, f) {
            Err(e) => { d(); Err(e) },
            Ok(None) => { d(); Ok(()) },
            Ok(Some((k, x, new))) => {
                let mut new_root = BNode { φ: PhantomData, m: 0, p: p };
                unsafe { ptr::write(&mut new_root.child_array_mut(b)[0],
                                    mem::replace(&mut self.root, new_root)); }
                self.depth += 1;
                self.root.insert_here_at(b, 0, k, x, new);
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

    #[inline] fn delete_which<Q: ?Sized>(&mut self, which: Which<&Q>) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        let opt_k_x = self.root.delete_which(self.b, self.depth, which);
        if self.root.m == 0 && self.depth != 0 {
            let node = mem::replace(&mut self.root.children_mut(self.b, self.depth)[0],
                                    BNode { φ: PhantomData, m: 0, p: ptr::null_mut() });
            unsafe { BNode::<Rel, K, T>::dealloc(mem::replace(&mut self.root, node).p, self.b, self.depth) };
            self.depth -= 1;
        }
        opt_k_x
    }

    /// Seek `k`; if found, delete it and value `x` there and return `Some((k, x))`.
    #[inline] pub fn delete<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> { self.delete_which(Key(k)) }

    #[inline] pub fn delete_min(&mut self) -> Option<(K, T)> { self.delete_which(Min) }
    #[inline] pub fn delete_max(&mut self) -> Option<(K, T)> { self.delete_which(Max) }

    /// Fold elements in forward order.
    #[inline] pub fn foldl_with_key<A, F: FnMut(A, &K, &T) -> A>(&self, z0: A, mut f: F) -> A { self.root.foldl_with_key(self.b, self.depth, z0, &mut f) }

    /// Fold elements in backward order.
    #[inline] pub fn foldr_with_key<A, F: FnMut(A, &K, &T) -> A>(&self, z0: A, mut f: F) -> A { self.root.foldr_with_key(self.b, self.depth, z0, &mut f) }
}

unsafe impl<K: Send, T: Send, Rel: TotalOrderRelation<K>> Send for BTree<K, T, Rel> {}
unsafe impl<K: Sync, T: Sync, Rel: TotalOrderRelation<K>> Sync for BTree<K, T, Rel> {}

impl<K, T, Rel: TotalOrderRelation<K>> Drop for BTree<K, T, Rel> {
    #[inline] fn drop(&mut self) { mem::replace(&mut self.root, BNode { φ: PhantomData, m: 0, p: ptr::null_mut() }).drop(self.b, self.depth) }
}

impl<K: fmt::Debug, T: fmt::Debug, Rel: TotalOrderRelation<K>> fmt::Debug for BTree<K, T, Rel> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if cfg!(test) { self.root.debug_fmt(self.b, self.depth, fmt) }
        else { self.foldl_with_key(fmt.debug_map(), |mut d, k, x| { d.entry(k, x); d }).finish() }
    }
}

#[cfg(test)] mod tests {
    use core::fmt;
    use quickcheck::*;
    use std::cmp::Ord;
    use std::vec::*;

    use super::*;

    fn test_size<T: Copy + Ord + fmt::Debug>(b: usize, mut kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(b).unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        kv.sort();
        kv.dedup();
        TestResult::from_bool(t.size() == kv.len())
    }
    #[quickcheck] fn size_unit(b: usize, kv: Vec<()>) -> TestResult { test_size(b, kv) }
    #[quickcheck] fn size_bool(b: usize, kv: Vec<bool>) -> TestResult { test_size(b, kv) }
    #[quickcheck] fn size_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_size(b, kv) }
    #[quickcheck] fn size_usize(b: usize, kv: Vec<usize>) -> TestResult { test_size(b, kv) }

    fn test_order<T: Copy + Ord + fmt::Debug>(b: usize, kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(b).unwrap();
        for k in kv { t.insert(k, ()).unwrap(); }
        t.foldl_with_key(None, |opt_m, &n, &()| {
                             match opt_m { None => (), Some(m) => if m > n { panic!("out of order") } };
                             Some(n)
                         });
        TestResult::passed()
    }
    #[quickcheck] fn order_unit(b: usize, kv: Vec<()>) -> TestResult { test_order(b, kv) }
    #[quickcheck] fn order_bool(b: usize, kv: Vec<bool>) -> TestResult { test_order(b, kv) }
    #[quickcheck] fn order_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_order(b, kv) }
    #[quickcheck] fn order_usize(b: usize, kv: Vec<usize>) -> TestResult { test_order(b, kv) }

    fn test_find<T: Copy + Ord + fmt::Debug>(b: usize, kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(b).unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        TestResult::from_bool(kv.iter().all(|&k| t.find(&k).is_some()))
    }
    #[quickcheck] fn find_unit(b: usize, kv: Vec<()>) -> TestResult { test_find(b, kv) }
    #[quickcheck] fn find_bool(b: usize, kv: Vec<bool>) -> TestResult { test_find(b, kv) }
    #[quickcheck] fn find_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_find(b, kv) }
    #[quickcheck] fn find_usize(b: usize, kv: Vec<usize>) -> TestResult { test_find(b, kv) }

    fn test_min_max<T: Copy + Ord + fmt::Debug>(b: usize, kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(b).unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        TestResult::from_bool(t.min().map(|k_x| k_x.0) == kv.iter().min() &&
                              t.max().map(|k_x| k_x.0) == kv.iter().max())
    }
    #[quickcheck] fn min_max_unit(b: usize, kv: Vec<()>) -> TestResult { test_min_max(b, kv) }
    #[quickcheck] fn min_max_bool(b: usize, kv: Vec<bool>) -> TestResult { test_min_max(b, kv) }
    #[quickcheck] fn min_max_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_min_max(b, kv) }
    #[quickcheck] fn min_max_usize(b: usize, kv: Vec<usize>) -> TestResult { test_min_max(b, kv) }

    fn test_deletion<T: Copy + Ord + fmt::Debug>(b: usize, kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        if kv.len() == 0 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(b).unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        t.delete(&kv[0]);
        TestResult::from_bool(t.find(&kv[0]).is_none())
    }
    #[quickcheck] fn deletion_unit(b: usize, kv: Vec<()>) -> TestResult { test_deletion(b, kv) }
    #[quickcheck] fn deletion_bool(b: usize, kv: Vec<bool>) -> TestResult { test_deletion(b, kv) }
    #[quickcheck] fn deletion_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_deletion(b, kv) }
    #[quickcheck] fn deletion_usize(b: usize, kv: Vec<usize>) -> TestResult { test_deletion(b, kv) }

    fn test_deletion_min<T: Copy + Ord + fmt::Debug>(b: usize, mut kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        if kv.len() == 0 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(b).unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        t.delete_min();
        kv.sort();
        TestResult::from_bool(t.find(&kv[0]).is_none())
    }
    #[quickcheck] fn deletion_min_unit(b: usize, kv: Vec<()>) -> TestResult { test_deletion_min(b, kv) }
    #[quickcheck] fn deletion_min_bool(b: usize, kv: Vec<bool>) -> TestResult { test_deletion_min(b, kv) }
    #[quickcheck] fn deletion_min_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_deletion_min(b, kv) }
    #[quickcheck] fn deletion_min_usize(b: usize, kv: Vec<usize>) -> TestResult { test_deletion_min(b, kv) }

    fn test_deletion_max<T: Copy + Ord + fmt::Debug>(b: usize, mut kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        if kv.len() == 0 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(b).unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        t.delete_max();
        kv.sort();
        kv.reverse();
        TestResult::from_bool(t.find(&kv[0]).is_none())
    }
    #[quickcheck] fn deletion_max_unit(b: usize, kv: Vec<()>) -> TestResult { test_deletion_max(b, kv) }
    #[quickcheck] fn deletion_max_bool(b: usize, kv: Vec<bool>) -> TestResult { test_deletion_max(b, kv) }
    #[quickcheck] fn deletion_max_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_deletion_max(b, kv) }
    #[quickcheck] fn deletion_max_usize(b: usize, kv: Vec<usize>) -> TestResult { test_deletion_max(b, kv) }

    fn test_total_deletion<T: Copy + Ord + fmt::Debug>(b: usize, kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(b).unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        for &k in kv.iter() { t.delete(&k); }
        TestResult::from_bool(kv.iter().all(|k| t.find(k).is_none()))
    }
    #[quickcheck] fn total_deletion_unit(b: usize, kv: Vec<()>) -> TestResult { test_total_deletion(b, kv) }
    #[quickcheck] fn total_deletion_bool(b: usize, kv: Vec<bool>) -> TestResult { test_total_deletion(b, kv) }
    #[quickcheck] fn total_deletion_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_total_deletion(b, kv) }
    #[quickcheck] fn total_deletion_usize(b: usize, kv: Vec<usize>) -> TestResult { test_total_deletion(b, kv) }
}
