//! Balanced search trees

use alloc::*;
use core::borrow::Borrow;
use core::cmp::{ max, min };
use core::cmp::Ordering::*;
use core::fmt;
use core::marker::PhantomData;
use core::mem;
use core::ptr::{self, NonNull};
use core::slice;

use rel::ord::*;
use util::*;

struct BNode<K, T> {
    φ: PhantomData<(K, T)>,
    m: usize,
    p: NonNull<u8>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Which<K> { Min, Max, Key(K), }
use self::Which::*;

impl<K, T> BNode<K, T> {
    fn new<A: Alloc>(a: &mut A, b: usize, depth: usize) -> Option<Self> {
        if depth == 0 { Self::new_leaf(a, b) } else { Self::new_stem(a, b) }
    }

    fn new_stem<A: Alloc>(a: &mut A, b: usize) -> Option<Self> {
        match unsafe { a.alloc(Self::stem_layout(b)?) } {
            Err(_) => None,
            Ok(p) => Some(BNode { φ: PhantomData, m: 0, p }),
        }
    }

    fn new_leaf<A: Alloc>(a: &mut A, b: usize) -> Option<Self> {
        let layout = Self::leaf_layout(b)?;
        match unsafe { if layout.size() == 0 { Ok(mem::transmute(layout.align())) }
                       else { a.alloc(layout) } } {
            Err(_) => None,
            Ok(p) => Some(BNode { φ: PhantomData, m: 0, p })
        }
    }

    unsafe fn dealloc<A: Alloc>(ptr: NonNull<u8>, a: &mut A, b: usize, depth: usize) {
        if depth == 0 && Self::leaf_layout(b).unwrap().size() == 0 { return };
        a.dealloc(ptr, if depth == 0 { Self::leaf_layout(b) } else { Self::stem_layout(b) }.unwrap());
    }

    fn stem_layout(b: usize) -> Option<Layout> {
        let n_max = b<<1;
        Some(Self::leaf_layout(b)?.extend(Layout::array::<Self>(n_max)?)?.0)
    }

    fn leaf_layout(b: usize) -> Option<Layout> {
        let n_max = b<<1;
        Some(Layout::new::<()>().extend(Layout::array::<T>(n_max-1)?)?.0
                                .extend(Layout::array::<K>(n_max-1)?)?.0)
    }

    unsafe fn component_arrays_mut(&mut self, b: usize) -> (&mut [K], &mut [T], &mut [Self]) {
        let n_max = b<<1;
        let vals_ptr: *mut T = self.p.cast().as_ptr();
        let keys_ptr: *mut K = align_mut_ptr(vals_ptr.offset(n_max as isize-1));
        let children_ptr: *mut Self = align_mut_ptr(keys_ptr.offset(n_max as isize-1));
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

    unsafe fn component_arrays(&self, b: usize) -> (&[K], &[T], &[Self]) {
        let (keys, vals, children) =
            (self as *const Self as *mut Self).as_mut().unwrap().component_arrays_mut(b);
        (keys, vals, children)
    }

    unsafe fn val_array(&self, b: usize) -> &[T] { self.component_arrays(b).1 }

    fn vals(&self, b: usize) -> &[T] { &(unsafe { self.val_array(b) })[0..self.m] }

    unsafe fn val_ptr(&self, b: usize, i: usize) -> *const T { self.vals(b).as_ptr().offset(i as _) }

    unsafe fn val_array_mut(&mut self, b: usize) -> &mut [T] { self.component_arrays_mut(b).1 }

    fn vals_mut(&mut self, b: usize) -> &mut [T] { self.components_mut(b, 0).1 }

    unsafe fn val_mut_ptr(&mut self, b: usize, i: usize) -> *mut T { self.vals_mut(b).as_mut_ptr().offset(i as _) }

    unsafe fn key_array(&self, b: usize) -> &[K] { self.component_arrays(b).0 }

    fn keys(&self, b: usize) -> &[K] { &(unsafe { self.key_array(b) })[0..self.m] }

    unsafe fn key_ptr(&self, b: usize, i: usize) -> *const K { self.keys(b).as_ptr().offset(i as _) }

    unsafe fn key_array_mut(&mut self, b: usize) -> &mut [K] { self.component_arrays_mut(b).0 }

    fn keys_mut(&mut self, b: usize) -> &mut [K] { self.components_mut(b, 0).0 }

    unsafe fn key_mut_ptr(&mut self, b: usize, i: usize) -> *mut K { self.keys_mut(b).as_mut_ptr().offset(i as _) }

    unsafe fn child_array(&self, b: usize) -> &[Self] { self.component_arrays(b).2 }

    fn children(&self, b: usize, depth: usize) -> &[Self] { &(unsafe { self.child_array(b) })[0..if depth == 0 { 0 } else { self.m+1 }] }

    unsafe fn child_ptr(&self, b: usize, i: usize) -> *const Self { self.child_array(b).as_ptr().offset(i as _) }

    unsafe fn child_array_mut(&mut self, b: usize) -> &mut [Self] { self.component_arrays_mut(b).2 }

    fn children_mut(&mut self, b: usize, depth: usize) -> &mut [Self] { self.components_mut(b, depth).2 }

    unsafe fn child_mut_ptr(&mut self, b: usize, i: usize) -> *mut Self { self.child_array_mut(b).as_mut_ptr().offset(i as _) }

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

    fn find<Q: ?Sized, Rel>(&self, rel: &Rel, b: usize, depth: usize, k: &Q) -> Option<&T>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        match self.keys(b).binary_search_by(|i| rel.cmp(i.borrow(), k)) {
            Ok(i) => Some(&self.vals(b)[i]),
            Err(i) => if depth == 0 { None } else { self.children(b, depth)[i].find(rel, b, depth-1, k) },
        }
    }

    fn find_mut<Q: ?Sized, Rel>(&mut self, rel: &Rel, b: usize, depth: usize, k: &Q) -> Option<&mut T>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        match self.keys(b).binary_search_by(|i| rel.cmp(i.borrow(), k)) {
            Ok(i) => Some(&mut self.vals_mut(b)[i]),
            Err(i) => if depth == 0 { None } else { self.children_mut(b, depth)[i].find_mut(rel, b, depth-1, k) },
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

    fn insert_with<Rel, F, A: Alloc>(&mut self, rel: &Rel, a: &mut A, b: usize, depth: usize, k: K, f: F) -> Result<Option<(K, T, Self)>, (K, F)>
      where Rel: TotalOrderRelation<K>, F: FnOnce(Option<T>) -> T {
        let n_max = b<<1;
        match self.keys(b).binary_search_by(|i| rel.cmp(&i, &k)) {
            Ok(i) => {
                mutate(&mut self.vals_mut(b)[i], |x| f(Some(x)));
                Ok(None)
            },
            Err(i) => if self.m == n_max-1 { // full
                match self.split(a, b, depth) {
                    Err(()) => Err((k, f)),
                    Ok((i, y, mut other)) => {
                        match if rel.less(&k, &i) { self.insert_with(rel, a, b, depth, k, f) }
                              else { other.insert_with(rel, a, b, depth, k, f) } {
                            Err(e) => {
                                self.merge(other, a, b, depth, i, y);
                                Err(e)
                            },
                            Ok(Some(_)) => panic!("impossible"),
                            Ok(None) => Ok(Some((i, y, other))),
                        }
                    },
                }
            } else if depth == 0 { // we are a leaf
                self.insert_here_leaf_at(b, i, k, f(None));
                Ok(None)
            } else {
                match self.children_mut(b, depth)[i].insert_with(rel, a, b, depth-1, k, f) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some((k, x, child))) => {
                        self.insert_here_at(b, i, k, x, child);
                        Ok(None)
                    },
                }
            },
        }
    }

    fn delete_which_from_child<Q: ?Sized, Rel, A: Alloc>(&mut self, rel: &Rel, a: &mut A, b: usize,
                                                         depth: usize, i: usize, which: Which<&Q>) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        let opt_k_x = self.children_mut(b, depth)[i].delete_which(rel, a, b, depth-1, which);
        if opt_k_x.is_some() && self.children(b, depth)[i].m < b {
            let j = if i == 0 { 1 } else { i-1 };
            if self.children(b, depth)[j].m < b {
                // TODO: balance on other side rather than merge if possible
                let (l, y, node) = self.delete_here_at(b, min(i, j));
                self.children_mut(b, depth)[min(i, j)].merge(node, a, b, depth-1, l, y);
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

    fn delete<Q: ?Sized, Rel, A: Alloc>(&mut self, rel: &Rel, a: &mut A, b: usize, depth: usize, k: &Q) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        match (depth, self.keys(b).binary_search_by(|i| rel.cmp(i.borrow(), k))) {
            (0, Ok(i))  => Some(self.delete_here_leaf_at(b, i)),
            (0, Err(_)) => None,
            (_, Ok(i))  => {
                {
                    let (keys, vals, children) = self.components_mut(b, depth);
                    let (j, y) = children[i].max_mut(b, depth-1);
                    mem::swap(j, &mut keys[i]);
                    mem::swap(y, &mut vals[i]);
                }
                self.delete_which_from_child(rel, a, b, depth, i, Key(k))
            },
            (_, Err(i)) => self.delete_which_from_child(rel, a, b, depth, i, Key(k)),
        }
    }

    fn delete_min<Q: ?Sized, Rel, A: Alloc>(&mut self, rel: &Rel, a: &mut A, b: usize, depth: usize) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        if 0 == self.m { None } else if 0 == depth { Some(self.delete_here_leaf_at(b, 0)) }
                                     else { self.delete_which_from_child(rel, a, b, depth, 0, Min) }
    }

    fn delete_max<Q: ?Sized, Rel, A: Alloc>(&mut self, rel: &Rel, a: &mut A, b: usize, depth: usize) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        let m = self.m;
        if 0 == self.m { None } else if 0 == depth { Some(self.delete_here_leaf_at(b, m-1)) }
                                     else { self.delete_which_from_child(rel, a, b, depth, m, Max) }
    }

    fn delete_which<Q: ?Sized, Rel, A: Alloc>(&mut self, rel: &Rel, a: &mut A, b: usize, depth: usize, which: Which<&Q>) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        match which {
            Min => self.delete_min(rel, a, b, depth),
            Max => self.delete_max(rel, a, b, depth),
            Key(k) => self.delete(rel, a, b, depth, k),
        }
    }

    fn split<A: Alloc>(&mut self, a: &mut A, b: usize, depth: usize) -> Result<(K, T, Self), ()> {
        debug_assert_ne!(0, self.m & 1);
        match Self::new(a, b, depth) {
            None => Err(()),
            Some(mut other) => Ok(unsafe {
                self.m >>= 1;
                other.m = self.m;
                ptr::copy(self.key_ptr(b, self.m+1), other.key_mut_ptr(b, 0), self.m);
                ptr::copy(self.val_ptr(b, self.m+1), other.val_mut_ptr(b, 0), self.m);
                if depth != 0 { ptr::copy(self.child_ptr(b, self.m+1), other.child_mut_ptr(b, 0), self.m+1); }
                (ptr::read(&self.key_array(b)[self.m]),
                 ptr::read(&self.val_array(b)[self.m]),
                 other)
            }),
        }
    }

    fn merge<A: Alloc>(&mut self, other: Self, a: &mut A, b: usize, depth: usize, k: K, x: T) {
        debug_assert!(self.m + other.m + 1 < b<<1);
        let m = self.m;
        unsafe {
            ptr::write(&mut self.key_array_mut(b)[m], k);
            ptr::write(&mut self.val_array_mut(b)[m], x);
            ptr::copy(other.key_ptr(b, 0), self.key_mut_ptr(b, m+1), other.m);
            ptr::copy(other.val_ptr(b, 0), self.val_mut_ptr(b, m+1), other.m);
            if depth != 0 { ptr::copy(other.child_ptr(b, 0), self.child_mut_ptr(b, m+1), other.m+1); }
            self.m += other.m + 1;
            Self::dealloc(other.p, a, b, depth);
        }
        mem::forget(other); // lint
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
        match ::core::cmp::Ord::cmp(&s_n, &0) {
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

    fn drop<A: Alloc>(mut self, a: &mut A, b: usize, depth: usize) {
        unsafe {
            for p in self.keys_mut(b) { ptr::drop_in_place(p); }
            for p in self.vals_mut(b) { ptr::drop_in_place(p); }
            for p in self.children_mut(b, depth) { ptr::read(p).drop(a, b, depth-1); }
        }
        unsafe { Self::dealloc(self.p, a, b, depth); }
    }
}

impl<K: fmt::Debug, T: fmt::Debug> BNode<K, T> {
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
pub struct BTree<K, T, Rel: TotalOrderRelation<K> = ::rel::Core, A: Alloc = ::DefaultA> {
    rel: Rel,
    root: BNode<K, T>,
    depth: usize,
    b: usize,
    alloc: A,
}

impl<K, T, Rel: TotalOrderRelation<K>, A: Alloc + Default> BTree<K, T, Rel, A> {
    /// Make a new tree.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline] pub fn new(rel: Rel, b: usize) -> Option<Self> { Self::new_in(rel, A::default(), b) }
}

impl<K, T, Rel: TotalOrderRelation<K>, A: Alloc> BTree<K, T, Rel, A> {
    /// Make a new tree.
    ///
    /// # Failures
    ///
    /// Returns `None` if allocation fails.
    #[inline] pub fn new_in(rel: Rel, mut a: A, b: usize) -> Option<Self> {
        if b < 2 { return None; }
        BNode::new_leaf(&mut a, b).map(|root| BTree { rel: rel, root: root, depth: 0, b: b, alloc: a })
    }

    /// Return number of elements.
    #[inline] pub fn size(&self) -> usize { self.root.size(self.b, self.depth) }

    /// Find value with given key `k`.
    #[inline] pub fn find<Q: ?Sized>(&self, k: &Q) -> Option<&T>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> { self.root.find(&self.rel, self.b, self.depth, k) }

    /// Find value with given key `k`.
    #[inline] pub fn find_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut T>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> { self.root.find_mut(&self.rel, self.b, self.depth, k) }

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
    #[inline] pub fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, k: K, f: F) -> Result<(), (K, F)> {
        let b = self.b;
        match BNode::<K, T>::stem_layout(b).and_then(|layout| unsafe { self.alloc.alloc(layout).ok() }) {
            Some(p) => {
                let d = |a: &mut A| unsafe { a.dealloc(p, BNode::<K, T>::stem_layout(b).unwrap()) };
                match self.root.insert_with(&self.rel, &mut self.alloc, b, self.depth, k, f) {
                    Err(e) => { d(&mut self.alloc); Err(e) },
                    Ok(None) => { d(&mut self.alloc); Ok(()) },
                    Ok(Some((k, x, new))) => {
                        let mut new_root = BNode { φ: PhantomData, m: 0, p };
                        unsafe { ptr::write(&mut new_root.child_array_mut(b)[0],
                                            mem::replace(&mut self.root, new_root)); }
                        self.depth += 1;
                        self.root.insert_here_at(b, 0, k, x, new);
                        Ok(())
                    },
                }
            },
            None => Err((k, f)),
        }
    }

    /// Insert `x` at `k` and return `Some(x)` if there was already a value `x` there.
    ///
    /// # Failures
    ///
    /// Returns `Err` if allocation fails.
    #[inline] pub fn insert(&mut self, k: K, x: T) -> Result<Option<T>, (K, T)> {
        let mut opt_y = None;
        self.insert_with(k, |opt_x| { opt_y = opt_x; x })
            .map_err(|(k, f)| (k, f(None))).map(|()| opt_y)
    }

    /// Seek `which`; if found, delete it and value `x` there and return `Some((k, x))`.
    #[inline] pub fn delete_which<Q: ?Sized>(&mut self, which: Which<&Q>) -> Option<(K, T)>
      where K: Borrow<Q>, Rel: TotalOrderRelation<Q> {
        let opt_k_x = self.root.delete_which(&self.rel, &mut self.alloc, self.b, self.depth, which);
        if self.root.m == 0 && self.depth != 0 {
            let node = mem::replace(&mut self.root.children_mut(self.b, self.depth)[0],
                                    BNode { φ: PhantomData, m: 0, p: NonNull::dangling() });
            unsafe { BNode::<K, T>::dealloc(mem::replace(&mut self.root, node).p, &mut self.alloc, self.b, self.depth) };
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
    #[inline] pub fn foldl_with_key<Z, F: FnMut(Z, &K, &T) -> Z>(&self, z0: Z, mut f: F) -> Z { self.root.foldl_with_key(self.b, self.depth, z0, &mut f) }

    /// Fold elements in backward order.
    #[inline] pub fn foldr_with_key<Z, F: FnMut(Z, &K, &T) -> Z>(&self, z0: Z, mut f: F) -> Z { self.root.foldr_with_key(self.b, self.depth, z0, &mut f) }
}

unsafe impl<K: Send, T: Send, Rel: TotalOrderRelation<K>, A: Alloc + Send> Send for BTree<K, T, Rel, A> {}
unsafe impl<K: Sync, T: Sync, Rel: TotalOrderRelation<K>, A: Alloc + Sync> Sync for BTree<K, T, Rel, A> {}

impl<K, T, Rel: TotalOrderRelation<K>, A: Alloc> Drop for BTree<K, T, Rel, A> {
    #[inline] fn drop(&mut self) { mem::replace(&mut self.root, BNode { φ: PhantomData, m: 0, p: NonNull::dangling() }).drop(&mut self.alloc, self.b, self.depth) }
}

impl<K: fmt::Debug, T: fmt::Debug, Rel: TotalOrderRelation<K>, A: Alloc> fmt::Debug for BTree<K, T, Rel, A> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if cfg!(test) { self.root.debug_fmt(self.b, self.depth, fmt) }
        else { self.foldl_with_key(fmt.debug_map(), |mut d, k, x| { d.entry(k, x); d }).finish() }
    }
}

#[cfg(test)] mod tests {
    use core::fmt;
    use quickcheck::TestResult;
    use std::cmp::Ord;
    use std::vec::*;

    use super::*;

    fn test_size<T: Copy + Ord + fmt::Debug>(b: usize, mut kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(::rel::Core, b).unwrap();
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
        let mut t = BTree::<_, _>::new(::rel::Core, b).unwrap();
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
        let mut t = BTree::<_, _>::new(::rel::Core, b).unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        TestResult::from_bool(kv.iter().all(|&k| t.find(&k).is_some()))
    }
    #[quickcheck] fn find_unit(b: usize, kv: Vec<()>) -> TestResult { test_find(b, kv) }
    #[quickcheck] fn find_bool(b: usize, kv: Vec<bool>) -> TestResult { test_find(b, kv) }
    #[quickcheck] fn find_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_find(b, kv) }
    #[quickcheck] fn find_usize(b: usize, kv: Vec<usize>) -> TestResult { test_find(b, kv) }

    fn test_min_max<T: Copy + Ord + fmt::Debug>(b: usize, kv: Vec<T>) -> TestResult {
        if b < 2 { return TestResult::discard() }
        let mut t = BTree::<_, _>::new(::rel::Core, b).unwrap();
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
        let mut t = BTree::<_, _>::new(::rel::Core, b).unwrap();
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
        let mut t = BTree::<_, _>::new(::rel::Core, b).unwrap();
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
        let mut t = BTree::<_, _>::new(::rel::Core, b).unwrap();
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
        let mut t = BTree::<_, _>::new(::rel::Core, b).unwrap();
        for &k in kv.iter() { t.insert(k, ()).unwrap(); }
        for &k in kv.iter() { t.delete(&k); }
        TestResult::from_bool(kv.iter().all(|k| t.find(k).is_none()))
    }
    #[quickcheck] fn total_deletion_unit(b: usize, kv: Vec<()>) -> TestResult { test_total_deletion(b, kv) }
    #[quickcheck] fn total_deletion_bool(b: usize, kv: Vec<bool>) -> TestResult { test_total_deletion(b, kv) }
    #[quickcheck] fn total_deletion_abc(b: usize, kv: Vec<ABC>) -> TestResult { test_total_deletion(b, kv) }
    #[quickcheck] fn total_deletion_usize(b: usize, kv: Vec<usize>) -> TestResult { test_total_deletion(b, kv) }
}
