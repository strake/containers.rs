use alloc::Alloc;
use core::{fmt, hash::{Hash, Hasher}, ptr, ops::{Index, IndexMut}};
use either::Either::{self, *};
use fallible::TryClone;
use unreachable::UncheckedResultExt;

use super::RawVec;

pub struct VecDeque<T, A: Alloc = ::DefaultA> {
    raw: RawVec<T, A>,
    head: usize,
    tail: usize,
}

impl<T, A: Alloc> VecDeque<T, A> {
    #[inline]
    pub fn new_in(a: A) -> Self { VecDeque { raw: RawVec::new_in(a), head: 0, tail: 0 } }

    #[inline]
    pub fn with_capacity_in(a: A, cap: usize) -> Option<Self> {
        RawVec::with_capacity_in(a, cap).map(|raw| VecDeque { raw, head: 0, tail: 0 })
    }

    #[inline]
    pub fn capacity(&self) -> usize { self.raw.capacity() }

    #[inline]
    pub fn reserve(&mut self, n_more: usize) -> bool {
        let n_free = self.head - self.tail;
        let old_cap = self.capacity();
        n_free >= n_more || self.raw.reserve(old_cap - n_free, n_more) && unsafe {
            let new_cap = self.capacity();
            let old_head = self.head;
            let new_head = self.head + new_cap - old_cap;
            let p = self.raw.ptr();
            ptr::copy_nonoverlapping(p.offset(old_head as _), p.offset(new_head as _),
                                     old_cap - old_head);
            self.head = new_head;
            true
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        let mut tail = self.tail;
        if tail < self.head { tail += self.capacity(); }
        tail - self.head
    }

    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        if 0 == self.len() { None } else {
            let k = self.head;
            self.head += 1;
            if self.head >= self.capacity() { self.head -= self.capacity(); }
            Some(unsafe { ptr::read(&self.raw.storage()[k]) })
        }
    }

    #[inline]
    pub fn push_front(&mut self, x: T) -> Result<(), T> {
        if !self.reserve(1) { Err(x) } else {
            if 0 == self.head { self.head = self.capacity(); }
            self.head -= 1;
            unsafe { ptr::write(&mut self.raw.storage_mut()[self.head], x) };
            Ok(())
        }
    }

    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        if 0 == self.len() { None } else {
            if 0 == self.tail { self.tail = self.capacity(); }
            self.tail -= 1;
            Some(unsafe { ptr::read(&self.raw.storage()[self.tail]) })
        }
    }

    #[inline]
    pub fn push_back(&mut self, x: T) -> Result<(), T> {
        if !self.reserve(1) { Err(x) } else {
            let k = self.tail;
            self.tail += 1;
            if self.tail >= self.capacity() { self.tail -= self.capacity(); }
            unsafe { ptr::write(&mut self.raw.storage_mut()[k], x) };
            Ok(())
        }
    }

    #[inline]
    pub fn get(&self, k: usize) -> Option<&T> { unsafe {
        if k >= self.len() { None } else { Some(self.get_unchecked(k)) }
    } }

    #[inline]
    pub fn get_mut(&mut self, k: usize) -> Option<&mut T> { unsafe {
        if k >= self.len() { None } else { Some(self.get_unchecked_mut(k)) }
    } }

    #[inline]
    pub unsafe fn get_unchecked(&self, k: usize) -> &T {
        let mut n = self.head + k;
        if n >= self.capacity() { n -= self.capacity(); }
        &self.raw.storage()[n]
    }

    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, k: usize) -> &mut T {
        let mut n = self.head + k;
        if n >= self.capacity() { n -= self.capacity(); }
        &mut self.raw.storage_mut()[n]
    }

    #[inline]
    pub fn iter(&self) -> Iter<T, A> {
        Iter { raw: &self.raw, head: self.head, tail: self.tail }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<T, A> {
        IterMut { raw: &mut self.raw, head: self.head, tail: self.tail }
    }

    #[inline]
    pub fn truncate_back(&mut self, n: usize) {
        while self.len() > n { self.pop_back(); }
    }

    #[inline]
    pub fn truncate_front(&mut self, n: usize) {
        while self.len() > n { self.pop_front(); }
    }
}

impl<T: Hash, A: Alloc> Hash for VecDeque<T, A> {
    #[inline]
    fn hash<H: Hasher>(&self, h: &mut H) { self.iter().for_each(|x| x.hash(h)); }
}

impl<T: fmt::Debug, A: Alloc> fmt::Debug for VecDeque<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: TryClone, A: Alloc + TryClone> TryClone for VecDeque<T, A> {
    type Error = Option<Either<A::Error, T::Error>>;

    #[inline]
    fn try_clone(&self) -> Result<Self, Self::Error> {
        let alloc = self.raw.alloc.try_clone().map_err(Left).map_err(Some)?;
        match Self::with_capacity_in(alloc, self.len()) {
            Some(mut new) => {
                new.try_clone_from(self)?;
                Ok(new)
            },
            None => Err(None),
        }
    }

    #[inline]
    fn try_clone_from(&mut self, other: &Self) -> Result<(), Self::Error> {
        if let Some(n_more) = usize::checked_sub(self.capacity(), other.len()) {
            if !self.reserve(n_more) { return Err(None); }
        }
        self.truncate_back(other.len());
        for i in 0..self.len() {
            self[i].try_clone_from(&other[i]).map_err(Right).map_err(Some)?;
        }
        for x in other.iter().skip(self.len()) { unsafe {
            self.push_back(x.try_clone().map_err(Right).map_err(Some)?).unchecked_unwrap_ok();
        } }
        Ok(())
    }
}

impl<T, A: Alloc> Drop for VecDeque<T, A> {
    #[inline]
    fn drop(&mut self) {
        while let Some(_) = self.pop_front() {}
    }
}

impl<T, A: Alloc> Index<usize> for VecDeque<T, A> {
    type Output = T;

    #[inline]
    fn index(&self, k: usize) -> &T { self.get(k).expect("index out of bounds") }
}

impl<T, A: Alloc> IndexMut<usize> for VecDeque<T, A> {
    #[inline]
    fn index_mut(&mut self, k: usize) -> &mut T { self.get_mut(k).expect("index out of bounds") }
}

pub struct Iter<'a, T: 'a, A: 'a + Alloc> {
    raw: &'a RawVec<T, A>,
    head: usize,
    tail: usize,
}

impl<'a, T, A: Alloc> Iterator for Iter<'a, T, A> {
    type Item = &'a T;
    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if 0 == self.len() { None } else {
            let k = self.head;
            self.head += 1;
            if self.head >= self.raw.capacity() { self.head -= self.raw.capacity(); }
            Some(unsafe { &self.raw.storage()[k] })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) { (self.len(), Some(self.len())) }
}

impl<'a, T, A: Alloc> DoubleEndedIterator for Iter<'a, T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        if 0 == self.len() { None } else {
            if 0 == self.tail { self.tail = self.raw.capacity(); }
            self.tail -= 1;
            Some(unsafe { &self.raw.storage()[self.tail] })
        }
    }
}

impl<'a, T, A: Alloc> ExactSizeIterator for Iter<'a, T, A> {
    #[inline]
    fn len(&self) -> usize {
        let mut tail = self.tail;
        if tail < self.head { tail += self.raw.capacity(); }
        tail - self.head
    }
}

pub struct IterMut<'a, T: 'a, A: 'a + Alloc> {
    raw: &'a mut RawVec<T, A>,
    head: usize,
    tail: usize,
}

impl<'a, T, A: Alloc> Iterator for IterMut<'a, T, A> {
    type Item = &'a mut T;
    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        if 0 == self.len() { None } else {
            let k = self.head;
            self.head += 1;
            if self.head >= self.raw.capacity() { self.head -= self.raw.capacity(); }
            Some(unsafe { &mut *self.raw.ptr().offset(k as _) })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) { (self.len(), Some(self.len())) }
}

impl<'a, T, A: Alloc> DoubleEndedIterator for IterMut<'a, T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        if 0 == self.len() { None } else {
            if 0 == self.tail { self.tail = self.raw.capacity(); }
            self.tail -= 1;
            Some(unsafe { &mut *self.raw.ptr().offset(self.tail as _) })
        }
    }
}

impl<'a, T, A: Alloc> ExactSizeIterator for IterMut<'a, T, A> {
    #[inline]
    fn len(&self) -> usize {
        let mut tail = self.tail;
        if tail < self.head { tail += self.raw.capacity(); }
        tail - self.head
    }
}
