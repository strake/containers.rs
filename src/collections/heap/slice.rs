//! Heap operations on slices

use core::mem;

use util::*;

/// Given a slice `xs` which is all but the last element already a heap, extend
/// the heap to include the last element.
/// `f(x,y)` is whether `x` must be nearer to the root than `y`.
/// `xs` being empty is an error.
#[inline] pub fn push<A, F: Fn(&A, &A) -> bool>(arity: usize, f: F, xs: &mut [A]) {
    assert!(xs.len() > 0);
    let mut n = xs.len() - 1;
    loop {
        if n == 0 { return };
        let m = (n-1)/arity;
        if !f(&xs[n], &xs[m]) { return };
        xs.swap(m, n);
        n = m;
    }
}

/// Given a slice `xs` which is already a heap, move the root to the end of the
/// slice and retract the heap to exclude it.
/// `f(x,y)` is whether `x` must be nearer to the root than `y`.
/// `xs` being empty is an error.
#[inline] pub fn pop<A, F: Fn(&A, &A) -> bool>(arity: usize, f: F, xs: &mut [A]) {
    assert!(xs.len() > 0);
    let l = xs.len()-1;
    xs.swap(0, l);
    sift_down(arity, f, &mut xs[0..l], 0);
}

/// Make `xs` a heap.
/// `f(x,y)` is whether `x` must be nearer to the root than `y`.
#[inline] pub fn build<A, F: Fn(&A, &A) -> bool>(arity: usize, f: F, xs: &mut [A]) {
    if xs.len() <= 1 { return };
    for k in (0..xs.len()>>1).rev() { sift_down(arity, &f, xs, k) }
}

/// Given a slice `xs` which is already a heap, sort the elements.
#[inline] pub fn sort<A, F: Fn(&A, &A) -> bool>(arity: usize, f: F, xs: &mut [A]) {
    for l in (1..xs.len()).rev() {
        // l+1 rather than l here lest we miss last element, as we have 2 half-open ranges
        pop(arity, &f, &mut xs[0..l+1]);
    }
}

/// Given a slice `xs` which is already a heap, replace the root.
/// `f(x,y)` is whether `x` must be nearer to the root than `y`.
/// `xs` being empty is an error.
#[inline] pub fn replace_root<A, F: Fn(&A, &A) -> bool>(arity: usize, f: F, xs: &mut [A], x: A) -> A {
    assert!(xs.len() > 0);
    let y = mem::replace(&mut xs[0], x);
    sift_down(arity, f, xs, 0);
    y
}

#[inline] fn sift_down<A, F: Fn(&A, &A) -> bool>(arity: usize, f: F, xs: &mut [A], mut m: usize) {
    let g: &Fn(Option<&A>, Option<&A>) -> bool = &|opt_x, opt_y| map_opt_2_or(false, &f, opt_x, opt_y);
    loop {
        if m >= xs.len() { return };
        let n = {
            let mut n = m;
            for k in (0..arity).map(|k| arity*m+k+1) { if g(xs.get(k), Some(&xs[n])) { n = k } }
            n
        };
        if m == n { return };
        xs.swap(m, n);
        m = n;
    }
}

#[inline] pub fn is_heap<A, F: Fn(&A, &A) -> bool>(arity: usize, f: F, xs: &[A]) -> bool {
    let g: &Fn(Option<&A>, Option<&A>) -> bool = &|opt_x, opt_y| map_opt_2_or(false, &f, opt_x, opt_y);
    !(0..xs.len()).any(|n| (0..arity).any(|k| g(xs.get(n*arity+k+1), Some(&xs[n]))))
}

#[cfg(test)] mod tests {
    use quickcheck::*;
    use std::vec::*;

    use super::*;

    fn greater<A: Ord>(x: &A, y: &A) -> bool { x > y }

    fn is_sorted(xs: &[usize]) -> bool {
        (1..xs.len()).all(|k| xs[k-1] <= xs[k])
    }

    #[quickcheck] fn build_test(arity: usize, mut xv: Vec<usize>) -> TestResult {
        if arity <= 1 { return TestResult::discard() };
        let xs = &mut xv[..];
        build(arity, greater, xs);
        TestResult::from_bool(is_heap(arity, greater, xs))
    }
    #[quickcheck] fn  push_test(arity: usize, mut xv: Vec<usize>) -> TestResult {
        if arity <= 1 { return TestResult::discard() };
        if xv.len() == 0 { return TestResult::discard() };
        let xs = &mut xv[..];
        let l = xs.len();
        build(arity, greater, &mut xs[0..l]);
        push(arity, greater, xs);
        TestResult::from_bool(is_heap(arity, greater, xs))
    }
    #[quickcheck] fn   pop_test(arity: usize, mut xv: Vec<usize>) -> TestResult {
        if arity <= 1 { return TestResult::discard() };
        if xv.len() == 0 { return TestResult::discard() };
        let xs = &mut xv[..];
        let l = xs.len()-1;
        build(arity, greater, xs);
        pop(arity, greater, xs);
        TestResult::from_bool(is_heap(arity, greater, &mut xs[0..l]) && xs[l] >= xs[0])
    }
    #[quickcheck] fn  sort_test(arity: usize, mut xv: Vec<usize>) -> TestResult {
        if arity <= 1 { return TestResult::discard() };
        let xs = &mut xv[..];
        build(arity, greater, xs);
        sort(arity, greater, xs);
        TestResult::from_bool(is_sorted(xs))
    }
}
