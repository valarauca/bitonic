

use std::cmp::Ordering;


mod parallel;
pub use self::parallel::{
    parallel_bitonic_sort_descending,
    parallel_bitonic_sort_ascending,
    parallel_bitonic_sort_ascending_func,
    parallel_bitonic_sort_descending_func
};

/// If A's relation to B is O they are swapped
#[inline(always)]
fn cmp_and_swap<T: Ord>(arr: &mut [T], a: usize, b: usize, o: Ordering) {
    if unsafe {arr.get_unchecked(a).cmp(arr.get_unchecked(b))} == o {
        arr.swap(a, b);
    }
}
#[test]
fn test_cmp_and_swap() {
    let mut base: Vec<usize> = vec![0,1];
    cmp_and_swap(&mut base, 0,1, Ordering::Greater);
    assert_eq!(0, base[0]);
    assert_eq!(1, base[1]);

    cmp_and_swap(&mut base, 0, 1, Ordering::Less);
    assert_eq!(1, base[0]);
    assert_eq!(0, base[1]);
}


fn bitonic_merge<T: Ord>(arr: &mut [T], low: usize, count: usize, o: Ordering) {
    if count > 1 {
        let split = count >> 1;
        for i in low..(split+low) {
            cmp_and_swap(arr, i, i+split, o);
        }
        bitonic_merge(arr, low, split, o);
        bitonic_merge(arr, low+split, split, o);
    }
}

fn bitonic_r_sort<T: Ord>(arr: &mut [T], low: usize, count: usize, o: Ordering) {
    if count > 1 {
        let split = count >> 1;
        bitonic_r_sort(arr, low, split, Ordering::Greater);
        bitonic_r_sort(arr, low+split, split, Ordering::Less);
        bitonic_merge(arr, low, count, o);
    }
}

/// Orders a mutable array in descending `3,2,1`
///
/// Uses bitonic sort to sort the array in place
/// this is an unstable sort.
pub fn bitonic_sort_descending<T: Ord>(arr: &mut [T]) {
    let len = arr.len();
    bitonic_r_sort(arr, 0, len, Ordering::Less);
}

/// Orders a mutable array in ascending order `1,2,3`
///
/// Uses bitonic sort to sort the array in place
/// this is an unstable sort.
pub fn bitonic_sort_ascending<T: Ord>(arr: &mut [T]) {
    let len = arr.len();
    bitonic_r_sort(arr, 0, len, Ordering::Greater);
}
#[test]
fn test_bitonic_sort() {
    let mut v: Vec<usize> = vec![8,6,7,4,5,3,2,1];
    bitonic_sort_ascending(&mut v);
    assert_eq!(v.as_slice(), &[1,2,3,4,5,6,7,8]);
    bitonic_sort_descending(&mut v);
    assert_eq!(v.as_slice(), &[8,7,6,5,4,3,2,1]);
}


/// Sort things that aren't normally sortable
#[inline(always)]
fn cmp_and_swap_func<T, F: Fn(&T,&T)->Ordering>(arr: &mut [T], a: usize, b: usize, o: Ordering, func: &F) {
    let det = unsafe {
        let a_ptr = arr.get_unchecked(a);
        let b_ptr = arr.get_unchecked(b);
        func(a_ptr, b_ptr)
    };
    if det == o {
        arr.swap(a, b);
    }
}
fn bitonic_merge_func<T, F: Fn(&T,&T)->Ordering>(arr: &mut [T], low: usize, count: usize, o: Ordering, func: &F) {
    if count > 1 {
        let split = count >> 1;
        for i in low..(split+low) {
            cmp_and_swap_func(arr, i, i+split, o, func);
        }
        bitonic_merge_func(arr, low, split, o, func);
        bitonic_merge_func(arr, low+split, split, o, func);
    }
}

fn bitonic_r_sort_func<T, F: Fn(&T,&T)-> Ordering>(arr: &mut [T], low: usize, count: usize, o: Ordering, func: &F) {
    if count > 1 {
        let split = count >> 1;
        bitonic_r_sort_func(arr, low, split, Ordering::Greater, func);
        bitonic_r_sort_func(arr, low+split, split, Ordering::Less, func);
        bitonic_merge_func(arr, low, count, o, func);
    }
}

/// Sort items in ascending order which don't implement ord
pub fn bitonic_sort_ascending_func<T, F: Fn(&T,&T)-> Ordering>(arr: &mut [T], func: &F) {
    let len = arr.len();
    bitonic_r_sort_func(arr, 0, len, Ordering::Greater, func);
}
/// Sort items in descending order which don't implement ord
pub fn bitonic_sort_descending_func<T, F: Fn(&T,&T)-> Ordering>(arr: &mut [T], func: &F) {
    let len = arr.len();
    bitonic_r_sort_func(arr, 0, len, Ordering::Less, func);
}
#[test]
fn test_bitonic_sort_ascending_func() {

    fn get_len(x: &&str, y: &&str) -> Ordering {
        x.len().cmp( &y.len())
    }

    let mut v: Vec<&str> = vec!["helloworld","hi","sup","words"];
    bitonic_sort_ascending_func(v.as_mut_slice(), &get_len);
    assert_eq!("hi", v[0]);
    assert_eq!("sup", v[1]);
    assert_eq!("words", v[2]);
    assert_eq!("helloworld", v[3]);

    bitonic_sort_descending_func(v.as_mut_slice(), &get_len);
    assert_eq!("helloworld",v[0]);
}
