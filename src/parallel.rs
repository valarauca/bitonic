
extern crate crossbeam;

use super::{
    cmp_and_swap,
    cmp_and_swap_func
};
use std::sync::Mutex;
use std::cmp::Ordering;
use std::marker::{
    Send,
    Sync,
    PhantomData
};
use std::mem;
use std::sync::atomic::{
    AtomicUsize,
    Ordering as AtomicOrdering
};

struct TrackerAtomic {
    locker: AtomicUsize,
    count: AtomicUsize
}
impl TrackerAtomic {
    fn new(size: usize) -> TrackerAtomic {
        TrackerAtomic {
            locker: AtomicUsize::new(0),
            count: AtomicUsize::new(size)
        }
    }
    #[inline(always)]
    fn lock(&self) {
        loop {
            //lock/unlock is a 0
            if self.locker.compare_and_swap(0,1,AtomicOrdering::SeqCst) == 0 {
                break;
            }
        }
    }
    #[inline(always)]
    fn unlock(&self) {
        self.locker.store(0,AtomicOrdering::SeqCst);
    }
    // how many threads can be launched
    fn start_threads(&self) -> usize {
        self.lock();
        let ret: usize;
        let sized = self.count.load(AtomicOrdering::Relaxed);
        if sized >= 2 {
            let newsize = sized - 2;
            self.count.store(newsize,AtomicOrdering::Relaxed);
            ret = 2;
        } else if sized >= 1 {
            let newsize = sized - 1;
            self.count.store(newsize,AtomicOrdering::Relaxed);
            ret = 1;
        } else {
            ret = 0;
        }
        self.unlock();
        return ret;
    }
    // note that threads ended
    fn stop_threads(&self, val: usize) {
        self.lock();
        self.count.fetch_add(val, AtomicOrdering::Relaxed);
        self.unlock();
    }
}
unsafe impl Send for TrackerAtomic { } 
unsafe impl Sync for TrackerAtomic { }

struct Tracker(Mutex<(usize,usize)>);
impl Tracker {
    fn new(size: usize) -> Tracker {
        let tup = (0usize, size);
        Tracker(Mutex::new(tup))
    }
    fn increment(&self) -> bool {
        #[inline(always)]
        fn can_inc(tup: &mut (usize,usize) ) -> bool {
            let workers = tup.0.clone();
            let max = tup.1.clone();
            if workers < max {
                tup.0 += 1;
                return true
            }
            false
        }
        match self.0.lock() {
            Ok(ref mut val) => can_inc(val),
            Err(_) => false
        }
    }
    fn decrement(&self) {
        #[inline(always)]
        fn dec(tup: &mut (usize,usize)) {
            tup.0 -=1;
        }
        match self.0.lock() {
            Ok(ref mut val) => dec(val),
            Err(_) => { }
        };
    }
}

/// This is a safe abstraction as long as the rust borrow system
/// maintains it guarantees
struct Array<T> {
    ptr: *mut T,
    len: usize
}
impl<T> Array<T> {
    fn new(array: &mut[T]) -> Array<T> {
        let tup: (*mut T, usize) = unsafe{ mem::transmute(array)};
        Array {
            ptr: tup.0,
            len: tup.1
        }
    }
    fn as_mut_slice(&self) -> &mut [T] {
        unsafe{ ::std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}
unsafe impl<T> Send for Array<T> { } 
unsafe impl<T> Sync for Array<T> { }


fn bitonic_merge<T: Ord>(arr: &Array<T>, low: usize, count: usize, o: Ordering, a: &Tracker) {
    if count > 1 {
        let split = count >> 1;
        for i in low..(split+low) {
            cmp_and_swap(arr.as_mut_slice(), i, i+split, o);
        }
        let mut thread_count = 0usize;
        if a.increment() {
            thread_count += 1;
        }
        if a.increment() {
            thread_count += 1;
        }
        match thread_count {
            2 => {
                crossbeam::scope(|scope| {
                    scope.spawn(move ||{
                        bitonic_merge(arr, low, split, o, a);
                    });
                    scope.spawn(move ||{
                        bitonic_merge(arr, low+split, split, o, a);
                    });
                });
                a.decrement();
                a.decrement();
            },
            1 => {
                crossbeam::scope(|scope| {
                    scope.spawn(move ||{
                        bitonic_merge(arr, low, split, o, a);
                    });
                    bitonic_merge(arr, low+split, split, o, a);
                });
                a.decrement();
            },
            0 => {
                bitonic_merge(arr, low, split, o, a);
                bitonic_merge(arr, low+split, split, o, a);
            },
            _ => unreachable!()
        };
    }
}

fn bitonic_t_sort<T: Ord>(arr: &Array<T>, low: usize, count: usize, o: Ordering, a: &Tracker) {
    if count > 1 {
        let split = count >> 1;
        let mut thread_count = 0usize;
        if a.increment() {
            thread_count += 1;
        }
        if a.increment() {
            thread_count += 1;
        }
        match thread_count {
            2 => {
                crossbeam::scope(|scope| {
                    scope.spawn(move ||{
                        bitonic_t_sort(arr, low, split, Ordering::Greater, a);
                    });
                    scope.spawn(move ||{
                        bitonic_t_sort(arr, low+split, split, Ordering::Less, a);
                    });
                });
                a.decrement();
                a.decrement();
            },
            1 => {
                crossbeam::scope(|scope| {
                    scope.spawn(move ||{
                        bitonic_t_sort(arr, low, split, Ordering::Greater, a);
                    });
                    bitonic_t_sort(arr, low+split, split, Ordering::Less, a);
                });
                a.decrement();
            },
            0 => {
                bitonic_t_sort(arr, low, split, Ordering::Greater, a);
                bitonic_t_sort(arr, low+split, split, Ordering::Less, a);
            },
            _ => unreachable!()
        };
        bitonic_merge(arr,low,count,o,a);
    }
}

/// Preforms a concurrent bitonic sort.
///
/// This is an early version of the crate so there is a fair amount of 
/// lock contention, that'll be improved as time goes on.
pub fn parallel_bitonic_sort_descending<T: Ord>(arr: &mut [T], threads: usize) {
    let threads = if threads == 0 { 1 } else { threads };
    let len = arr.len();
    let arr = Array::new(arr);
    let track = Tracker::new(threads);
    bitonic_t_sort(&arr, 0, len, Ordering::Less, &track);
}

/// Preforms a concurrent bitonic sort.
///
/// This is an early version of the crate so there is a fair amount of 
/// lock contention, that'll be improved as time goes on.
pub fn parallel_bitonic_sort_ascending<T: Ord>(arr: &mut [T], threads: usize) {
    let threads = if threads == 0 { 1 } else { threads };
    let len = arr.len();
    let arr = Array::new(arr);
    let track = Tracker::new(threads);
    bitonic_t_sort(&arr, 0, len, Ordering::Greater, &track);
}


#[test]
fn test_bitonic_concurrent_sort() {
    let mut v: Vec<usize> = vec![8,6,7,4,5,3,2,1];
    parallel_bitonic_sort_ascending(&mut v, 8);
    assert_eq!(v.as_slice(), &[1,2,3,4,5,6,7,8]);
    parallel_bitonic_sort_descending(&mut v, 8);
    assert_eq!(v.as_slice(), &[8,7,6,5,4,3,2,1]);
}


struct DumbThing<'a,T: 'a, F: Fn(&T,&T)->Ordering+'a> {
    marker: PhantomData<&'a T>,
    ptr: &'a F
}
impl<'a, T:'a, F: Fn(&T,&T)->Ordering+'a> DumbThing<'a,T, F> {
    pub fn new(func: &'a F) -> DumbThing<'a,T,F> {
        DumbThing {
            marker: PhantomData,
            ptr: func
        }
    }
    #[inline(always)]
    pub fn refer(&self) -> &'a F {
        self.ptr
    }
}
unsafe impl<'a, T:'a, F: Fn(&T,&T)->Ordering+'a> Sync for DumbThing<'a,T,F> { }
unsafe impl<'a, T:'a, F: Fn(&T,&T)->Ordering+'a> Send for DumbThing<'a,T,F> { }


fn bitonic_merge_func<T, F: Fn(&T,&T)->Ordering>(
    arr: &Array<T>,
    low: usize,
    count: usize,
    o: Ordering,
    a: &TrackerAtomic,
    f: &DumbThing<T,F>,
    suggestion: usize
) {
    if count > 1 {
        let split = count >> 1;
        for i in low..(split+low) {
            cmp_and_swap_func(arr.as_mut_slice(), i, i+split, o, f.refer());
        }
        let thread_count = if split > suggestion { a.start_threads() } else { 0 };
        match thread_count {
            2 => {
                crossbeam::scope(|scope| {
                    scope.spawn(move ||{
                        bitonic_merge_func(arr, low, split, o, a, f, suggestion);
                    });
                    scope.spawn(move ||{
                        bitonic_merge_func(arr, low+split, split, o, a, f, suggestion);
                    });
                });
                a.stop_threads(2);
            },
            1 => {
                crossbeam::scope(|scope| {
                    scope.spawn(move ||{
                        bitonic_merge_func(arr, low, split, o, a, f, suggestion);
                    });
                    bitonic_merge_func(arr, low+split, split, o, a, f, suggestion);
                });
                a.stop_threads(1);
            },
            0 => {
                bitonic_merge_func(arr, low, split, o, a, f, suggestion);
                bitonic_merge_func(arr, low+split, split, o, a, f, suggestion);
            },
            _ => unreachable!()
        };
    }
}

fn bitonic_t_sort_func<T, F: Fn(&T,&T)->Ordering>(
    arr: &Array<T>, 
    low: usize, 
    count: usize,
    o: Ordering,
    a: &TrackerAtomic, 
    f: &DumbThing<T,F>,
    suggestion: usize
) {
    if count > 1 {
        let split = count >> 1;
        let thread_count = if split > suggestion { a.start_threads() } else { 0 };
        match thread_count {
            2 => {
                crossbeam::scope(|scope| {
                    scope.spawn(move ||{
                        bitonic_t_sort_func(arr, low, split, Ordering::Greater, a, f, suggestion);
                    });
                    scope.spawn(move ||{
                        bitonic_t_sort_func(arr, low+split, split, Ordering::Less, a, f, suggestion);
                    });
                });
                a.stop_threads(2);
            },
            1 => {
                crossbeam::scope(|scope| {
                    scope.spawn(move ||{
                        bitonic_t_sort_func(arr, low, split, Ordering::Greater, a, f, suggestion);
                    });
                    bitonic_t_sort_func(arr, low+split, split, Ordering::Less, a, f, suggestion);
                });
                a.stop_threads(1);
            },
            0 => {
                bitonic_t_sort_func(arr, low, split, Ordering::Greater, a, f, suggestion);
                bitonic_t_sort_func(arr, low+split, split, Ordering::Less, a, f, suggestion);
            },
            _ => unreachable!()
        };
        bitonic_merge_func(arr,low, count, o, a, f, suggestion);
    }
}

/// Preforms a concurrent bitonic sort.
///
/// This is an early version of the crate so there is a fair amount of 
/// lock contention, that'll be improved as time goes on.
pub fn parallel_bitonic_sort_descending_func<T, F: Fn(&T,&T)->Ordering>(
    arr: &mut [T], 
    threads: usize, 
    cmp: &F
) {
    let threads = if threads == 0 { 1 } else { threads };
    let len = arr.len();
    let arr = Array::new(arr);
    let track = TrackerAtomic::new(threads);
    let f = DumbThing::new(cmp);
    bitonic_t_sort_func(&arr, 0, len, Ordering::Less, &track, &f);
}

/// Preforms a concurrent bitonic sort.
///
/// This is an early version of the crate so there is a fair amount of 
/// lock contention, that'll be improved as time goes on.
///
/// suggestion is the cut off for threading. If there are less then
/// `suggestion` rows the method won't attempt to fork
pub fn parallel_bitonic_sort_ascending_func<T, F: Fn(&T,&T)->Ordering>(
    arr: &mut [T], 
    threads: usize,
    suggestion: usize,
    cmp: &F
) {
    let threads = if threads == 0 { 1 } else { threads };
    let len = arr.len();
    let arr = Array::new(arr);
    let track = TrackerAtomic::new(threads);
    let f = DumbThing::new(cmp);
    bitonic_t_sort_func(&arr, 0, len, Ordering::Greater, &track, &f);
}
#[test]
fn test_parallel_bitonic_sort_func() {

    fn get_len(x: &&str, y: &&str) -> Ordering {
        x.len().cmp( &y.len())
    }

    let mut v: Vec<&str> = vec!["helloworld","hi","sup","words"];
    parallel_bitonic_sort_ascending_func(v.as_mut_slice(), 8, &get_len);
    assert_eq!("hi", v[0]);
    assert_eq!("sup", v[1]);
    assert_eq!("words", v[2]);
    assert_eq!("helloworld", v[3]);

    parallel_bitonic_sort_descending_func(v.as_mut_slice(), 8, &get_len);
    assert_eq!("helloworld",v[0]);
}

