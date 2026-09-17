// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Assumptions about `alloc::vec` APIs that are not yet specified by vstd.

use alloc::vec;
use vstd::prelude::*;
use vstd::std_specs::iter::{into_iter_remaining, IteratorSpec};

verus! {

pub assume_specification<T, A: core::alloc::Allocator>[ <vec::IntoIter<T, A> as Iterator>::size_hint ](
    iter: &vec::IntoIter<T, A>,
) -> (result: (usize, Option<usize>))
    ensures
        result.0 as int == IteratorSpec::remaining(iter).len(),
        result.1 == Some(result.0),
;

pub assume_specification<T, A: core::alloc::Allocator, I: IntoIterator<Item = T>>[
    <vec::Vec<T, A> as Extend<T>>::extend
](
    vec: &mut vec::Vec<T, A>,
    iter: I,
)
    ensures
        final(vec)@ == old(vec)@ + into_iter_remaining::<T, I>(iter),
;

pub open spec fn seq_retain_ensures<T, F>(
    old_values: Seq<T>,
    predicate: F,
    new_values: Seq<T>,
    keep: Seq<bool>,
) -> bool
where
    F: FnMut(&T) -> bool,
{
    &&& keep.len() == old_values.len()
    &&& forall|index: int| #![auto]
        0 <= index < keep.len() ==>
            call_ensures(predicate, (&old_values[index],), keep[index])
    &&& new_values == old_values.filter_index(|index: int| keep[index])
}

pub assume_specification<T, A: core::alloc::Allocator, F>[ vec::Vec::<T, A>::retain ](
    vec: &mut vec::Vec<T, A>,
    predicate: F,
)
where
    F: FnMut(&T) -> bool,
    requires
        forall|index: int| #![auto]
            0 <= index < vec@.len() ==> call_requires(predicate, (&vec@[index],)),
    ensures
        exists|keep: Seq<bool>|
            seq_retain_ensures(old(vec)@, predicate, final(vec)@, keep),
;

} // verus!
