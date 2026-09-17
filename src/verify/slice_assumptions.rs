// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Assumptions about `core::slice` APIs that are not yet specified by vstd.

use core::slice;
use vstd::prelude::*;
use vstd::relations::{sorted_by, total_ordering};
use vstd::std_specs::cmp::OrdSpec;
use vstd::std_specs::iter::IteratorSpec;

verus! {

pub assume_specification<'a, T>[ <slice::Iter<'a, T> as Iterator>::size_hint ](
    iter: &slice::Iter<'a, T>,
) -> (result: (usize, Option<usize>))
    ensures
        result.0 as int == IteratorSpec::remaining(iter).len(),
        result.1 == Some(result.0),
;

pub assume_specification<'a, T>[ <slice::IterMut<'a, T> as Iterator>::size_hint ](
    iter: &slice::IterMut<'a, T>,
) -> (result: (usize, Option<usize>))
    ensures
        result.0 as int == IteratorSpec::remaining(iter).len(),
        result.1 == Some(result.0),
;

pub assume_specification<T>[ <[T]>::reverse ](slice: &mut [T])
    ensures
    final(slice)@ == old(slice)@.reverse(),
;

pub open spec fn slice_le<T: Ord>(left: T, right: T) -> bool {
    left.cmp_spec(&right) != core::cmp::Ordering::Greater
}

pub assume_specification<T: Ord>[ <[T]>::sort ](slice: &mut [T])
    ensures
        final(slice)@.to_multiset() == old(slice)@.to_multiset(),
        T::obeys_cmp_spec()
            && total_ordering(|left: T, right: T| slice_le(left, right)) ==>
                sorted_by(final(slice)@, |left: T, right: T| slice_le(left, right)),
;

} // verus!
