// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Assumptions about `core::slice` APIs that are not yet specified by vstd.

use core::slice;
use vstd::prelude::*;
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

} // verus!
