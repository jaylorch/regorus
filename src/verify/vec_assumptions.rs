// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Assumptions about `alloc::vec` APIs that are not yet specified by vstd.

use alloc::vec;
use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpec;

verus! {

pub assume_specification<T, A: core::alloc::Allocator>[ <vec::IntoIter<T, A> as Iterator>::size_hint ](
	iter: &vec::IntoIter<T, A>,
) -> (result: (usize, Option<usize>))
	ensures
		result.0 as int == IteratorSpec::remaining(iter).len(),
		result.1 == Some(result.0),
;

} // verus!
