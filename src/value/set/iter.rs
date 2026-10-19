// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Opaque iterator types for [`Set`].
//!
//! These newtypes wrap the storage backend's iterators so the backend can be
//! swapped without changing any iterator type signatures observed by callers.

use alloc::collections::btree_set;
use core::iter::FusedIterator;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::*;

use super::Set;
use crate::value::Value;

/// Owned iterator over `Value` elements.
#[derive(Debug)]
pub struct IntoIter {
    pub(super) inner: btree_set::IntoIter<Value>,
}

impl Iterator for IntoIter {
    type Item = Value;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl DoubleEndedIterator for IntoIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl ExactSizeIterator for IntoIter {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl FusedIterator for IntoIter {}

/// Borrowed iterator over `&Value` elements.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Clone)]
pub struct Iter<'a> {
    pub(super) inner: btree_set::Iter<'a, Value>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Value;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

#[verus_verify]
impl<'a> ExactSizeIterator for Iter<'a> {
    #[inline]
    #[verus_spec(result =>
        ensures
            result == self.inner_exact_len(),
    )]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a> FusedIterator for Iter<'a> {}

impl IntoIterator for Set {
    type Item = Value;
    type IntoIter = IntoIter;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

impl<'a> IntoIterator for &'a Set {
    type Item = &'a Value;
    type IntoIter = Iter<'a>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            inner: self.inner.iter(),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {

impl<'a> Iter<'a> {
    pub closed spec fn elts(&self) -> Seq<Value> {
        vstd::std_specs::btree::into_iter_btree_keys(self.inner)
    }

    pub closed spec fn iter_wf(&self) -> bool {
        IteratorSpec::obeys_prophetic_iter_laws(&self.inner)
    }

    pub closed spec fn inner_exact_len(&self) -> usize {
        self.inner.exact_len()
    }

    pub(super) broadcast proof fn reveal_model(&self)
        ensures
            #[trigger] self.elts()
                == vstd::std_specs::btree::into_iter_btree_keys(self.inner),
            self.iter_wf() == IteratorSpec::obeys_prophetic_iter_laws(&self.inner),
            #[trigger] IteratorSpec::remaining(self)
                == IteratorSpec::remaining(&self.inner),
            IteratorSpec::will_return_none(self)
                == IteratorSpec::will_return_none(&self.inner),
            IteratorSpec::decrease(self) == IteratorSpec::decrease(&self.inner),
    {
    }
}

impl<'a> IteratorSpecImpl for Iter<'a> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        self.iter_wf()
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        IteratorSpec::remaining(&self.inner)
    }

    #[verifier::prophetic]
    closed spec fn will_return_none(&self) -> bool {
        IteratorSpec::will_return_none(&self.inner)
    }

    closed spec fn decrease(&self) -> Option<nat> {
        IteratorSpec::decrease(&self.inner)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < self.elts().len() {
            Some(&self.elts()[index])
        } else {
            None
        }
    }
}

impl<'a> ExactSizeIteratorSpecImpl for Iter<'a> {
    open spec fn exact_len(&self) -> usize {
        self.inner_exact_len()
    }
}

}
