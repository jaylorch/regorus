// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Opaque iterator types for [`Array`].

use alloc::vec;
use core::iter::FusedIterator;
use core::slice;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::*;

use super::Array;
use crate::value::Value;

/// Owned iterator over `Value` elements.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub struct ArrayIntoIter {
    pub(super) inner: vec::IntoIter<Value>,
}

#[verus_verify]
impl Iterator for ArrayIntoIter {
    type Item = Value;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    #[inline]
    #[verus_spec(result =>
        ensures
            result.0 as int == IteratorSpec::remaining(self).len(),
            result.1 == Some(result.0),
    )]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[verus_verify]
impl DoubleEndedIterator for ArrayIntoIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

#[verus_verify]
impl ExactSizeIterator for ArrayIntoIter {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl FusedIterator for ArrayIntoIter {}

/// Borrowed iterator over `&Value` elements.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Clone)]
pub struct ArrayIter<'a> {
    pub(super) inner: slice::Iter<'a, Value>,
}

#[verus_verify]
impl<'a> Iterator for ArrayIter<'a> {
    type Item = &'a Value;
    #[verus_verify(external_body)]
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a> DoubleEndedIterator for ArrayIter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a> ExactSizeIterator for ArrayIter<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a> FusedIterator for ArrayIter<'a> {}

/// Borrowed iterator over `&mut Value` elements.
#[derive(Debug)]
pub struct ArrayIterMut<'a> {
    pub(super) inner: slice::IterMut<'a, Value>,
}

impl<'a> Iterator for ArrayIterMut<'a> {
    type Item = &'a mut Value;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a> DoubleEndedIterator for ArrayIterMut<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a> ExactSizeIterator for ArrayIterMut<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a> FusedIterator for ArrayIterMut<'a> {}

impl IntoIterator for Array {
    type Item = Value;
    type IntoIter = ArrayIntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        ArrayIntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

impl<'a> IntoIterator for &'a Array {
    type Item = &'a Value;
    type IntoIter = ArrayIter<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a mut Array {
    type Item = &'a mut Value;
    type IntoIter = ArrayIterMut<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[cfg(verus_keep_ghost)]
verus! {

use vstd::std_specs::iter::{
    DoubleEndedIteratorSpec, DoubleEndedIteratorSpecImpl, IteratorSpecImpl,
};

impl ArrayIntoIter {
    pub closed spec fn elts(&self) -> Seq<Value> {
        vstd::std_specs::vec::into_iter_elts(self.inner)
    }

    pub closed spec fn inner_exact_len(&self) -> usize {
        self.inner.exact_len()
    }

    pub closed spec fn iter_wf(&self) -> bool {
        IteratorSpec::obeys_prophetic_iter_laws(&self.inner)
    }
}

impl IteratorSpecImpl for ArrayIntoIter {
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
            Some(self.elts()[index])
        } else {
            None
        }
    }
}

impl ExactSizeIteratorSpecImpl for ArrayIntoIter {
    open spec fn exact_len(&self) -> usize {
        self.inner_exact_len()
    }
}

impl DoubleEndedIteratorSpecImpl for ArrayIntoIter {
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        let len = self.elts().len();
        if 0 <= index < len {
            Some(self.elts()[len - index - 1])
        } else {
            None
        }
    }
}

impl<'a> ArrayIter<'a> {
    pub closed spec fn elts(&self) -> Seq<Value> {
        vstd::std_specs::slice::into_iter_elts(self.inner)
    }

    pub closed spec fn iter_wf(&self) -> bool {
        IteratorSpec::obeys_prophetic_iter_laws(&self.inner)
    }

    pub(super) broadcast proof fn reveal_model(&self)
        ensures
            self.elts() == vstd::std_specs::slice::into_iter_elts(self.inner),
            self.iter_wf() == IteratorSpec::obeys_prophetic_iter_laws(&self.inner),
            #[trigger] IteratorSpec::remaining(self)
                == IteratorSpec::remaining(&self.inner),
            IteratorSpec::will_return_none(self)
                == IteratorSpec::will_return_none(&self.inner),
            IteratorSpec::decrease(self) == IteratorSpec::decrease(&self.inner),
    {
    }
}

impl<'a> IteratorSpecImpl for ArrayIter<'a> {
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

}
