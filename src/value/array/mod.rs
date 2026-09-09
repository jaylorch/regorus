// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! See [`Array`].

mod iter;
mod serde;

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;
use core::ops;
use vstd::prelude::*;

use crate::value::Value;

pub use iter::{ArrayIntoIter, ArrayIter, ArrayIterMut};

/// Opaque, ordered sequence of [`Value`]s.
///
/// The current backing storage is `Vec<Value>`. The inner field is private so
/// the representation can change without touching call sites.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Default, Clone, Eq, PartialEq)]
pub struct Array {
    inner: Vec<Value>,
}

#[verus_verify]
impl Array {
    /// Create an empty `Array`.
    #[inline]
    #[verus_spec(result =>
        ensures
            result@ == Seq::<ValueView>::empty(),
    )]
    pub const fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[inline]
    #[verus_spec(result =>
        ensures
            result == self@.len(),
    )]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    #[verus_spec(result =>
        ensures
            result <==> self@.len() == 0,
    )]
    pub const fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[inline]
    #[verus_spec(result =>
        ensures
            match result {
                Some(value) => index < self@.len() && value@ == self@[index as int],
                None => index >= self@.len(),
            },
    )]
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.inner.get(index)
    }

    #[inline]
    // We have to mark this one external until Verus issue #2902 is fixed.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            match result {
                Some(value) => {
                    &&& index < old(self)@.len()
                    &&& value@ == old(self)@[index as int]
                    &&& final(self)@ == old(self)@.update(index as int, final(value)@)
                },
                None => {
                    &&& index >= old(self)@.len()
                    &&& final(self)@ == old(self)@
                },
            },
    )]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut Value> {
        self.inner.get_mut(index)
    }

    #[inline]
    #[verus_spec(result =>
        ensures
            match result {
                Some(value) => self@.len() > 0 && value@ == self@[0],
                None => self@.len() == 0,
            },
    )]
    pub fn first(&self) -> Option<&Value> {
        self.inner.first()
    }

    #[inline]
    #[verus_spec(result =>
        ensures
            match result {
                Some(value) => self@.len() > 0 && value@ == self@.last(),
                None => self@.len() == 0,
            },
    )]
    pub fn last(&self) -> Option<&Value> {
        self.inner.last()
    }

    #[inline]
    // We can only assume this specification until we have a useful
    // spec for the equality operation on values.
    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures
            result == self@.contains(value@),
    )]
    pub fn contains(&self, value: &Value) -> bool {
        self.inner.contains(value)
    }

    #[inline]
    #[verus_spec(result =>
        ensures
            value_seq_view(result@) == self@,
    )]
    pub const fn as_slice(&self) -> &[Value] {
        self.inner.as_slice()
    }

    /// Iteration in element order. Non-resumable.
    #[inline]
    #[verus_verify(external)]
    pub fn iter(&self) -> ArrayIter<'_> {
        ArrayIter {
            inner: self.inner.iter(),
        }
    }

    #[inline]
    #[verus_verify(external)]
    pub fn iter_mut(&mut self) -> ArrayIterMut<'_> {
        ArrayIterMut {
            inner: self.inner.iter_mut(),
        }
    }

    #[inline]
    #[verus_spec(
        ensures
            final(self)@ == old(self)@.push(value@),
    )]
    pub fn push(&mut self, value: Value) {
        self.inner.push(value);
    }

    #[inline]
    #[verus_spec(
        ensures
            final(self)@ == old(self)@ + old(other)@,
            final(other)@ == Seq::<ValueView>::empty(),
    )]
    pub fn append(&mut self, other: &mut Array) {
        self.inner.append(&mut other.inner);
    }

    #[inline]
    #[verus_verify(external_body)]
    pub fn extend<I: IntoIterator<Item = Value>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }

    /// Append all elements of `other` (by clone) to the end of `self`.
    #[inline]
    #[verus_spec(
        ensures
            final(self)@ == old(self)@ + value_seq_view(other@),
    )]
    pub fn extend_from_slice(&mut self, other: &[Value]) {
        self.inner.extend_from_slice(other);
    }

    #[inline]
    #[verus_verify(external_body)]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&Value) -> bool,
    {
        self.inner.retain(f);
    }

    #[inline]
    #[verus_spec(
        ensures
            final(self)@ == Seq::<ValueView>::empty(),
    )]
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    #[inline]
    #[verus_verify(external_body)]
    pub fn reverse(&mut self) {
        self.inner.reverse();
    }

    #[inline]
    #[verus_verify(external_body)]
    pub fn sort(&mut self) {
        self.inner.sort();
    }

    #[inline]
    #[verus_spec(result =>
        ensures
            value_seq_view(result@) == self@,
    )]
    pub fn to_vec(&self) -> Vec<Value> {
        self.inner.clone()
    }

    #[inline]
    #[verus_spec(result =>
        ensures
            value_seq_view(result@) == self@,
    )]
    pub fn into_vec(self) -> Vec<Value> {
        self.inner
    }

    /// Wrap into a `Value::Array`.
    #[inline]
    #[verus_spec(result =>
        ensures
            result@ == ValueView::Array(self@),
    )]
    pub fn into_value(self) -> Value {
        Value::Array(crate::Rc::new(self))
    }

    /// Create a resumable cursor over elements in order. O(1).
    #[inline]
    #[verus_spec(result =>
        ensures
            result@ == 0,
    )]
    pub const fn cursor(&self) -> ArrayCursor {
        ArrayCursor { index: 0 }
    }

    /// Advance `cursor` and yield the next element.
    #[verus_spec(result =>
        ensures
            match result {
                Some(value) => {
                    &&& old(cursor)@ < self@.len()
                    &&& value@ == self@[old(cursor)@ as int]
                    &&& final(cursor)@ == old(cursor)@ + 1
                },
                None => {
                    &&& old(cursor)@ >= self@.len()
                    &&& final(cursor)@ == old(cursor)@
                },
            },
    )]
    pub fn next<'a>(&'a self, cursor: &mut ArrayCursor) -> Option<&'a Value> {
        let value = self.inner.get(cursor.index)?;
        proof! {
            // Prove that the saturating add below always just increments by 1.
            assert(self@.len() <= usize::MAX) by {
                vstd::std_specs::vec::axiom_spec_len(&self.inner);
            }
        }
        cursor.index = cursor.index.saturating_add(1);
        Some(value)
    }
}

/// Opaque resumable cursor over an [`Array`]'s elements.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Clone)]
pub struct ArrayCursor {
    index: usize,
}

impl Ord for Array {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl PartialOrd for Array {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Array {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl Extend<Value> for Array {
    fn extend<I: IntoIterator<Item = Value>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }
}

impl FromIterator<Value> for Array {
    fn from_iter<I: IntoIterator<Item = Value>>(iter: I) -> Self {
        Self {
            inner: Vec::from_iter(iter),
        }
    }
}

#[verus_verify]
impl From<Vec<Value>> for Array {
    #[inline]
    #[verus_spec(result =>
        ensures
            result@ == value_seq_view(values@),
    )]
    fn from(values: Vec<Value>) -> Self {
        Self { inner: values }
    }
}

#[verus_verify]
impl ops::Index<usize> for Array {
    type Output = Value;

    /// Indexes the array. Returns `&Value::Undefined` for out-of-range
    /// indices rather than panicking, matching `Value`'s indexing semantics.
    /// Use [`Array::get`] to distinguish "missing" from "present-and-Undefined".
    #[inline]
    #[verus_spec(result =>
        ensures
            result@ == if index < self@.len() {
                self@[index as int]
            } else {
                ValueView::Undefined
            },
    )]
    fn index(&self, index: usize) -> &Self::Output {
        self.inner.get(index).unwrap_or(&Value::Undefined)
    }
}

#[verus_verify]
impl From<Array> for Value {
    #[inline]
    #[verus_spec(result =>
        ensures
            result@ == ValueView::Array(a@),
    )]
    fn from(a: Array) -> Self {
        a.into_value()
    }
}

#[cfg(verus_keep_ghost)]
verus! {

use super::specs::ValueView;
use crate::verify::utils::*;
use vstd::std_specs::convert::*;

impl FromSpecImpl<Vec<Value>> for Array {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    closed spec fn from_spec(values: Vec<Value>) -> Array {
        Array{ inner: values }
    }
}

impl FromSpecImpl<Array> for Value {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    closed spec fn from_spec(array: Array) -> Value {
        Value::Array(crate::Rc::new(array))
    }
}

pub closed spec fn value_seq_view(values: Seq<Value>) -> Seq<ValueView>
    decreases
        values,
{
    Seq::new(values.len(), |index: int|
        if 0 <= index < values.len() {
            values[index]@
        } else {
            ValueView::Undefined
        }
    )
}

pub closed spec fn value_array_view(a: Array) -> Seq<ValueView>
    decreases
        a,
{
    value_seq_view(a.inner@)
}

impl View for Array {
    type V = Seq<ValueView>;

    open spec fn view(&self) -> Seq<ValueView>
        decreases self,
    {
        value_array_view(*self)
    }
}

impl View for ArrayCursor {
    type V = usize;

    closed spec fn view(&self) -> usize {
        self.index
    }
}

}
