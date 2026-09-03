// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use vstd::prelude::*;

verus! {

use std::sync::Arc;
use super::array::value_array_view;
use super::object::{Object, Repr};
use super::set::value_set_view;
use super::specs::{ObjectView, ValueView};
use super::Value;
use vstd::set::*;
use vstd::set_lib::*;
use vstd::std_specs::smart_ptrs::*;

pub closed spec fn value_pair_seq_view(entries: Seq<(Value, Value)>) -> Seq<(ValueView, ValueView)>
    decreases
        entries,
{
    Seq::new(entries.len(), |index: int|
        if 0 <= index < entries.len() {
            (entries[index].0@, entries[index].1@)
        } else {
            (ValueView::Undefined, ValueView::Undefined)
        }
    )
}

pub closed spec fn value_map_view(entries: Map<Value, Value>) -> Map<ValueView, ValueView>
    decreases
        entries,
{
    proof {
        assert forall|key: Value| #[trigger] entries.dom().contains(key) implies
                   decreases_to!(entries => key) && decreases_to!(entries => entries[key]) by {
            assert(decreases_to!((key, entries[key]) => (key, entries[key]).0));
            assert(decreases_to!((key, entries[key]) => (key, entries[key]).1));
        }
    }
    let keys = entries.dom().map(|key: Value|
        if entries.dom().contains(key) {
            key@
        } else {
            ValueView::Undefined
        }
    );
    vstd::map::Map::new(keys, |view_key: ValueView| {
        let key = choose|key: Value| #![auto]
            entries.dom().contains(key)
            && (if entries.dom().contains(key) {
                key@ == view_key
            } else {
                false
            });
        if entries.dom().contains(key) {
            entries[key]@
        } else {
            ValueView::Undefined
        }
   })
}

pub closed spec fn object_view(obj: Object) -> ObjectView
    decreases
        obj,
{
    match obj.repr {
        Repr::Empty => ObjectView::Empty,
        Repr::Frozen(raw_entries) => ObjectView::Frozen(value_pair_seq_view(raw_entries@)),
        Repr::BTree(raw_entries) => ObjectView::Map(value_map_view(raw_entries@)),
    }
}

/// View implementation (internal to crate)

impl View for Value
{
    type V = ValueView;

    open(crate) spec fn view(&self) -> ValueView
        decreases self,
    {
        match *self {
            Value::Null => ValueView::Null,
            Value::Bool(b) => ValueView::Bool(b),
            Value::Number(n) => ValueView::Number(n@),
            Value::String(s) => ValueView::String(s@),
            Value::Array(arr) => ValueView::Array(value_array_view(*arr)),
            Value::Set(s) => ValueView::Set(value_set_view(*s)),
            Value::Object(obj) => ValueView::Object(object_view(*obj)),
            Value::Undefined => ValueView::Undefined,
        }
    }
}

}
