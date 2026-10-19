// This file contains specifications for `Value` and its methods.
//
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::arithmetic_side_effects,
    clippy::float_cmp,
    clippy::unwrap_used,
    clippy::unreachable,
    clippy::option_if_let_else,
    clippy::unseparated_literal_suffix,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

use vstd::prelude::*;

verus! {

use crate::number::*;
use crate::value::*;
use crate::verify::number_proofs::*;
use crate::verify::number_specs::*;
use vstd::std_specs::convert::*;

pub assume_specification[ <Value as Clone>::clone ](v: &Value) -> (res: Value)
    ensures
        res@ == v@,
;

pub enum ObjectView {
    Empty,
    Frozen(Seq<(ValueView, ValueView)>),
    Map(vstd::map::Map<ValueView, ValueView>),
}

pub enum ValueView {
    Null,
    Bool(bool),
    Number(NumberView),
    String(Seq<char>),
    Array(Seq<ValueView>),
    Set(vstd::set::Set<ValueView>),
    Object(ObjectView),
    Undefined,
}

impl FromSpecImpl<bool> for Value {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    closed spec fn from_spec(value: bool) -> Value {
        Value::Bool(value)
    }
}

impl FromSpecImpl<Number> for Value {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    closed spec fn from_spec(value: Number) -> Value {
        Value::Number(value)
    }
}

impl FromSpecImpl<Vec<Value>> for Value {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    closed spec fn from_spec(values: Vec<Value>) -> Value {
        Value::Array(crate::Rc::new(
            <Array as FromSpec<Vec<Value>>>::from_spec(values),
        ))
    }
}

impl FromSpecImpl<BTreeSet<Value>> for Value {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    closed spec fn from_spec(values: BTreeSet<Value>) -> Value {
        Value::Set(crate::Rc::new(
            <crate::value::Set as FromSpec<BTreeSet<Value>>>::from_spec(values),
        ))
    }
}

} // end verus!
