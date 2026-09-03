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

} // end verus!
