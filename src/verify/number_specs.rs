// This file contains specifications for `Number` and its methods.
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
use super::bigint_assumptions::*;
use super::f64_assumptions::*;
use vstd::float::*;
use vstd::std_specs::cmp::PartialEqSpec;

pub assume_specification[ <Number as Clone>::clone ](n: &Number) -> (res: Number)
    ensures
        res@ == n@,
;

pub enum NumberView {
    Integer(int),
    Float(f64),
}

pub open spec fn float_to_small_int(value: f64) -> Option<int>
{
    if !value.is_finite_spec() ||
       !spec_f64_fract(value).eq_spec(&0.0f64) ||
       spec_f64_abs(value) > 9_007_199_254_740_992.0 {
        None
    }
    else if value >= 0.0 {
        let value_as_u64 = ieee_float_cast::<f64, u64>(value);
        if ieee_float_cast::<u64, f64>(value_as_u64).eq_spec(&value) {
            Some(value_as_u64 as int)
        }
        else {
            None
        }
    }
    else {
        let value_as_i64 = ieee_float_cast::<f64, i64>(value);
        if ieee_float_cast::<i64, f64>(value_as_i64).eq_spec(&value) {
            Some(ieee_float_cast::<f64, i64>(value) as int)
        }
        else {
            None
        }
    }
}

pub open spec fn normalize_float(value: f64) -> NumberView
{
    match float_to_small_int(value) {
        Some(n) => NumberView::Integer(n),
        None => NumberView::Float(value),
    }
}

impl NumberView {
    pub open spec fn is_zero(&self) -> bool
    {
        match *self {
            Self::Integer(n) => n == 0,
            Self::Float(f) => f.eq_spec(&0.0f64),
        }
    }

    pub open spec fn to_int(&self) -> Option<int>
    {
        match *self {
            Self::Integer(n) => Some(n),
            Self::Float(f) => float_to_small_int(f),
        }
    }

    pub open spec fn to_f64_lossy_ensures(self: Self, f: f64) -> bool
    {
        match self {
            NumberView::Integer(v) =>
            {
                ||| 0 <= v <= u64::MAX && f == ieee_float_cast::<u64, f64>(v as u64)
                ||| i64::MIN <= v <= i64::MAX && f == ieee_float_cast::<i64, f64>(v as i64)
                ||| exists|bi: BigInt| {
                    &&& bi@ == v
                    &&& match #[trigger] super::bigint_assumptions::spec_bigint_to_f64(&bi) {
                        Some(x) => f == x,
                        None => f == if v < 0 { spec_f64_neg_infinity() } else { spec_f64_infinity() }
                    }
                }
            },
            NumberView::Float(v) => f == v,
        }
    }

    pub open spec fn as_u128_ensures(self: Self, result: Option<u128>) -> bool
    {
        match self {
            NumberView::Integer(value) => {
                if 0 <= value <= u128::MAX {
                    result matches Some(actual) && actual as int == value
                } else {
                    result is None
                }
            },
            NumberView::Float(value) => {
                if value.is_finite_spec()
                   && value.ieee_ge(0.0f64)
                   && spec_f64_fract(value).eq_spec(&0.0f64)
                   && ieee_float_cast::<u128, f64>(
                       ieee_float_cast::<f64, u128>(value),
                   ).eq_spec(&value) {
                    result matches Some(actual)
                        && actual == ieee_float_cast::<f64, u128>(value)
                } else {
                    result is None
                }
            },
        }
    }

    pub open spec fn as_i128_ensures(self: Self, result: Option<i128>) -> bool
    {
        match self {
            NumberView::Integer(value) => {
                if i128::MIN <= value <= i128::MAX {
                    result matches Some(actual) && actual as int == value
                } else {
                    result is None
                }
            },
            NumberView::Float(value) => {
                if value.is_finite_spec()
                   && spec_f64_fract(value).eq_spec(&0.0f64)
                   && ieee_float_cast::<i128, f64>(
                       ieee_float_cast::<f64, i128>(value),
                   ).eq_spec(&value) {
                    result matches Some(actual)
                        && actual == ieee_float_cast::<f64, i128>(value)
                } else {
                    result is None
                }
            },
        }
    }

    pub open spec fn as_u64_ensures(self: Self, result: Option<u64>) -> bool
    {
        match self {
            NumberView::Integer(value) => {
                if 0 <= value <= u64::MAX {
                    result matches Some(actual) && actual as int == value
                } else {
                    result is None
                }
            },
            NumberView::Float(value) => {
                if value.is_finite_spec()
                   && value.ieee_ge(0.0f64)
                   && spec_f64_fract(value).eq_spec(&0.0f64)
                   && value.ieee_le(ieee_float_cast::<u64, f64>(u64::MAX))
                   && ieee_float_cast::<u64, f64>(
                       ieee_float_cast::<f64, u64>(value),
                   ).eq_spec(&value) {
                    result matches Some(actual)
                        && actual == ieee_float_cast::<f64, u64>(value)
                } else {
                    result is None
                }
            },
        }
    }

    pub open spec fn as_i64_ensures(self: Self, result: Option<i64>) -> bool
    {
        match self {
            NumberView::Integer(value) => {
                if i64::MIN <= value <= i64::MAX {
                    result matches Some(actual) && actual as int == value
                } else {
                    result is None
                }
            },
            NumberView::Float(value) => {
                if value.is_finite_spec()
                   && spec_f64_fract(value).eq_spec(&0.0f64)
                   && value.ieee_ge(ieee_float_cast::<i64, f64>(i64::MIN))
                   && value.ieee_le(ieee_float_cast::<i64, f64>(i64::MAX))
                   && ieee_float_cast::<i64, f64>(
                       ieee_float_cast::<f64, i64>(value),
                   ).eq_spec(&value) {
                    result matches Some(actual)
                        && actual == ieee_float_cast::<f64, i64>(value)
                } else {
                    result is None
                }
            },
        }
    }

    pub open spec fn as_f64_ensures(self: Self, result: Option<f64>) -> bool
    {
        match (self, result) {
            (NumberView::Float(value), Some(actual)) =>
                value.is_finite_spec() && actual == value,
            (NumberView::Float(value), None) => !value.is_finite_spec(),
            (number @ NumberView::Integer(value), Some(actual)) => {
                &&& -9_007_199_254_740_992 <= value <= 9_007_199_254_740_992
                &&& number.to_f64_lossy_ensures(actual)
            },
            // The bounds intentionally overlap at +/-2^53: primitive variants return
            // Some there, while a BigInt variant with the same NumberView returns None.
            (NumberView::Integer(value), None) => {
                value <= -9_007_199_254_740_992 || 9_007_199_254_740_992 <= value
            },
        }
    }

    pub open spec fn add_ensures(self: Self, rhs: Self, result: Self) -> bool
    {
        match (self, rhs) {
            (NumberView::Integer(lhs), NumberView::Integer(rhs)) =>
                result matches NumberView::Integer(sum) && sum == lhs + rhs,
            _ => exists|a: f64, b: f64| {
                &&& self.to_f64_lossy_ensures(a)
                &&& rhs.to_f64_lossy_ensures(b)
                &&& match float_to_small_int(a + b) {
                    Some(sum) => result == NumberView::Integer(sum),
                    None => result == NumberView::Float(a + b),
                }
            },
        }
    }

    pub open spec fn sub_ensures(self: Self, rhs: Self, result: Self) -> bool
    {
        match (self, rhs) {
            (NumberView::Integer(lhs), NumberView::Integer(rhs)) =>
                result matches NumberView::Integer(diff) && diff == lhs - rhs,
            _ => exists|a: f64, b: f64| {
                &&& self.to_f64_lossy_ensures(a)
                &&& rhs.to_f64_lossy_ensures(b)
                &&& match float_to_small_int(a - b) {
                    Some(diff) => result == NumberView::Integer(diff),
                    None => result == NumberView::Float(a - b)
                }
            },
        }
    }

    pub open spec fn mul_ensures(self: Self, rhs: Self, result: Self) -> bool
    {
        match (self, rhs) {
            (NumberView::Integer(lhs), NumberView::Integer(rhs)) =>
                result matches NumberView::Integer(product) && product == lhs * rhs,
            _ => exists|a: f64, b: f64| {
                &&& self.to_f64_lossy_ensures(a)
                &&& rhs.to_f64_lossy_ensures(b)
                &&& match float_to_small_int(a * b) {
                    Some(product) => result == NumberView::Integer(product),
                    None => result == NumberView::Float(a * b)
                }
            },
        }
    }

    pub open spec fn div_ensures(self: Self, rhs: Self, result: Self) -> bool
    {
        match (self, rhs) {
            (NumberView::Integer(lhs), NumberView::Integer(divisor)) => {
                &&& divisor != 0
                &&& if vstd::arithmetic::div_mod::rust_rem(lhs, divisor) == 0 {
                    result == NumberView::Integer(
                        vstd::arithmetic::div_mod::rust_div(lhs, divisor),
                    )
                } else {
                    exists|a: f64, b: f64| {
                        &&& self.to_f64_lossy_ensures(a)
                        &&& rhs.to_f64_lossy_ensures(b)
                        &&& result == NumberView::Float(a / b)
                    }
                }
            },
            _ => {
                &&& !rhs.is_zero()
                &&& exists|a: f64, b: f64| {
                    &&& self.to_f64_lossy_ensures(a)
                    &&& rhs.to_f64_lossy_ensures(b)
                    &&& result == NumberView::Float(a / b)
                }
            },
        }
    }

}

} // end verus!
