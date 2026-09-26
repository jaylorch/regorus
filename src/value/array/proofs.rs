// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::{value_seq_view, ValueViewPredicate};
use crate::value::{specs::ValueView, Value};
use crate::verify::vec_assumptions::seq_retain_ensures;
use vstd::multiset::Multiset;
use vstd::prelude::*;

verus! {

pub(super) open spec fn insert_value_view(
) -> spec_fn(Multiset<ValueView>, Value) -> Multiset<ValueView> {
    |views: Multiset<ValueView>, value: Value| views.insert(value@)
}

proof fn lemma_value_seq_view_fold(values: Seq<Value>)
    ensures
        value_seq_view(values).to_multiset() ==
            values.fold_left(Multiset::empty(), insert_value_view()),
    decreases
        values.len(),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;

    if values.len() > 0 {
        let prefix = values.drop_last();
        lemma_value_seq_view_fold(prefix);
        assert(value_seq_view(values) =~= value_seq_view(prefix).push(values.last()@));
    }
}

pub(super) proof fn lemma_value_seq_view_multiset(
    old_values: Seq<Value>,
    new_values: Seq<Value>,
)
    requires
        new_values.to_multiset() == old_values.to_multiset(),
    ensures
        value_seq_view(new_values).to_multiset() ==
            value_seq_view(old_values).to_multiset(),
{
    assert(vstd::seq_lib::commutative_foldl(insert_value_view())) by {
        assert forall|left: Value, right: Value, views: Multiset<ValueView>|
            #[trigger] insert_value_view()(insert_value_view()(views, left), right) ==
                insert_value_view()(insert_value_view()(views, right), left) by {
            broadcast use vstd::multiset::group_multiset_axioms;
            assert(views.insert(left@).insert(right@) =~=
                views.insert(right@).insert(left@));
        }
    }
    vstd::seq_lib::lemma_fold_left_permutation(
        old_values,
        new_values,
        insert_value_view(),
        Multiset::empty(),
    );
    lemma_value_seq_view_fold(old_values);
    lemma_value_seq_view_fold(new_values);
}

proof fn lemma_value_seq_view_filter_index(
    values: Seq<Value>,
    keep: spec_fn(int) -> bool,
    view_predicate: ValueViewPredicate,
)
    requires
        forall|index: int|
            0 <= index < values.len() ==>
                #[trigger] keep(index) == view_predicate(values[index]@),
    ensures
        value_seq_view(values.filter_index(keep)) ==
            value_seq_view(values).filter(view_predicate),
    decreases
        values.len(),
{
    reveal(Seq::filter_index);
    reveal(Seq::filter);

    if values.len() > 0 {
        let prefix = values.drop_last();
        assert forall|index: int|
            0 <= index < prefix.len() implies
                #[trigger] keep(index) == view_predicate(prefix[index]@) by {
            assert(prefix[index] == values[index]);
        }
        lemma_value_seq_view_filter_index(prefix, keep, view_predicate);
        assert(value_seq_view(prefix) =~= value_seq_view(values).drop_last());

        let last_index = values.len() - 1;
        if keep(last_index) {
            assert(value_seq_view(prefix.filter_index(keep).push(values.last())) =~=
                value_seq_view(prefix.filter_index(keep)).push(values.last()@));
        }
    }
}

pub(super) proof fn lemma_seq_retain_view<F>(
    old_values: Seq<Value>,
    predicate: F,
    new_values: Seq<Value>,
    keep: Seq<bool>,
    view_predicate: ValueViewPredicate,
)
where
    F: FnMut(&Value) -> bool,
    requires
        seq_retain_ensures(old_values, predicate, new_values, keep),
        forall|value: Value, result: bool|
            #[trigger] call_ensures(predicate, (&value,), result) ==>
                result == view_predicate(value@),
    ensures
        value_seq_view(new_values) == value_seq_view(old_values).filter(view_predicate),
{
    assert forall|index: int|
        0 <= index < old_values.len() implies
            #[trigger] keep[index] == view_predicate(old_values[index]@) by {
        assert(value_seq_view(old_values)[index] == old_values[index]@);
        assert(call_ensures(predicate, (&old_values[index],), keep[index]));
    }
    lemma_value_seq_view_filter_index(
        old_values,
        |index: int| keep[index],
        view_predicate,
    );
}

} // verus!
