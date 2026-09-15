//! Phase 1 token-vector and record-map foundation.

#![allow(dead_code)]
#![cfg(feature = "certora-pool-collections-ghost")]

#[cfg(feature = "certora-lp-balance-ghost")]
use crate::c_pool::balance::{
    certora_reset_balance_ghost, certora_watch_balance, certora_write_balance, read_balance,
};
#[cfg(feature = "certora-pool-scalar-ghost")]
use crate::c_pool::metadata::{
    certora_reset_pool_scalar_ghost, get_total_shares, has_controller, put_total_shares,
    read_controller, read_freeze, read_swap_fee, write_controller, write_freeze, write_swap_fee,
};
use crate::c_pool::{
    metadata::{
        certora_read_pool_records as read_record, certora_read_pool_tokens as read_tokens,
        certora_reset_pool_collections_ghost, certora_write_pool_records as write_record,
        certora_write_pool_tokens as write_tokens, CertoraPoolRecordMap, CertoraPoolTokenVec,
    },
    storage_types::Record,
};
use cvlr_asserts::{cvlr_assert, cvlr_assume, cvlr_satisfy};
use cvlr_soroban_derive::rule;
use soroban_sdk::{Address, Env};

fn two_tokens(first: Address, second: Address) -> CertoraPoolTokenVec {
    let mut tokens = CertoraPoolTokenVec::new();
    tokens.push_back(first);
    tokens.push_back(second);
    tokens
}

fn two_records(
    first: Address,
    first_record: Record,
    second: Address,
    second_record: Record,
) -> CertoraPoolRecordMap {
    let mut records = CertoraPoolRecordMap::new();
    records.set(first, first_record);
    records.set(second, second_record);
    records
}

fn fixed_second_record() -> Record {
    Record {
        balance: 41,
        weight: 42,
        scalar: 43,
        index: 1,
    }
}

fn indexed_record(index: u32) -> Record {
    Record {
        balance: 100 + index as i128,
        weight: 200 + index as i128,
        scalar: 300 + index as i128,
        index,
    }
}

fn eight_records(
    token_0: &Address,
    token_1: &Address,
    token_2: &Address,
    token_3: &Address,
    token_4: &Address,
    token_5: &Address,
    token_6: &Address,
    token_7: &Address,
) -> CertoraPoolRecordMap {
    let mut records = CertoraPoolRecordMap::new();
    records.set(token_0.clone(), indexed_record(0));
    records.set(token_1.clone(), indexed_record(1));
    records.set(token_2.clone(), indexed_record(2));
    records.set(token_3.clone(), indexed_record(3));
    records.set(token_4.clone(), indexed_record(4));
    records.set(token_5.clone(), indexed_record(5));
    records.set(token_6.clone(), indexed_record(6));
    records.set(token_7.clone(), indexed_record(7));
    records
}

macro_rules! record_replacement_rule {
    (
        $name:ident,
        target $target:ident : $target_index:literal,
        length $length:literal,
        records [$($token:ident : $index:literal),+ $(,)?],
        distinct [$($left:ident != $right:ident),* $(,)?] $(,)?
    ) => {
        #[rule]
        fn $name(e: Env, $($token: Address),+) {
            $(cvlr_assume!($left != $right);)*
            certora_reset_pool_collections_ghost();

            let mut records = CertoraPoolRecordMap::new();
            $(records.set($token.clone(), indexed_record($index));)+
            records.set($target.clone(), indexed_record(10 + $target_index));
            write_record(&e, records);

            let observed_records = read_record(&e);
            cvlr_assert!(observed_records.len() == $length);
            $(
                cvlr_assert!(
                    observed_records.get($token).unwrap()
                        == if $index == $target_index {
                            indexed_record(10 + $target_index)
                        } else {
                            indexed_record($index)
                        }
                );
            )+
        }
    };
}

fn eight_distinct(
    token_0: &Address,
    token_1: &Address,
    token_2: &Address,
    token_3: &Address,
    token_4: &Address,
    token_5: &Address,
    token_6: &Address,
    token_7: &Address,
) -> bool {
    token_0 != token_1
        && token_0 != token_2
        && token_0 != token_3
        && token_0 != token_4
        && token_0 != token_5
        && token_0 != token_6
        && token_0 != token_7
        && token_1 != token_2
        && token_1 != token_3
        && token_1 != token_4
        && token_1 != token_5
        && token_1 != token_6
        && token_1 != token_7
        && token_2 != token_3
        && token_2 != token_4
        && token_2 != token_5
        && token_2 != token_6
        && token_2 != token_7
        && token_3 != token_4
        && token_3 != token_5
        && token_3 != token_6
        && token_3 != token_7
        && token_4 != token_5
        && token_4 != token_6
        && token_4 != token_7
        && token_5 != token_6
        && token_5 != token_7
        && token_6 != token_7
}

/// Both collection accessors must preserve arbitrary token and record values.
#[rule]
fn phase1_collection_ghost_round_trip(
    e: Env,
    first: Address,
    second: Address,
    balance: i128,
    weight: i128,
    scalar: i128,
    index: u32,
) {
    cvlr_assume!(first != second);
    certora_reset_pool_collections_ghost();

    let first_record = Record {
        balance,
        weight,
        scalar,
        index,
    };
    write_tokens(&e, two_tokens(first.clone(), second.clone()));
    write_record(
        &e,
        two_records(
            first.clone(),
            first_record.clone(),
            second.clone(),
            fixed_second_record(),
        ),
    );

    let observed_tokens = read_tokens(&e);
    let observed_records = read_record(&e);
    cvlr_assert!(observed_tokens.len() == 2);
    cvlr_assert!(observed_tokens.get(0).unwrap() == first.clone());
    cvlr_assert!(observed_tokens.get(1).unwrap() == second.clone());
    cvlr_assert!(observed_tokens.get(2).is_none());
    cvlr_assert!(observed_records.len() == 2);
    cvlr_assert!(observed_records.contains_key(first.clone()));
    cvlr_assert!(observed_records.contains_key(second.clone()));
    cvlr_assert!(observed_records.get(first).unwrap() == first_record);
    cvlr_assert!(observed_records.get(second).unwrap() == fixed_second_record());
}

/// Equal addresses must alias one key, while a distinct address remains absent.
#[rule]
fn phase1_collection_equal_address_aliasing(
    e: Env,
    stored: Address,
    alias: Address,
    unbound: Address,
) {
    cvlr_assume!(stored == alias);
    cvlr_assume!(stored != unbound);
    certora_reset_pool_collections_ghost();

    let initial = indexed_record(0);
    let replacement = indexed_record(1);
    let mut records = CertoraPoolRecordMap::new();
    records.set(stored.clone(), initial);
    write_record(&e, records);

    let mut updated_records = read_record(&e);
    updated_records.set(alias.clone(), replacement.clone());
    write_record(&e, updated_records);

    let observed_records = read_record(&e);
    cvlr_assert!(observed_records.len() == 1);
    cvlr_assert!(observed_records.get(stored).unwrap() == replacement);
    cvlr_assert!(observed_records.get(alias).unwrap() == indexed_record(1));
    cvlr_assert!(!observed_records.contains_key(unbound));
}

/// Witness that equal aliases and a distinct unbound address coexist.
#[rule]
fn phase1_collection_aliasing_reachable(stored: Address, alias: Address, unbound: Address) {
    cvlr_satisfy!(stored == alias && stored != unbound);
}

/// Exercise every explicit slot at the pool's maximum supported token count.
#[rule]
fn phase1_collection_ghost_eight_slot_capacity(
    e: Env,
    token_0: Address,
    token_1: Address,
    token_2: Address,
    token_3: Address,
    token_4: Address,
    token_5: Address,
    token_6: Address,
    token_7: Address,
) {
    cvlr_assume!(eight_distinct(
        &token_0, &token_1, &token_2, &token_3, &token_4, &token_5, &token_6, &token_7,
    ));
    certora_reset_pool_collections_ghost();

    let mut tokens = CertoraPoolTokenVec::new();
    tokens.push_back(token_0.clone());
    tokens.push_back(token_1.clone());
    tokens.push_back(token_2.clone());
    tokens.push_back(token_3.clone());
    tokens.push_back(token_4.clone());
    tokens.push_back(token_5.clone());
    tokens.push_back(token_6.clone());
    tokens.push_back(token_7.clone());
    write_tokens(&e, tokens);

    let records = eight_records(
        &token_0, &token_1, &token_2, &token_3, &token_4, &token_5, &token_6, &token_7,
    );
    write_record(&e, records);

    let observed_tokens = read_tokens(&e);
    let observed_records = read_record(&e);
    cvlr_assert!(observed_tokens.len() == 8);
    cvlr_assert!(observed_records.len() == 8);
    cvlr_assert!(observed_tokens.get(0).unwrap() == token_0.clone());
    cvlr_assert!(observed_tokens.get(1).unwrap() == token_1.clone());
    cvlr_assert!(observed_tokens.get(2).unwrap() == token_2.clone());
    cvlr_assert!(observed_tokens.get(3).unwrap() == token_3.clone());
    cvlr_assert!(observed_tokens.get(4).unwrap() == token_4.clone());
    cvlr_assert!(observed_tokens.get(5).unwrap() == token_5.clone());
    cvlr_assert!(observed_tokens.get(6).unwrap() == token_6.clone());
    cvlr_assert!(observed_tokens.get(7).unwrap() == token_7.clone());
    cvlr_assert!(observed_records.get(token_0).unwrap() == indexed_record(0));
    cvlr_assert!(observed_records.get(token_1).unwrap() == indexed_record(1));
    cvlr_assert!(observed_records.get(token_2).unwrap() == indexed_record(2));
    cvlr_assert!(observed_records.get(token_3).unwrap() == indexed_record(3));
    cvlr_assert!(observed_records.get(token_4).unwrap() == indexed_record(4));
    cvlr_assert!(observed_records.get(token_5).unwrap() == indexed_record(5));
    cvlr_assert!(observed_records.get(token_6).unwrap() == indexed_record(6));
    cvlr_assert!(observed_records.get(token_7).unwrap() == indexed_record(7));
}

// Each constant-size rule keeps the verifier away from symbolic indexing while
// exercising one handwritten replacement branch and every preceding key test.
record_replacement_rule!(
    phase1_collection_record_replacement_slot_0,
    target token_0: 0,
    length 1,
    records [token_0: 0],
    distinct [],
);
record_replacement_rule!(
    phase1_collection_record_replacement_slot_1,
    target token_1: 1,
    length 2,
    records [token_0: 0, token_1: 1],
    distinct [token_0 != token_1],
);
record_replacement_rule!(
    phase1_collection_record_replacement_slot_2,
    target token_2: 2,
    length 3,
    records [token_0: 0, token_1: 1, token_2: 2],
    distinct [token_0 != token_1, token_0 != token_2, token_1 != token_2],
);
record_replacement_rule!(
    phase1_collection_record_replacement_slot_3,
    target token_3: 3,
    length 4,
    records [token_0: 0, token_1: 1, token_2: 2, token_3: 3],
    distinct [
        token_0 != token_1,
        token_0 != token_2,
        token_0 != token_3,
        token_1 != token_2,
        token_1 != token_3,
        token_2 != token_3,
    ],
);
record_replacement_rule!(
    phase1_collection_record_replacement_slot_4,
    target token_4: 4,
    length 5,
    records [token_0: 0, token_1: 1, token_2: 2, token_3: 3, token_4: 4],
    distinct [
        token_0 != token_1,
        token_0 != token_2,
        token_0 != token_3,
        token_0 != token_4,
        token_1 != token_2,
        token_1 != token_3,
        token_1 != token_4,
        token_2 != token_3,
        token_2 != token_4,
        token_3 != token_4,
    ],
);
record_replacement_rule!(
    phase1_collection_record_replacement_slot_5,
    target token_5: 5,
    length 6,
    records [token_0: 0, token_1: 1, token_2: 2, token_3: 3, token_4: 4, token_5: 5],
    distinct [
        token_0 != token_1,
        token_0 != token_2,
        token_0 != token_3,
        token_0 != token_4,
        token_0 != token_5,
        token_1 != token_2,
        token_1 != token_3,
        token_1 != token_4,
        token_1 != token_5,
        token_2 != token_3,
        token_2 != token_4,
        token_2 != token_5,
        token_3 != token_4,
        token_3 != token_5,
        token_4 != token_5,
    ],
);
record_replacement_rule!(
    phase1_collection_record_replacement_slot_6,
    target token_6: 6,
    length 7,
    records [
        token_0: 0,
        token_1: 1,
        token_2: 2,
        token_3: 3,
        token_4: 4,
        token_5: 5,
        token_6: 6,
    ],
    distinct [
        token_0 != token_1,
        token_0 != token_2,
        token_0 != token_3,
        token_0 != token_4,
        token_0 != token_5,
        token_0 != token_6,
        token_1 != token_2,
        token_1 != token_3,
        token_1 != token_4,
        token_1 != token_5,
        token_1 != token_6,
        token_2 != token_3,
        token_2 != token_4,
        token_2 != token_5,
        token_2 != token_6,
        token_3 != token_4,
        token_3 != token_5,
        token_3 != token_6,
        token_4 != token_5,
        token_4 != token_6,
        token_5 != token_6,
    ],
);
record_replacement_rule!(
    phase1_collection_record_replacement_slot_7,
    target token_7: 7,
    length 8,
    records [
        token_0: 0,
        token_1: 1,
        token_2: 2,
        token_3: 3,
        token_4: 4,
        token_5: 5,
        token_6: 6,
        token_7: 7,
    ],
    distinct [
        token_0 != token_1,
        token_0 != token_2,
        token_0 != token_3,
        token_0 != token_4,
        token_0 != token_5,
        token_0 != token_6,
        token_0 != token_7,
        token_1 != token_2,
        token_1 != token_3,
        token_1 != token_4,
        token_1 != token_5,
        token_1 != token_6,
        token_1 != token_7,
        token_2 != token_3,
        token_2 != token_4,
        token_2 != token_5,
        token_2 != token_6,
        token_2 != token_7,
        token_3 != token_4,
        token_3 != token_5,
        token_3 != token_6,
        token_3 != token_7,
        token_4 != token_5,
        token_4 != token_6,
        token_4 != token_7,
        token_5 != token_6,
        token_5 != token_7,
        token_6 != token_7,
    ],
);

/// Witness that both full-capacity collections and slot-seven replacement
/// return normally with every populated getter live.
#[rule]
fn phase1_collection_record_replacement_slot_7_reachable(
    e: Env,
    token_0: Address,
    token_1: Address,
    token_2: Address,
    token_3: Address,
    token_4: Address,
    token_5: Address,
    token_6: Address,
    token_7: Address,
) {
    certora_reset_pool_collections_ghost();

    let mut tokens = CertoraPoolTokenVec::new();
    tokens.push_back(token_0.clone());
    tokens.push_back(token_1.clone());
    tokens.push_back(token_2.clone());
    tokens.push_back(token_3.clone());
    tokens.push_back(token_4.clone());
    tokens.push_back(token_5.clone());
    tokens.push_back(token_6.clone());
    tokens.push_back(token_7.clone());
    write_tokens(&e, tokens);

    let mut records = eight_records(
        &token_0, &token_1, &token_2, &token_3, &token_4, &token_5, &token_6, &token_7,
    );
    records.set(token_7.clone(), indexed_record(17));
    write_record(&e, records);

    let observed_tokens = read_tokens(&e);
    let observed_records = read_record(&e);
    cvlr_satisfy!(
        eight_distinct(
            &token_0, &token_1, &token_2, &token_3, &token_4, &token_5, &token_6, &token_7,
        ) && observed_tokens.len() == 8
            && observed_tokens.get(0).unwrap() == token_0.clone()
            && observed_tokens.get(1).unwrap() == token_1.clone()
            && observed_tokens.get(2).unwrap() == token_2.clone()
            && observed_tokens.get(3).unwrap() == token_3.clone()
            && observed_tokens.get(4).unwrap() == token_4.clone()
            && observed_tokens.get(5).unwrap() == token_5.clone()
            && observed_tokens.get(6).unwrap() == token_6.clone()
            && observed_tokens.get(7).unwrap() == token_7.clone()
            && observed_records.len() == 8
            && observed_records.get(token_0).unwrap() == indexed_record(0)
            && observed_records.get(token_1).unwrap() == indexed_record(1)
            && observed_records.get(token_2).unwrap() == indexed_record(2)
            && observed_records.get(token_3).unwrap() == indexed_record(3)
            && observed_records.get(token_4).unwrap() == indexed_record(4)
            && observed_records.get(token_5).unwrap() == indexed_record(5)
            && observed_records.get(token_6).unwrap() == indexed_record(6)
            && observed_records.get(token_7).unwrap() == indexed_record(17)
    );
}

/// Witness that the maximum-size rule's pairwise-distinct precondition is live.
#[rule]
fn phase1_eight_distinct_tokens_reachable(
    token_0: Address,
    token_1: Address,
    token_2: Address,
    token_3: Address,
    token_4: Address,
    token_5: Address,
    token_6: Address,
    token_7: Address,
) {
    cvlr_satisfy!(eight_distinct(
        &token_0, &token_1, &token_2, &token_3, &token_4, &token_5, &token_6, &token_7,
    ));
}

/// Replacing either collection must leave the other collection unchanged.
#[rule]
fn phase1_collection_ghost_fields_are_isolated(e: Env, first: Address, second: Address) {
    cvlr_assume!(first != second);
    certora_reset_pool_collections_ghost();

    let first_record = Record {
        balance: 31,
        weight: 32,
        scalar: 33,
        index: 0,
    };
    let second_record = fixed_second_record();
    write_tokens(&e, two_tokens(first.clone(), second.clone()));
    write_record(
        &e,
        two_records(
            first.clone(),
            first_record,
            second.clone(),
            second_record.clone(),
        ),
    );

    let replacement = Record {
        balance: 51,
        weight: 52,
        scalar: 53,
        index: 0,
    };
    let mut updated_records = read_record(&e);
    updated_records.set(first.clone(), replacement.clone());
    write_record(&e, updated_records);

    let tokens_after_record_write = read_tokens(&e);
    cvlr_assert!(tokens_after_record_write.get(0).unwrap() == first.clone());
    cvlr_assert!(tokens_after_record_write.get(1).unwrap() == second.clone());
    cvlr_assert!(read_record(&e).get(first.clone()).unwrap() == replacement);
    cvlr_assert!(read_record(&e).get(second.clone()).unwrap() == second_record);

    write_tokens(&e, two_tokens(second.clone(), first.clone()));
    let records_after_token_write = read_record(&e);
    cvlr_assert!(read_tokens(&e).get(0).unwrap() == second.clone());
    cvlr_assert!(read_tokens(&e).get(1).unwrap() == first.clone());
    cvlr_assert!(records_after_token_write.get(first).unwrap() == replacement);
    cvlr_assert!(records_after_token_write.get(second).unwrap() == second_record);
}

/// Collection writes must not change the scalar projection, or vice versa.
#[cfg(feature = "certora-pool-scalar-ghost")]
#[rule]
fn phase1_collection_and_scalar_ghosts_are_isolated(e: Env, first: Address, second: Address) {
    cvlr_assume!(first != second);
    certora_reset_pool_collections_ghost();
    certora_reset_pool_scalar_ghost();
    write_controller(&e, first.clone());
    write_swap_fee(&e, 22);
    put_total_shares(&e, 33);
    write_freeze(&e, true);

    write_tokens(&e, two_tokens(first.clone(), second.clone()));
    write_record(
        &e,
        two_records(
            first.clone(),
            Record {
                balance: 31,
                weight: 32,
                scalar: 33,
                index: 0,
            },
            second.clone(),
            fixed_second_record(),
        ),
    );
    cvlr_assert!(has_controller(&e));
    cvlr_assert!(read_controller(&e) == first.clone());
    cvlr_assert!(read_swap_fee(&e) == 22);
    cvlr_assert!(get_total_shares(&e) == 33);
    cvlr_assert!(read_freeze(&e));

    write_controller(&e, second.clone());
    write_swap_fee(&e, 23);
    put_total_shares(&e, 34);
    write_freeze(&e, false);
    cvlr_assert!(read_controller(&e) == second.clone());
    cvlr_assert!(read_tokens(&e).get(0).unwrap() == first.clone());
    cvlr_assert!(read_tokens(&e).get(1).unwrap() == second.clone());
    cvlr_assert!(read_record(&e).get(first).unwrap().index == 0);
    cvlr_assert!(read_record(&e).get(second).unwrap() == fixed_second_record());
}

/// Collection writes must not change the watched LP projection, or vice versa.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase1_collection_and_lp_ghosts_are_isolated(e: Env, first: Address, second: Address) {
    cvlr_assume!(first != second);
    certora_reset_pool_collections_ghost();
    certora_reset_balance_ghost();
    certora_watch_balance(first.clone(), 61);

    write_tokens(&e, two_tokens(first.clone(), second.clone()));
    write_record(
        &e,
        two_records(
            first.clone(),
            Record {
                balance: 31,
                weight: 32,
                scalar: 33,
                index: 0,
            },
            second.clone(),
            fixed_second_record(),
        ),
    );
    cvlr_assert!(read_balance(&e, first.clone()) == 61);

    certora_write_balance(&e, first.clone(), 62);
    cvlr_assert!(read_tokens(&e).get(0).unwrap() == first.clone());
    cvlr_assert!(read_tokens(&e).get(1).unwrap() == second.clone());
    cvlr_assert!(read_record(&e).get(first).unwrap().index == 0);
    cvlr_assert!(read_record(&e).get(second).unwrap() == fixed_second_record());
}

/// A two-token initialized projection keeps each vector position associated
/// with the record stored under the same token address and index.
#[rule]
fn phase1_two_token_record_alignment(e: Env, first: Address, second: Address) {
    cvlr_assume!(first != second);
    certora_reset_pool_collections_ghost();
    write_tokens(&e, two_tokens(first.clone(), second.clone()));
    write_record(
        &e,
        two_records(
            first.clone(),
            Record {
                balance: 31,
                weight: 32,
                scalar: 33,
                index: 0,
            },
            second.clone(),
            fixed_second_record(),
        ),
    );

    let tokens = read_tokens(&e);
    let records = read_record(&e);
    let token_0 = tokens.get(0).unwrap();
    let token_1 = tokens.get(1).unwrap();
    cvlr_assert!(records.get(token_0).unwrap().index == 0);
    cvlr_assert!(records.get(token_1).unwrap().index == 1);
}

/// Witness a successful two-token collection setup with distinct addresses.
#[rule]
fn phase1_collection_foundation_reachable(e: Env, first: Address, second: Address) {
    certora_reset_pool_collections_ghost();
    write_tokens(&e, two_tokens(first.clone(), second.clone()));
    write_record(
        &e,
        two_records(
            first.clone(),
            Record {
                balance: 31,
                weight: 32,
                scalar: 33,
                index: 0,
            },
            second.clone(),
            fixed_second_record(),
        ),
    );

    cvlr_satisfy!(
        first != second
            && read_tokens(&e).len() == 2
            && read_record(&e).len() == 2
            && read_record(&e).get(first).unwrap().index == 0
            && read_record(&e).get(second).unwrap().index == 1
    );
}
