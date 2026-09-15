#![allow(dead_code)]

#[cfg(feature = "certora-lp-balance-ghost")]
use crate::c_pool::balance::{
    certora_reset_balance_ghost, certora_watch_balance, certora_write_balance, read_balance,
    receive_balance, spend_balance,
};
#[cfg(feature = "certora-storage-symbols")]
use crate::c_pool::storage_types::DataKey;
use crate::c_pool::{
    comet::CometPoolContract,
    metadata::{get_total_shares, put_total_shares},
};
use cvlr_asserts::{cvlr_assert, cvlr_assume, cvlr_satisfy};
use cvlr_soroban::is_auth;
use cvlr_soroban_derive::rule;
use soroban_sdk::{Address, Env, Vec};

#[cfg(feature = "certora-storage-symbols")]
macro_rules! cvlr_assert_pairwise_distinct {
    ($head:expr, $($tail:expr),+ $(,)?) => {
        $(cvlr_assert!($head != $tail);)+
        cvlr_assert_pairwise_distinct!($($tail),+);
    };
    ($last:expr $(,)?) => {};
}

/// Validate that the verification-only `DataKey` abstraction is injective.
///
/// This rule is intentionally absent from the production-key build. It checks
/// the complete finite key set rather than assuming storage-key separation.
#[cfg(feature = "certora-storage-symbols")]
#[rule]
fn phase0_conditional_data_key_symbols_are_injective() {
    cvlr_assert_pairwise_distinct!(
        DataKey::Factory
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
        DataKey::Controller
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
        DataKey::SwapFee
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
        DataKey::AllTokenVec
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
        DataKey::AllRecordData
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
        DataKey::TokenShare
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
        DataKey::TotalShares
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
        DataKey::PublicSwap
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
        DataKey::Finalize
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
        DataKey::Freeze
            .certora_storage_symbol()
            .to_val()
            .get_payload(),
    );
}

/// Check repeated reads after explicitly seeding the watched LP owner.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase0_conditional_lp_balance_round_trip(e: Env, account: Address) {
    certora_reset_balance_ghost();
    certora_watch_balance(account.clone(), 11);

    let first = read_balance(&e, account.clone());
    let second = read_balance(&e, account);

    cvlr_assert!(first == 11 && second == 11);
}

/// A write to the watched LP owner must update its projected balance.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase0_conditional_watched_lp_balance_updates(e: Env, account: Address) {
    certora_reset_balance_ghost();
    certora_watch_balance(account.clone(), 11);
    certora_write_balance(&e, account.clone(), 22);

    cvlr_assert!(read_balance(&e, account) == 22);
}

/// The normal LP credit/debit helpers must compose with the watched projection.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase0_conditional_lp_balance_helpers_update(e: Env, account: Address) {
    certora_reset_balance_ghost();
    certora_watch_balance(account.clone(), 11);
    receive_balance(&e, account.clone(), 5);
    spend_balance(&e, account.clone(), 3);

    cvlr_assert!(read_balance(&e, account) == 13);
}

/// Semantically equal addresses must alias the same watched LP balance.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase0_conditional_equal_lp_addresses_alias(e: Env, first: Address, second: Address) {
    cvlr_assume!(first == second);
    certora_reset_balance_ghost();
    certora_watch_balance(first.clone(), 11);
    certora_write_balance(&e, second.clone(), 22);

    cvlr_assert!(read_balance(&e, first) == 22);
    cvlr_assert!(read_balance(&e, second) == 22);
}

/// Witness that two symbolic inputs can denote the same address.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase0_conditional_equal_lp_addresses_reachable(first: Address, second: Address) {
    cvlr_satisfy!(first == second);
}

/// A write to another owner must not change the watched LP balance.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase0_conditional_distinct_lp_addresses_are_isolated(e: Env, first: Address, second: Address) {
    cvlr_assume!(first != second);
    certora_reset_balance_ghost();
    certora_watch_balance(first.clone(), 11);
    certora_write_balance(&e, second, 22);

    cvlr_assert!(read_balance(&e, first) == 11);
}

/// Witness that the distinct-address isolation rule has reachable inputs.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase0_conditional_distinct_lp_addresses_reachable(first: Address, second: Address) {
    cvlr_satisfy!(first != second);
}

/// Untracked owners remain unconstrained rather than implicitly having zero.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase0_conditional_untracked_lp_balance_is_unconstrained(
    e: Env,
    watched: Address,
    other: Address,
) {
    cvlr_assume!(watched != other);
    certora_reset_balance_ghost();
    certora_watch_balance(watched, 11);

    cvlr_satisfy!(read_balance(&e, other) == 22);
}

/// The production accessor path must round-trip a total-shares write/read.
#[rule]
fn phase0_total_shares_round_trip(e: Env) {
    put_total_shares(&e, 33);

    cvlr_assert!(get_total_shares(&e) == 33);
}

/// Isolate raw short-symbol host storage from the production TTL calls.
#[cfg(feature = "certora-storage-symbols")]
#[rule]
fn phase0_conditional_raw_total_shares_round_trip(e: Env) {
    let key = DataKey::TotalShares;
    e.storage().persistent().set(&key, &33_i128);
    let observed = e
        .storage()
        .persistent()
        .get::<DataKey, i128>(&key)
        .unwrap_or(0);

    cvlr_assert!(observed == 33);
}

/// A pool-storage write must not change the watched LP ghost balance.
#[cfg(all(
    feature = "certora-lp-balance-ghost",
    feature = "certora-storage-symbols"
))]
#[rule]
fn phase0_conditional_lp_balance_survives_pool_write(e: Env, account: Address) {
    certora_reset_balance_ghost();
    certora_watch_balance(account.clone(), 44);
    put_total_shares(&e, 33);

    cvlr_assert!(read_balance(&e, account) == 44);
}

/// Smoke test that a public storage getter is stable without an intervening
/// state-changing operation.
#[rule]
fn phase0_get_total_supply_is_stable(e: Env) {
    let first = CometPoolContract::get_total_supply(e.clone());
    let second = CometPoolContract::get_total_supply(e);

    cvlr_assert!(second == first);
}

/// Witness that the stable-getter smoke test covers a nonzero supply.
#[rule]
fn phase0_get_total_supply_nonzero_reachable(e: Env) {
    let first = CometPoolContract::get_total_supply(e.clone());
    let second = CometPoolContract::get_total_supply(e);

    cvlr_satisfy!(first != 0 && second == first);
}

/// Negative control: this intentionally false claim must report `Violated`.
#[rule]
fn phase0_negative_control_get_total_supply_is_not_stable(e: Env) {
    let first = CometPoolContract::get_total_supply(e.clone());
    let second = CometPoolContract::get_total_supply(e);

    cvlr_assert!(second != first);
}

/// Revert-observation probe for a join rejected by its amount guard.
///
/// A passing result establishes only that the call cannot return normally. It
/// does not expose post-revert storage, so it cannot establish failure
/// atomicity. The Phase 0 report records that limitation explicitly.
#[rule]
fn phase0_rejected_join_cannot_return(e: Env, user: Address) {
    let no_limits = Vec::new(&e);
    let authorized = is_auth(user.clone());

    cvlr_assume!(authorized);
    CometPoolContract::join_pool(e.clone(), 0, no_limits, user);

    cvlr_assert!(false);
}

/// Witness that the rejected-join probe's authorized pre-state is reachable.
#[rule]
fn phase0_rejected_join_prestate_reachable(e: Env, user: Address) {
    let before_total_shares = get_total_shares(&e);
    let authorized = is_auth(user);

    cvlr_satisfy!(authorized && before_total_shares == 0);
}
