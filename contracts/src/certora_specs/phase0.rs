#![allow(dead_code)]

#[cfg(feature = "certora-storage-symbols")]
use crate::c_pool::storage_types::DataKey;
use crate::c_pool::{comet::CometPoolContract, metadata::get_total_shares};
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
