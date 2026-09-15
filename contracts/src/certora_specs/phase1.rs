//! Phase 1 initialized-state foundation.

#![allow(dead_code)]
#![cfg(feature = "certora-pool-scalar-ghost")]

use crate::c_pool::metadata::{
    certora_reset_pool_scalar_ghost, get_total_shares, has_controller, put_total_shares,
    read_controller, read_freeze, read_swap_fee, write_controller, write_freeze, write_swap_fee,
};
#[cfg(feature = "certora-lp-balance-ghost")]
use crate::c_pool::{
    balance::{
        certora_reset_balance_ghost, certora_watch_balance, certora_write_balance, read_balance,
    },
    token_utility::mint_shares,
};
use cvlr_asserts::{cvlr_assert, cvlr_satisfy};
use cvlr_soroban_derive::rule;
use soroban_sdk::{Address, Env};

/// The scalar projection must reproduce the production accessors' defaults.
#[rule]
fn phase1_scalar_ghost_defaults(e: Env) {
    certora_reset_pool_scalar_ghost();

    cvlr_assert!(!has_controller(&e));
    cvlr_assert!(read_swap_fee(&e) == 0);
    cvlr_assert!(get_total_shares(&e) == 0);
    cvlr_assert!(!read_freeze(&e));
}

/// Every modeled scalar accessor must round-trip arbitrary values.
#[rule]
fn phase1_scalar_ghost_round_trip(
    e: Env,
    controller: Address,
    swap_fee: i128,
    total_shares: i128,
    freeze: bool,
) {
    certora_reset_pool_scalar_ghost();
    write_controller(&e, controller.clone());
    write_swap_fee(&e, swap_fee);
    put_total_shares(&e, total_shares);
    write_freeze(&e, freeze);

    cvlr_assert!(has_controller(&e));
    cvlr_assert!(read_controller(&e) == controller);
    cvlr_assert!(read_swap_fee(&e) == swap_fee);
    cvlr_assert!(get_total_shares(&e) == total_shares);
    cvlr_assert!(read_freeze(&e) == freeze);
}

/// Updating one modeled scalar field must preserve every other field.
#[rule]
fn phase1_scalar_ghost_fields_are_isolated(e: Env, controller: Address, replacement: Address) {
    certora_reset_pool_scalar_ghost();
    write_controller(&e, controller.clone());
    write_swap_fee(&e, 22);
    put_total_shares(&e, 33);
    write_freeze(&e, true);

    write_swap_fee(&e, 23);
    cvlr_assert!(read_controller(&e) == controller);
    cvlr_assert!(read_swap_fee(&e) == 23);
    cvlr_assert!(get_total_shares(&e) == 33);
    cvlr_assert!(read_freeze(&e));

    put_total_shares(&e, 34);
    cvlr_assert!(read_controller(&e) == controller);
    cvlr_assert!(read_swap_fee(&e) == 23);
    cvlr_assert!(get_total_shares(&e) == 34);
    cvlr_assert!(read_freeze(&e));

    write_freeze(&e, false);
    cvlr_assert!(read_controller(&e) == controller);
    cvlr_assert!(read_swap_fee(&e) == 23);
    cvlr_assert!(get_total_shares(&e) == 34);
    cvlr_assert!(!read_freeze(&e));

    write_controller(&e, replacement.clone());
    cvlr_assert!(read_controller(&e) == replacement);
    cvlr_assert!(read_swap_fee(&e) == 23);
    cvlr_assert!(get_total_shares(&e) == 34);
    cvlr_assert!(!read_freeze(&e));
}

/// The scalar and one-account LP projections must remain independent.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase1_scalar_and_lp_ghosts_are_isolated(e: Env, controller: Address) {
    certora_reset_pool_scalar_ghost();
    certora_reset_balance_ghost();
    write_controller(&e, controller.clone());
    write_swap_fee(&e, 22);
    put_total_shares(&e, 33);
    write_freeze(&e, true);
    certora_watch_balance(controller.clone(), 44);

    put_total_shares(&e, 34);
    cvlr_assert!(read_balance(&e, controller.clone()) == 44);

    certora_write_balance(&e, controller.clone(), 45);
    cvlr_assert!(read_controller(&e) == controller);
    cvlr_assert!(read_swap_fee(&e) == 22);
    cvlr_assert!(get_total_shares(&e) == 34);
    cvlr_assert!(read_freeze(&e));
}

/// Initialization's LP mint primitive must update supply and owner equally.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase1_initial_share_mint_updates_supply_and_owner(e: Env, controller: Address) {
    certora_reset_pool_scalar_ghost();
    certora_reset_balance_ghost();
    put_total_shares(&e, 0);
    certora_watch_balance(controller.clone(), 0);

    mint_shares(&e, &controller, 100);

    cvlr_assert!(get_total_shares(&e) == 100);
    cvlr_assert!(read_balance(&e, controller) == 100);
}

/// Witness a normal return through the combined scalar/LP initialization path.
#[cfg(feature = "certora-lp-balance-ghost")]
#[rule]
fn phase1_scalar_foundation_reachable(e: Env, controller: Address) {
    certora_reset_pool_scalar_ghost();
    certora_reset_balance_ghost();
    write_controller(&e, controller.clone());
    write_swap_fee(&e, 22);
    write_freeze(&e, false);
    put_total_shares(&e, 0);
    certora_watch_balance(controller.clone(), 0);

    mint_shares(&e, &controller, 100);

    cvlr_satisfy!(
        has_controller(&e)
            && read_controller(&e) == controller.clone()
            && read_swap_fee(&e) == 22
            && !read_freeze(&e)
            && get_total_shares(&e) == 100
            && read_balance(&e, controller) == 100
    );
}
