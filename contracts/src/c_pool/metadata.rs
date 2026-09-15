//! Utilities to read and write contract's storage

use crate::c_pool::storage_types::DataKey;
use soroban_sdk::{unwrap::UnwrapOptimized, Address, Env, Map, String, Vec};
use soroban_token_sdk::{metadata::TokenMetadata, TokenUtils};

use super::storage_types::{Record, SHARED_BUMP_AMOUNT, SHARED_LIFETIME_THRESHOLD};

/// Verification-only projection of scalar pool state used by initialization
/// and the operation guards.
///
/// The SDK-25 Sunbeam host model does not preserve storage writes reliably.
/// Keeping these values in WASM ghost state gives the verification build exact
/// accessor semantics without changing the production build. An absent fee or
/// total supply reads as zero, and an absent freeze flag reads as false, just as
/// the production accessors do. An absent controller remains distinguishable
/// because `init` uses its presence as the single-initialization guard.
#[cfg(feature = "certora-pool-scalar-ghost")]
struct CertoraPoolScalarGhost {
    controller: Option<Address>,
    swap_fee: Option<i128>,
    total_shares: Option<i128>,
    freeze: Option<bool>,
}

#[cfg(feature = "certora-pool-scalar-ghost")]
impl CertoraPoolScalarGhost {
    const fn uninitialized() -> Self {
        Self {
            controller: None,
            swap_fee: None,
            total_shares: None,
            freeze: None,
        }
    }
}

#[cfg(feature = "certora-pool-scalar-ghost")]
static mut CERTORA_POOL_SCALAR_GHOST: CertoraPoolScalarGhost =
    CertoraPoolScalarGhost::uninitialized();

/// Reset the verification-only scalar projection to pre-initialization state.
#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub(crate) fn certora_reset_pool_scalar_ghost() {
    unsafe {
        *core::ptr::addr_of_mut!(CERTORA_POOL_SCALAR_GHOST) =
            CertoraPoolScalarGhost::uninitialized();
    }
}

// Read all Token Addresses in the pool
pub fn read_tokens(e: &Env) -> Vec<Address> {
    let key = DataKey::AllTokenVec;
    e.storage()
        .persistent()
        .extend_ttl(&key, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    e.storage()
        .persistent()
        .get::<DataKey, Vec<Address>>(&key)
        .unwrap_optimized()
}

// Write All Tokens Addresses to the Vector
pub fn write_tokens(e: &Env, new: Vec<Address>) {
    let key = DataKey::AllTokenVec;
    e.storage().persistent().set(&key, &new);
    e.storage()
        .persistent()
        .extend_ttl(&key, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
}

// Read Record
pub fn read_record(e: &Env) -> Map<Address, Record> {
    let key_rec = DataKey::AllRecordData;
    e.storage()
        .persistent()
        .extend_ttl(&key_rec, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
    e.storage()
        .persistent()
        .get::<DataKey, Map<Address, Record>>(&key_rec)
        .unwrap_optimized()
}

// Write Record
pub fn write_record(e: &Env, new_map: Map<Address, Record>) {
    let key_rec = DataKey::AllRecordData;
    e.storage().persistent().set(&key_rec, &new_map);
    e.storage()
        .persistent()
        .extend_ttl(&key_rec, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
}

// Read Factory
pub fn read_factory(e: &Env) -> Address {
    let key = DataKey::Factory;
    e.storage()
        .instance()
        .get::<DataKey, Address>(&key)
        .unwrap_optimized()
}

// Write Factory
pub fn write_factory(e: &Env, d: Address) {
    let key = DataKey::Factory;
    e.storage().instance().set(&key, &d)
}

// Read Controller
#[cfg(not(feature = "certora-pool-scalar-ghost"))]
pub fn read_controller(e: &Env) -> Address {
    let key = DataKey::Controller;
    e.storage()
        .instance()
        .get::<DataKey, Address>(&key)
        .unwrap_optimized()
}

#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub fn read_controller(_e: &Env) -> Address {
    unsafe {
        match &(*core::ptr::addr_of!(CERTORA_POOL_SCALAR_GHOST)).controller {
            Some(controller) => controller.clone(),
            None => panic!("controller is not initialized"),
        }
    }
}

// Write Controller
#[cfg(not(feature = "certora-pool-scalar-ghost"))]
pub fn write_controller(e: &Env, d: Address) {
    let key = DataKey::Controller;
    e.storage().instance().set(&key, &d);
}

#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub fn write_controller(_e: &Env, d: Address) {
    unsafe {
        (*core::ptr::addr_of_mut!(CERTORA_POOL_SCALAR_GHOST)).controller = Some(d);
    }
}

/// Whether the controller key is present.
///
/// This keeps the production initialization guard source-shaped while routing
/// only the verification build through scalar ghost state.
#[cfg(not(feature = "certora-pool-scalar-ghost"))]
#[inline(always)]
pub fn has_controller(e: &Env) -> bool {
    e.storage().instance().has(&DataKey::Controller)
}

#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub fn has_controller(_e: &Env) -> bool {
    unsafe {
        (*core::ptr::addr_of!(CERTORA_POOL_SCALAR_GHOST))
            .controller
            .is_some()
    }
}

// Read Swap Fee
#[cfg(not(feature = "certora-pool-scalar-ghost"))]
pub fn read_swap_fee(e: &Env) -> i128 {
    let key = DataKey::SwapFee;
    e.storage()
        .instance()
        .get::<DataKey, i128>(&key)
        .unwrap_or(0)
}

#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub fn read_swap_fee(_e: &Env) -> i128 {
    unsafe {
        (*core::ptr::addr_of!(CERTORA_POOL_SCALAR_GHOST))
            .swap_fee
            .unwrap_or(0)
    }
}

// Write Swap Fee
#[cfg(not(feature = "certora-pool-scalar-ghost"))]
pub fn write_swap_fee(e: &Env, d: i128) {
    let key = DataKey::SwapFee;
    e.storage().instance().set(&key, &d)
}

#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub fn write_swap_fee(_e: &Env, d: i128) {
    unsafe {
        (*core::ptr::addr_of_mut!(CERTORA_POOL_SCALAR_GHOST)).swap_fee = Some(d);
    }
}

// Read Total Shares
#[cfg(not(feature = "certora-pool-scalar-ghost"))]
pub fn get_total_shares(e: &Env) -> i128 {
    let key = DataKey::TotalShares;
    if let Some(supply) = e.storage().persistent().get::<DataKey, i128>(&key) {
        e.storage()
            .persistent()
            .extend_ttl(&key, SHARED_LIFETIME_THRESHOLD, SHARED_BUMP_AMOUNT);
        supply
    } else {
        0
    }
}

#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub fn get_total_shares(_e: &Env) -> i128 {
    unsafe {
        (*core::ptr::addr_of!(CERTORA_POOL_SCALAR_GHOST))
            .total_shares
            .unwrap_or(0)
    }
}

// Update Total Shares
#[cfg(not(feature = "certora-pool-scalar-ghost"))]
pub fn put_total_shares(e: &Env, amount: i128) {
    e.storage().persistent().set(&DataKey::TotalShares, &amount);
    e.storage().persistent().extend_ttl(
        &DataKey::TotalShares,
        SHARED_LIFETIME_THRESHOLD,
        SHARED_BUMP_AMOUNT,
    );
}

#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub fn put_total_shares(_e: &Env, amount: i128) {
    unsafe {
        (*core::ptr::addr_of_mut!(CERTORA_POOL_SCALAR_GHOST)).total_shares = Some(amount);
    }
}

// Read Finalize
pub fn read_finalize(e: &Env) -> bool {
    e.storage()
        .instance()
        .get::<DataKey, bool>(&DataKey::Finalize)
        .unwrap_optimized()
}

// Write Finalize
pub fn write_finalize(e: &Env, val: bool) {
    e.storage().instance().set(&DataKey::Finalize, &val)
}

// Read Public Swap
pub fn read_public_swap(e: &Env) -> bool {
    e.storage()
        .instance()
        .get::<DataKey, bool>(&DataKey::PublicSwap)
        .unwrap_optimized()
}

// Write Public Swap
pub fn write_public_swap(e: &Env, val: bool) {
    e.storage().instance().set(&DataKey::PublicSwap, &val)
}

// Read status of the pool
#[cfg(not(feature = "certora-pool-scalar-ghost"))]
pub fn read_freeze(e: &Env) -> bool {
    let key = DataKey::Freeze;
    e.storage()
        .instance()
        .get::<DataKey, bool>(&key)
        .unwrap_or(false)
}

#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub fn read_freeze(_e: &Env) -> bool {
    unsafe {
        (*core::ptr::addr_of!(CERTORA_POOL_SCALAR_GHOST))
            .freeze
            .unwrap_or(false)
    }
}

// Write status of the pool
#[cfg(not(feature = "certora-pool-scalar-ghost"))]
pub fn write_freeze(e: &Env, d: bool) {
    let key = DataKey::Freeze;
    e.storage().instance().set(&key, &d)
}

#[cfg(feature = "certora-pool-scalar-ghost")]
#[inline(never)]
pub fn write_freeze(_e: &Env, d: bool) {
    unsafe {
        (*core::ptr::addr_of_mut!(CERTORA_POOL_SCALAR_GHOST)).freeze = Some(d);
    }
}

pub fn read_decimal(e: &Env) -> u32 {
    let util = TokenUtils::new(e);
    util.metadata().get_metadata().decimal
}

pub fn read_name(e: &Env) -> String {
    let util = TokenUtils::new(e);
    util.metadata().get_metadata().name
}

pub fn read_symbol(e: &Env) -> String {
    let util = TokenUtils::new(e);
    util.metadata().get_metadata().symbol
}

pub fn write_metadata(e: &Env, metadata: TokenMetadata) {
    let util = TokenUtils::new(e);
    util.metadata().set_metadata(&metadata);
}
