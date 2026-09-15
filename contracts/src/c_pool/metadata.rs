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

/// Verification-only, value-level pool collection state.
///
/// Soroban object handles, arrays, and symbolic indexing are deliberately
/// excluded: all three are unreliable in the pinned SDK-25 verifier model.
/// Eight explicit slots cover the contract's complete supported token domain.
#[cfg(feature = "certora-pool-collections-ghost")]
const CERTORA_POOL_COLLECTION_CAPACITY: u32 = 8;

#[cfg(feature = "certora-pool-collections-ghost")]
const _: () = assert!(crate::c_consts::MAX_BOUND_TOKENS == CERTORA_POOL_COLLECTION_CAPACITY);

#[cfg(feature = "certora-pool-collections-ghost")]
struct CertoraPoolCollectionsGhost {
    tokens_initialized: bool,
    token_len: u32,
    token_0: Option<Address>,
    token_1: Option<Address>,
    token_2: Option<Address>,
    token_3: Option<Address>,
    token_4: Option<Address>,
    token_5: Option<Address>,
    token_6: Option<Address>,
    token_7: Option<Address>,
    records_initialized: bool,
    record_len: u32,
    record_key_0: Option<Address>,
    record_key_1: Option<Address>,
    record_key_2: Option<Address>,
    record_key_3: Option<Address>,
    record_key_4: Option<Address>,
    record_key_5: Option<Address>,
    record_key_6: Option<Address>,
    record_key_7: Option<Address>,
    record_value_0: Option<Record>,
    record_value_1: Option<Record>,
    record_value_2: Option<Record>,
    record_value_3: Option<Record>,
    record_value_4: Option<Record>,
    record_value_5: Option<Record>,
    record_value_6: Option<Record>,
    record_value_7: Option<Record>,
}

#[cfg(feature = "certora-pool-collections-ghost")]
impl CertoraPoolCollectionsGhost {
    const fn uninitialized() -> Self {
        Self {
            tokens_initialized: false,
            token_len: 0,
            token_0: None,
            token_1: None,
            token_2: None,
            token_3: None,
            token_4: None,
            token_5: None,
            token_6: None,
            token_7: None,
            records_initialized: false,
            record_len: 0,
            record_key_0: None,
            record_key_1: None,
            record_key_2: None,
            record_key_3: None,
            record_key_4: None,
            record_key_5: None,
            record_key_6: None,
            record_key_7: None,
            record_value_0: None,
            record_value_1: None,
            record_value_2: None,
            record_value_3: None,
            record_value_4: None,
            record_value_5: None,
            record_value_6: None,
            record_value_7: None,
        }
    }
}

#[cfg(feature = "certora-pool-collections-ghost")]
static mut CERTORA_POOL_COLLECTIONS_GHOST: CertoraPoolCollectionsGhost =
    CertoraPoolCollectionsGhost::uninitialized();

/// Zero-sized source adapter for the verification-only token vector.
#[cfg(feature = "certora-pool-collections-ghost")]
#[derive(Clone, Copy)]
pub(crate) struct CertoraPoolTokenVec;

#[cfg(feature = "certora-pool-collections-ghost")]
impl CertoraPoolTokenVec {
    pub(crate) fn new() -> Self {
        unsafe {
            let state = &mut *core::ptr::addr_of_mut!(CERTORA_POOL_COLLECTIONS_GHOST);
            state.tokens_initialized = true;
            state.token_len = 0;
            state.token_0 = None;
            state.token_1 = None;
            state.token_2 = None;
            state.token_3 = None;
            state.token_4 = None;
            state.token_5 = None;
            state.token_6 = None;
            state.token_7 = None;
        }
        Self
    }

    pub(crate) fn len(&self) -> u32 {
        unsafe { (*core::ptr::addr_of!(CERTORA_POOL_COLLECTIONS_GHOST)).token_len }
    }

    pub(crate) fn push_back(&mut self, value: Address) {
        unsafe {
            let state = &mut *core::ptr::addr_of_mut!(CERTORA_POOL_COLLECTIONS_GHOST);
            match state.token_len {
                0 => state.token_0 = Some(value),
                1 => state.token_1 = Some(value),
                2 => state.token_2 = Some(value),
                3 => state.token_3 = Some(value),
                4 => state.token_4 = Some(value),
                5 => state.token_5 = Some(value),
                6 => state.token_6 = Some(value),
                7 => state.token_7 = Some(value),
                _ => panic!("pool token ghost capacity exceeded"),
            }
            state.token_len += 1;
        }
    }

    pub(crate) fn get(&self, index: u32) -> Option<Address> {
        unsafe {
            let state = &*core::ptr::addr_of!(CERTORA_POOL_COLLECTIONS_GHOST);
            if index >= state.token_len {
                return None;
            }
            match index {
                0 => state.token_0.clone(),
                1 => state.token_1.clone(),
                2 => state.token_2.clone(),
                3 => state.token_3.clone(),
                4 => state.token_4.clone(),
                5 => state.token_5.clone(),
                6 => state.token_6.clone(),
                7 => state.token_7.clone(),
                _ => None,
            }
        }
    }

    pub(crate) fn get_unchecked(&self, index: u32) -> Address {
        match self.get(index) {
            Some(value) => value,
            None => panic!("pool token ghost index is out of bounds"),
        }
    }
}

/// Zero-sized source adapter for the verification-only record map.
///
/// `set` updates the value-level ghost immediately and the corresponding
/// `write` adapter is a no-op. This is equivalent for successful operations;
/// failed-call rollback remains outside the current verifier's claimed scope.
#[cfg(feature = "certora-pool-collections-ghost")]
#[derive(Clone, Copy)]
pub(crate) struct CertoraPoolRecordMap;

#[cfg(feature = "certora-pool-collections-ghost")]
impl CertoraPoolRecordMap {
    pub(crate) fn new() -> Self {
        unsafe {
            let state = &mut *core::ptr::addr_of_mut!(CERTORA_POOL_COLLECTIONS_GHOST);
            state.records_initialized = true;
            state.record_len = 0;
            state.record_key_0 = None;
            state.record_key_1 = None;
            state.record_key_2 = None;
            state.record_key_3 = None;
            state.record_key_4 = None;
            state.record_key_5 = None;
            state.record_key_6 = None;
            state.record_key_7 = None;
            state.record_value_0 = None;
            state.record_value_1 = None;
            state.record_value_2 = None;
            state.record_value_3 = None;
            state.record_value_4 = None;
            state.record_value_5 = None;
            state.record_value_6 = None;
            state.record_value_7 = None;
        }
        Self
    }

    pub(crate) fn len(&self) -> u32 {
        unsafe { (*core::ptr::addr_of!(CERTORA_POOL_COLLECTIONS_GHOST)).record_len }
    }

    pub(crate) fn contains_key(&self, key: Address) -> bool {
        self.get(key).is_some()
    }

    pub(crate) fn get(&self, key: Address) -> Option<Record> {
        unsafe {
            let state = &*core::ptr::addr_of!(CERTORA_POOL_COLLECTIONS_GHOST);
            macro_rules! return_if_matches {
                ($key_slot:ident, $value_slot:ident) => {
                    if let Some(candidate) = &state.$key_slot {
                        if candidate == &key {
                            return state.$value_slot.clone();
                        }
                    }
                };
            }
            return_if_matches!(record_key_0, record_value_0);
            return_if_matches!(record_key_1, record_value_1);
            return_if_matches!(record_key_2, record_value_2);
            return_if_matches!(record_key_3, record_value_3);
            return_if_matches!(record_key_4, record_value_4);
            return_if_matches!(record_key_5, record_value_5);
            return_if_matches!(record_key_6, record_value_6);
            return_if_matches!(record_key_7, record_value_7);
            None
        }
    }

    pub(crate) fn get_unchecked(&self, key: Address) -> Record {
        match self.get(key) {
            Some(value) => value,
            None => panic!("pool record ghost key is not bound"),
        }
    }

    pub(crate) fn set(&mut self, key: Address, value: Record) {
        unsafe {
            let state = &mut *core::ptr::addr_of_mut!(CERTORA_POOL_COLLECTIONS_GHOST);
            macro_rules! replace_if_matches {
                ($key_slot:ident, $value_slot:ident) => {
                    if let Some(candidate) = &state.$key_slot {
                        if candidate == &key {
                            state.$value_slot = Some(value);
                            return;
                        }
                    }
                };
            }
            replace_if_matches!(record_key_0, record_value_0);
            replace_if_matches!(record_key_1, record_value_1);
            replace_if_matches!(record_key_2, record_value_2);
            replace_if_matches!(record_key_3, record_value_3);
            replace_if_matches!(record_key_4, record_value_4);
            replace_if_matches!(record_key_5, record_value_5);
            replace_if_matches!(record_key_6, record_value_6);
            replace_if_matches!(record_key_7, record_value_7);

            match state.record_len {
                0 => {
                    state.record_key_0 = Some(key);
                    state.record_value_0 = Some(value);
                }
                1 => {
                    state.record_key_1 = Some(key);
                    state.record_value_1 = Some(value);
                }
                2 => {
                    state.record_key_2 = Some(key);
                    state.record_value_2 = Some(value);
                }
                3 => {
                    state.record_key_3 = Some(key);
                    state.record_value_3 = Some(value);
                }
                4 => {
                    state.record_key_4 = Some(key);
                    state.record_value_4 = Some(value);
                }
                5 => {
                    state.record_key_5 = Some(key);
                    state.record_value_5 = Some(value);
                }
                6 => {
                    state.record_key_6 = Some(key);
                    state.record_value_6 = Some(value);
                }
                7 => {
                    state.record_key_7 = Some(key);
                    state.record_value_7 = Some(value);
                }
                _ => panic!("pool record ghost capacity exceeded"),
            }
            state.record_len += 1;
        }
    }
}

/// Reset the verification-only collection projection to pre-initialization
/// state.
#[cfg(feature = "certora-pool-collections-ghost")]
#[inline(never)]
pub(crate) fn certora_reset_pool_collections_ghost() {
    unsafe {
        *core::ptr::addr_of_mut!(CERTORA_POOL_COLLECTIONS_GHOST) =
            CertoraPoolCollectionsGhost::uninitialized();
    }
}

#[cfg(feature = "certora-pool-collections-ghost")]
#[inline(never)]
pub(crate) fn certora_read_pool_tokens(_e: &Env) -> CertoraPoolTokenVec {
    unsafe {
        if !(*core::ptr::addr_of!(CERTORA_POOL_COLLECTIONS_GHOST)).tokens_initialized {
            panic!("pool token ghost is not initialized");
        }
    }
    CertoraPoolTokenVec
}

#[cfg(feature = "certora-pool-collections-ghost")]
#[inline(never)]
pub(crate) fn certora_write_pool_tokens(_e: &Env, _tokens: CertoraPoolTokenVec) {}

#[cfg(feature = "certora-pool-collections-ghost")]
#[inline(never)]
pub(crate) fn certora_read_pool_records(_e: &Env) -> CertoraPoolRecordMap {
    unsafe {
        if !(*core::ptr::addr_of!(CERTORA_POOL_COLLECTIONS_GHOST)).records_initialized {
            panic!("pool record ghost is not initialized");
        }
    }
    CertoraPoolRecordMap
}

#[cfg(feature = "certora-pool-collections-ghost")]
#[inline(never)]
pub(crate) fn certora_write_pool_records(_e: &Env, _records: CertoraPoolRecordMap) {}

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
