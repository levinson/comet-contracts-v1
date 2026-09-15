use crate::c_pool::error::Error;
#[cfg(not(feature = "certora-lp-balance-ghost"))]
use crate::c_pool::storage_types::{DataKeyToken, BALANCE_BUMP_AMOUNT};
#[cfg(feature = "certora-lp-balance-ghost")]
use cvlr_nondet::nondet;
use soroban_sdk::{assert_with_error, Address, Env};

#[cfg(not(feature = "certora-lp-balance-ghost"))]
use super::storage_types::BALANCE_LIFETIME_THRESHOLD;

#[cfg(not(feature = "certora-lp-balance-ghost"))]
pub fn read_balance(e: &Env, addr: Address) -> i128 {
    let key = DataKeyToken::Balance(addr);
    if let Some(balance) = e.storage().persistent().get::<DataKeyToken, i128>(&key) {
        e.storage()
            .persistent()
            .extend_ttl(&key, BALANCE_LIFETIME_THRESHOLD, BALANCE_BUMP_AMOUNT);
        balance
    } else {
        0
    }
}

#[cfg(not(feature = "certora-lp-balance-ghost"))]
fn write_balance(e: &Env, addr: Address, amount: i128) {
    let key = DataKeyToken::Balance(addr);
    e.storage().persistent().set(&key, &amount);
    e.storage()
        .persistent()
        .extend_ttl(&key, BALANCE_LIFETIME_THRESHOLD, BALANCE_BUMP_AMOUNT);
}

/// Verification-only projection of the LP balance map onto one watched owner.
///
/// Sunbeam's SDK-25 model cannot currently round-trip the production
/// `DataKeyToken::Balance(Address)` key. Keeping the watched key and value in
/// WASM ghost state avoids that unsupported host-storage path. Reads of every
/// other owner are deliberately nondeterministic, so the projection does not
/// assume those balances are zero. Rules using this model must initialize the
/// owner they observe with `certora_watch_balance`.
#[cfg(feature = "certora-lp-balance-ghost")]
enum CertoraLpBalanceGhost {
    Uninitialized,
    Watching { owner: Address, balance: i128 },
}

#[cfg(feature = "certora-lp-balance-ghost")]
static mut CERTORA_LP_BALANCE_GHOST: CertoraLpBalanceGhost = CertoraLpBalanceGhost::Uninitialized;

#[cfg(feature = "certora-lp-balance-ghost")]
#[inline(never)]
pub fn read_balance(_e: &Env, addr: Address) -> i128 {
    unsafe {
        match &*core::ptr::addr_of!(CERTORA_LP_BALANCE_GHOST) {
            CertoraLpBalanceGhost::Watching { owner, balance } if owner == &addr => *balance,
            _ => nondet(),
        }
    }
}

#[cfg(feature = "certora-lp-balance-ghost")]
#[inline(never)]
fn write_balance(_e: &Env, addr: Address, amount: i128) {
    unsafe {
        if let CertoraLpBalanceGhost::Watching { owner, balance } =
            &mut *core::ptr::addr_of_mut!(CERTORA_LP_BALANCE_GHOST)
        {
            if owner == &addr {
                *balance = amount;
            }
        }
    }
}

/// Select and seed the sole LP owner observed by a verification rule.
#[cfg(feature = "certora-lp-balance-ghost")]
#[inline(never)]
pub(crate) fn certora_watch_balance(owner: Address, balance: i128) {
    unsafe {
        CERTORA_LP_BALANCE_GHOST = CertoraLpBalanceGhost::Watching { owner, balance };
    }
}

/// Return the verification-only balance projection to its uninitialized state.
#[cfg(feature = "certora-lp-balance-ghost")]
#[inline(never)]
pub(crate) fn certora_reset_balance_ghost() {
    unsafe {
        CERTORA_LP_BALANCE_GHOST = CertoraLpBalanceGhost::Uninitialized;
    }
}

/// Exercise the same projected write used by the production balance helpers.
#[cfg(feature = "certora-lp-balance-ghost")]
#[inline(never)]
pub(crate) fn certora_write_balance(e: &Env, addr: Address, amount: i128) {
    write_balance(e, addr, amount);
}

pub fn receive_balance(e: &Env, addr: Address, amount: i128) {
    let balance = read_balance(e, addr.clone());
    write_balance(e, addr, balance + amount);
}

pub fn spend_balance(e: &Env, addr: Address, amount: i128) {
    let balance = read_balance(e, addr.clone());
    assert_with_error!(e, balance >= amount, Error::ErrInsufficientBalance);
    write_balance(e, addr, balance - amount);
}
