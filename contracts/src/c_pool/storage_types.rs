//! Declaration of the Storage Keys
use soroban_sdk::{contracttype, Address};

#[cfg(feature = "certora-storage-symbols")]
use soroban_sdk::{symbol_short, ConversionError, Env, Symbol, TryFromVal, Val};

pub(crate) const DAY_IN_LEDGERS: u32 = 17280;

pub(crate) const SHARED_BUMP_AMOUNT: u32 = 31 * DAY_IN_LEDGERS;
pub(crate) const SHARED_LIFETIME_THRESHOLD: u32 = SHARED_BUMP_AMOUNT - DAY_IN_LEDGERS;

pub(crate) const BALANCE_BUMP_AMOUNT: u32 = 120 * DAY_IN_LEDGERS;
pub(crate) const BALANCE_LIFETIME_THRESHOLD: u32 = BALANCE_BUMP_AMOUNT - 20 * DAY_IN_LEDGERS;

// Token Details Struct
#[contracttype]
#[derive(Clone, Default, Debug, Eq, PartialEq)]
pub struct Record {
    pub balance: i128,
    pub weight: i128,
    pub scalar: i128,
    pub index: u32,
}

// Data Keys for Pool' Storage Data
#[derive(Clone)]
#[cfg_attr(not(feature = "certora-storage-symbols"), contracttype)]
pub enum DataKey {
    Factory,       // Address of the Factory Contract
    Controller,    // Address of the Controller Account
    SwapFee,       // i128
    AllTokenVec,   // Vec<Address>
    AllRecordData, // Map<Address, Record>
    TokenShare,    // Address
    TotalShares,   // i128
    PublicSwap,    // bool
    Finalize,      // bool
    Freeze,        // bool
}

#[cfg(feature = "certora-storage-symbols")]
impl DataKey {
    /// Verification-only injective encoding for the pool's no-payload keys.
    ///
    /// SDK-25 Sunbeam does not currently preserve lookup identity for the
    /// production `#[contracttype]` enum vectors. Short symbols are immediate
    /// values in the verifier model, so independently encoded equal keys remain
    /// equal. This conditional abstraction is not the production serialization.
    pub(crate) fn certora_storage_symbol(&self) -> Symbol {
        match self {
            Self::Factory => symbol_short!("factory"),
            Self::Controller => symbol_short!("ctrl"),
            Self::SwapFee => symbol_short!("swap_fee"),
            Self::AllTokenVec => symbol_short!("tokens"),
            Self::AllRecordData => symbol_short!("records"),
            Self::TokenShare => symbol_short!("tok_shr"),
            Self::TotalShares => symbol_short!("tot_shr"),
            Self::PublicSwap => symbol_short!("pub_swap"),
            Self::Finalize => symbol_short!("finalize"),
            Self::Freeze => symbol_short!("freeze"),
        }
    }
}

#[cfg(feature = "certora-storage-symbols")]
impl TryFromVal<Env, DataKey> for Val {
    type Error = ConversionError;

    fn try_from_val(env: &Env, key: &DataKey) -> Result<Self, Self::Error> {
        let symbol = key.certora_storage_symbol();
        Self::try_from_val(env, &symbol)
    }
}

#[cfg(feature = "certora-storage-symbols")]
impl TryFromVal<Env, &DataKey> for Val {
    type Error = ConversionError;

    fn try_from_val(env: &Env, key: &&DataKey) -> Result<Self, Self::Error> {
        Self::try_from_val(env, *key)
    }
}

// Data Keys for the LP Token
#[derive(Clone)]
#[contracttype]
pub enum DataKeyToken {
    Allowance(AllowanceDataKey),
    Balance(Address),
    Nonce(Address),
    State(Address),
    Admin,
}

#[derive(Clone)]
#[contracttype]
pub struct AllowanceDataKey {
    pub from: Address,
    pub spender: Address,
}

#[contracttype]
pub struct AllowanceValue {
    pub amount: i128,
    pub expiration_ledger: u32,
}
