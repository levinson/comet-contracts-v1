#![cfg(test)]
extern crate std;
use soroban_sdk::Env;
use soroban_sdk::I256;

use crate::c_consts::BONE;
use crate::c_num::c_pow;

#[test]
#[should_panic = "Error(Contract, #34)"]
fn test_c_pow_low() {
    let env: Env = Env::default();
    c_pow(
        &env,
        &I256::from_i32(&env, 0),
        &I256::from_i32(&env, 2),
        false,
    );
}

#[test]
#[should_panic = "Error(Contract, #35)"]
fn test_c_pow_high() {
    let env: Env = Env::default();
    c_pow(
        &env,
        &I256::from_i128(&env, 2 * BONE),
        &I256::from_i32(&env, 2),
        false,
    );
}

#[test]
fn test_c_pow_integer_rounding_direction() {
    let env = Env::default();
    let base = I256::from_i128(&env, BONE + 1);
    let exp = I256::from_i128(&env, 2 * BONE);

    assert_eq!(c_pow(&env, &base, &exp, false).to_i128().unwrap(), BONE + 2);
    assert_eq!(c_pow(&env, &base, &exp, true).to_i128().unwrap(), BONE + 3);
}

#[test]
fn test_c_pow_first_term_convergence_rounds_toward_bound() {
    let env = Env::default();
    let quarter = I256::from_i128(&env, BONE / 4);

    // ceiling: series gives exactly BONE (term floors to 0) - one unit too low
    let base = I256::from_i128(&env, BONE + 1);
    assert_eq!(
        c_pow(&env, &base, &quarter, true).to_i128().unwrap(),
        BONE + 1
    );
    assert_eq!(c_pow(&env, &base, &quarter, false).to_i128().unwrap(), BONE);

    // floor: series gives BONE - 1e8 exactly - one unit too high
    let base = I256::from_i128(&env, BONE - 400_000_000);
    assert_eq!(
        c_pow(&env, &base, &quarter, false).to_i128().unwrap(),
        BONE - 100_000_001
    );
    // ceiling of the same input is BONE - 1e8; the nudge makes it a valid (1-unit loose) bound
    assert_eq!(
        c_pow(&env, &base, &quarter, true).to_i128().unwrap(),
        BONE - 100_000_000 + 1
    );

    let base = I256::from_i128(&env, BONE + 2);
    let exp = I256::from_i128(&env, 4 * BONE / 5);
    assert_eq!(c_pow(&env, &base, &exp, false).to_i128().unwrap(), BONE);
}

#[test]
fn test_c_pow_base_one_is_exact() {
    let env = Env::default();
    let base = I256::from_i128(&env, BONE);
    let exp = I256::from_i128(&env, BONE * 5 / 4);

    assert_eq!(c_pow(&env, &base, &exp, true).to_i128().unwrap(), BONE);
    assert_eq!(c_pow(&env, &base, &exp, false).to_i128().unwrap(), BONE);

    // and the neighbouring ratio BONE - 1 must stay at or below BONE when rounding up
    let base = I256::from_i128(&env, BONE - 1);
    assert_eq!(c_pow(&env, &base, &exp, true).to_i128().unwrap(), BONE - 1);
}
