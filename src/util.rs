// use blake2_rfc::blake2b::Blake2b;
// use blake2_rfc::blake2s::Blake2s;
use blake2b_simd;
use blake2s_simd;
use sha2::{Sha256, Digest};

use crate::jubjub::{JubjubEngine, ToUniform};

pub fn hash_to_scalar<E: JubjubEngine>(persona: &[u8], a: &[u8], b: &[u8]) -> E::Fs {
    let mut hasher = blake2b_simd::Params::new().hash_length(64).personal(persona).to_state();
    // let mut hasher = Blake2b::with_params(64, &[], &[], persona);
    hasher.update(a);
    hasher.update(b);
    let ret = *hasher.finalize().as_array();
    E::Fs::to_uniform(&ret)
}

pub fn hash_to_scalar_s<E: JubjubEngine>(persona: &[u8], a: &[u8], b: &[u8]) -> E::Fs {
    let mut hasher = blake2s_simd::Params::new().hash_length(32).personal(persona).to_state();
    // let mut hasher = Blake2s::with_params(32, &[], &[], persona);
    hasher.update(a);
    hasher.update(b);
    let ret = *hasher.finalize().as_array();
    E::Fs::to_uniform_32(&ret)
}

pub fn sha256_hash_to_scalar<E: JubjubEngine>(persona: &[u8], a: &[u8], b: &[u8]) -> E::Fs {
    let mut hasher = Sha256::new();
    hasher.input(persona);
    hasher.input(a);
    hasher.input(b);
    let result = hasher.result();
    E::Fs::to_uniform_32(result.as_slice())
}