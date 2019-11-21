// use blake2_rfc::blake2b::Blake2b;
use blake2b_simd;

use crate::babyjubjub::{JubjubEngine, ToUniform};

pub fn hash_to_scalar<E: JubjubEngine>(persona: &[u8], a: &[u8], b: &[u8]) -> E::Fs {
    let mut hasher = blake2b_simd::Params::new().hash_length(32).personal(persona).to_state();
    // let mut hasher = Blake2b::with_params(64, &[], &[], persona);
    hasher.update(a);
    hasher.update(b);
    let ret = *hasher.finalize().as_array();
    // let ret = hasher.finalize();
    E::Fs::to_uniform(ret.as_ref())
}
