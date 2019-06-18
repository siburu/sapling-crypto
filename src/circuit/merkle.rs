use crate::bellman::pairing::Engine;
use crate::bellman::{ConstraintSystem, SynthesisError};
use crate::circuit::boolean::Boolean;
use crate::jubjub::{JubjubEngine, JubjubParams};
use crate::circuit::num::AllocatedNum;
use crate::circuit::pedersen_hash;

pub trait MerkleTree<E: Engine> {
    const BRANCHING_FACTOR: usize;

    type Hash;

    // hashes a bit representation of the leaf
    fn hash_leaf<CS: ConstraintSystem<E>>(&self, cs: CS, leaf: &[Boolean]) -> Result<Self::Hash, SynthesisError>;

    // hashes a node with
    fn hash_node<CS: ConstraintSystem<E>>(&self, cs: CS, children: &[Self::Hash], level: usize) -> Result<Self::Hash, SynthesisError>;

    // checks inclusion of the leaf into the root
    fn check_inclusion<CS: ConstraintSystem<E>>(&self, cs: CS, leaf: &[Boolean], path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError>;
    
    // checks inclusion of the leaf into the root
    fn check_inclusion_for_root<CS: ConstraintSystem<E>>(&self, cs: CS, root: &Self::Hash, leaf: &[Boolean], path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError>;
    
    // checks inclusion of the leaf hash into the root
    fn check_hash_inclusion<CS: ConstraintSystem<E>>(&self, cs: CS, hash: &Self::Hash, path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError>;
    
    // checks inclusion of the leaf hash into the root
    fn check_hash_inclusion_for_root<CS: ConstraintSystem<E>>(&self, cs: CS, root: &Self::Hash, hash: &Self::Hash, path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError>;

    fn update<CS: ConstraintSystem<E>>(&mut self, cs: CS, leaf: &[Boolean], path: &[Boolean], witness: &[Self::Hash]) -> Result<Self::Hash, SynthesisError>;
    fn update_from_hash<CS: ConstraintSystem<E>>(&mut self, cs: CS, hash: &Self::Hash, path: &[Boolean], witness: &[Self::Hash]) -> Result<Self::Hash, SynthesisError>;

    // fn update_intersect(&mut self, cs: CS, leafs: (&[Boolean], &[Boolean]), paths: (&[Boolean], &[Boolean]), witnesses: (&[Self::Hash], &[Self::Hash])) -> Result<Self::Hash, SynthesisError>;
    // fn update_from_hash_intersect(&mut self, cs: CS, leafs: (&[Self::Hash], &[Self::Hash]), paths: (&[Boolean], &[Boolean]), witnesses: (&[Self::Hash], &[Self::Hash])) -> Result<Self::Hash, SynthesisError>;
}


pub struct PedersenHashTree<'a, E: JubjubEngine> {
    root: AllocatedNum<E>,
    height: usize,
    params: &'a E::Params
}

impl<'a, E: JubjubEngine> MerkleTree<E> for PedersenHashTree<'a, E> {
    const BRANCHING_FACTOR: usize = 2;

    type Hash = AllocatedNum<E>;

    fn hash_leaf<CS: ConstraintSystem<E>>(&self, mut cs: CS, leaf: &[Boolean]) -> Result<Self::Hash, SynthesisError> {
        let leaf_hash = pedersen_hash::pedersen_hash(
            cs.namespace(|| "hash leaf content"),
            pedersen_hash::Personalization::NoteCommitment,
            &leaf,
            self.params
        )?.get_x().clone();

        Ok(leaf_hash)
    }

    fn hash_node<CS: ConstraintSystem<E>>(&self, mut cs: CS, children: &[Self::Hash], level: usize) -> Result<Self::Hash, SynthesisError> {
        if children.len() != Self::BRANCHING_FACTOR {
            return Err(SynthesisError::Unsatisfiable);
        }

        let cs = &mut cs.namespace(|| format!("merkle tree hash {}", level));

        let mut preimage = vec![];
        preimage.extend(children[0].into_bits_le(cs.namespace(|| "left childred into bits"))?);
        preimage.extend(children[1].into_bits_le(cs.namespace(|| "right chinlder into bits"))?);

        let node_hash = pedersen_hash::pedersen_hash(
            cs.namespace(|| "computation of pedersen hash"),
            pedersen_hash::Personalization::MerkleTree(level),
            &preimage,
            self.params
        )?.get_x().clone();

        Ok(node_hash)
    }

    // checks inclusion of the leaf into the root
    fn check_inclusion<CS: ConstraintSystem<E>>(&self, mut cs: CS, leaf: &[Boolean], path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError> {
        let leaf_hash = self.hash_leaf(
            cs.namespace(|| "leaf hash calculation"), 
            leaf
        )?;

        self.check_hash_inclusion(cs, &leaf_hash, path, witness)
    }

    // checks inclusion of the leaf into the root
    fn check_inclusion_for_root<CS: ConstraintSystem<E>>(&self, mut cs: CS, root: &Self::Hash, leaf: &[Boolean], path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError> {
        let leaf_hash = self.hash_leaf(
            cs.namespace(|| "leaf hash calculation"), 
            leaf
        )?;

        self.check_hash_inclusion_for_root(cs, root, &leaf_hash, path, witness)
    }
    

    // checks inclusion of the leaf hash into the root
    fn check_hash_inclusion<CS: ConstraintSystem<E>>(&self, cs: CS, hash: &Self::Hash, path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError> {
        self.check_hash_inclusion_for_root(cs, &self.root, hash, path, witness)
    }
    
    // checks inclusion of the leaf hash into the root
    fn check_hash_inclusion_for_root<CS: ConstraintSystem<E>>(
        &self, 
        mut cs: CS, 
        root: &Self::Hash,
        hash: &Self::Hash, 
        path: &[Boolean], 
        witness: &[Self::Hash]
    ) -> Result<Boolean, SynthesisError> {
        if self.height != witness.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        
        // This is an injective encoding, as cur is a
        // point in the prime order subgroup.
        let mut cur = hash.clone();

        // Ascend the merkle tree authentication path
        for (i, direction_bit) in path.clone().into_iter()
                                        .enumerate() {
            let cs = &mut cs.namespace(|| format!("merkle tree hash {}", i));

            // "direction_bit" determines if the current subtree
            // is the "right" leaf at this depth of the tree.

            // Witness the authentication path element adjacent
            // at this depth.
            let path_element = &witness[i];

            // Swap the two if the current subtree is on the right
            let (xl, xr) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of preimage"),
                &cur,
                path_element,
                &direction_bit
            )?;

            cur = self.hash_node(
                cs.namespace(|| "node hash computation"), 
                &[xl, xr], 
                i
            )?;
        }

        let included = AllocatedNum::equals(
            cs.namespace(|| "compare roots"), 
            &cur, 
            &root
        )?;

        Ok(included)
    }


    fn update<CS: ConstraintSystem<E>>(&mut self, mut cs: CS, leaf: &[Boolean], path: &[Boolean], witness: &[Self::Hash]) -> Result<Self::Hash, SynthesisError> {
        let leaf_hash = self.hash_leaf(
            cs.namespace(|| "leaf hash calculation"), 
            leaf
        )?;

        self.update_from_hash(cs, &leaf_hash, path, witness)
    }

    fn update_from_hash<CS: ConstraintSystem<E>>(&mut self, mut cs: CS, hash: &Self::Hash, path: &[Boolean], witness: &[Self::Hash]) -> Result<Self::Hash, SynthesisError> {
        if self.height != witness.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        
        // This is an injective encoding, as cur is a
        // point in the prime order subgroup.
        let mut cur = hash.clone();

        // Ascend the merkle tree authentication path
        for (i, direction_bit) in path.clone().into_iter()
                                        .enumerate() {
            let cs = &mut cs.namespace(|| format!("merkle tree hash {}", i));

            // "direction_bit" determines if the current subtree
            // is the "right" leaf at this depth of the tree.

            // Witness the authentication path element adjacent
            // at this depth.
            let path_element = &witness[i];

            // Swap the two if the current subtree is on the right
            let (xl, xr) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of preimage"),
                &cur,
                path_element,
                &direction_bit
            )?;

            cur = self.hash_node(
                cs.namespace(|| "node hash computation"), 
                &[xl, xr], 
                i
            )?;
        }

        Ok(cur)
    }


    
    

}