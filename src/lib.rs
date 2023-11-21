use ipa_multipoint::{multiproof::MultiPoint, lagrange_basis::LagrangeBasis};
use ark_ff::fields::PrimeField;
use ipa_multipoint::crs::CRS;
use banderwagon::multi_scalar_mul;
use ark_serialize::CanonicalSerialize;
use ipa_multipoint::lagrange_basis::PrecomputedWeights;
use ipa_multipoint::transcript::Transcript;
use ipa_multipoint::multiproof::ProverQuery;
use ipa_multipoint::multiproof::VerifierQuery;
use banderwagon::Fr;
use banderwagon::Element;
use ipa_multipoint::multiproof::MultiPointProof;

const PEDERSEN_SEED: &[u8] = b"eth_verkle_oct_2021";

/// Pedersen hash receives an address and a trie index and returns a hash calculated this way:
/// H(constant || address_low || address_high || trie_index_low || trie_index_high)
/// where constant = 2 + 256*64
/// address_low = lower 16 bytes of the address
/// address_high = higher 16 bytes of the address
/// trie_index_low = lower 16 bytes of the trie index
/// trie_index_high = higher 16 bytes of the trie index
/// The result is a 256 bit hash
/// Specs: https://notes.ethereum.org/@vbuterin/verkle_tree_eip
fn exposed_pedersen_hash(input: [u8;64]) -> [u8;32] {
    let mut address32 = [0u8; 32];

    address32.copy_from_slice(&input[0..32]);

    let mut trie_index= [0u8; 32];

    trie_index.copy_from_slice(&input[32..64]);
    trie_index.reverse(); // reverse for little endian per specs


    let mut scalars: Vec<Fr> = Vec::new();
    scalars.push(Fr::from(16386));
    scalars.push(Fr::from_le_bytes_mod_order(&address32[0..16]));
    scalars.push(Fr::from_le_bytes_mod_order(&address32[16..32]));
    scalars.push(Fr::from_le_bytes_mod_order(&trie_index[0..16]));
    scalars.push(Fr::from_le_bytes_mod_order(&trie_index[16..32]));

    let bases = CRS::new(5, PEDERSEN_SEED);
    let commit = multi_scalar_mul(&bases.G, &scalars);
    let mut result = commit.to_bytes();
    result.reverse();
    result
}

/// Expects up to 256 32-be-bytes Banderwagon elements - simply numbers in the field.
/// Returns group_to_field(commitment) - a Fr element serialized to 32-be-bytes.
fn exposed_pedersen_commit_to_fr(input: Vec<u8>) -> [u8;32] {
        // Input should be a multiple of 32-be-bytes.
        let inp = input.as_slice();

        let len = input.len();
        if len % 32 != 0 {
            panic!("Invalid input length. Should be a multiple of 32-bytes."); // Return null pointer to indicate an error
        }    
        let n_scalars = len / 32;
        if n_scalars > 256 {
            panic!("Invalid input length. Should be at most 256 elements of 32-bytes.");
        }    

        // Each 32-be-bytes are interpreted as field elements.
        let mut scalars: Vec<Fr> = Vec::with_capacity(n_scalars);
        for b in inp.chunks(32) {
            scalars.push(Fr::from_be_bytes_mod_order(b));
        }

        // Committing all values at once.
        let bases = CRS::new(n_scalars, PEDERSEN_SEED);
        let commit = multi_scalar_mul(&bases.G, &scalars);

        // Serializing via x/y in projective coordinates, to int and to scalars.
        let scalar = group_to_field(&commit);
        let mut scalar_bytes = [0u8; 32];
        scalar.serialize(&mut scalar_bytes[..]).expect("could not serialise Fr into a 32 byte array");
        scalar_bytes.reverse();
    
        scalar_bytes
}

fn exposed_update_commitment(input: [u8; 65]) -> [u8; 32]{
    let mut commitment = [0u8; 32];
    commitment.copy_from_slice(&input[0..32]);

    let mut new_value_minus_old = [0u8; 32];
    new_value_minus_old.copy_from_slice(&input[32..64]);

    let mut index = 0u8;
    index.copy_from_slice(&input[64..65]).unwrap();
    let index_s = index[0];

    let mut new_minus_old_ser = Fr::from_be_bytes_mod_order(&new_value_minus_old);
    let bases = CRS::new(256, PEDERSEN_SEED);

    let mut commitment_ser = Element::new();
    commitment_ser.push(Element::from_bytes(&commitment));

    let mut new_commitment = commitment_ser + new_value_minus_old*bases[index_s];

    let mut result = new_commitment.to_bytes();
    result.reverse();
    result
}

/// Similar to exposed_pedersen_commit_to_fr, but returns just a commitment seriazlied as bytes.
fn exposed_pedersen_commit_to_element(input: Vec<u8>) -> [u8;32] {
        // Input should be a multiple of 32-be-bytes.
        let inp = input.as_slice();

        let len = input.len();
        if len % 32 != 0 {
            panic!("Invalid input length. Should be a multiple of 32-bytes.");
        }    
        let n_scalars = len / 32;
        if n_scalars > 256 {
            panic!("Invalid input length. Should be at most 256 elements of 32-bytes.");
        }    
    
        // Each 32-be-bytes are interpreted as field elements.
        let mut scalars: Vec<Fr> = Vec::with_capacity(n_scalars);
        for b in inp.chunks(32) {
            scalars.push(Fr::from_be_bytes_mod_order(b));
        }
        
        // Committing all values at once.
        let bases = CRS::new(n_scalars, PEDERSEN_SEED);
        let commit = multi_scalar_mul(&bases.G, &scalars);
        let commit_bytes = commit.to_bytes();
        commit_bytes
}

/// In case we need to expose the group_to_field function.
fn exposed_group_to_field(input: [u8;32]) -> [u8;32] {
    let mut bytes = [0u8; 32];
    let point = Element::from_bytes(&input).unwrap();
    let base_field = point.map_to_field();
    base_field
        .serialize(&mut bytes[..])
        .expect("could not serialise point into a 32 byte array");
    bytes
}

/// Receives a tuple (C_i, f_i(X), z_i, y_i)
/// Where C_i is a commitment to f_i(X) serialized as 32 bytes
/// f_i(X) is the polynomial serialized as 8192 bytes since we have 256 Fr elements each serialized as 32 bytes
/// z_i is index of the point in the polynomial: 1 byte (number from 1 to 256)
/// y_i is the evaluation of the polynomial at z_i i.e value we are opening: 32 bytes
/// Returns a proof serialized as bytes
fn exposed_prove_call(input: Vec<u8>) -> Vec<u8> {
    // Define the chunk size (8257 bytes)
    // C_i, f_i(X), z_i, y_i
    // 32, 8192, 1, 32 
    // = 8257
    let chunk_size = 8257;
    // Create an iterator over the input Vec<u8>
    let chunked_data = input.chunks(chunk_size);

    let mut prover_queries: Vec<ProverQuery> = Vec::new();


    for (_i, chunk) in chunked_data.enumerate() {
        if chunk.len() >= chunk_size {
            let data = chunk.clone();
            let commitment = Element::from_bytes(&data[0..32]).unwrap();

            // Create f_x from the next 8192 bytes
            let f_i_x: Vec<u8> = chunk[32..8224].to_vec();

            let chunked_f_i_x_data = f_i_x.chunks(32);

            let mut collect_lagrange_basis: Vec<Fr> = Vec::new();
            for (_j, chunk_f_i_x) in chunked_f_i_x_data.enumerate() {
                if chunk_f_i_x.len() >= 32 {
                    let data_f_i_x = chunk_f_i_x.clone();
                    let fr_data_f_i_x = Fr::from_be_bytes_mod_order(&data_f_i_x);
                    collect_lagrange_basis.push(fr_data_f_i_x);
                }
            }

            let lagrange_basis = LagrangeBasis::new(collect_lagrange_basis);


            let z_i: usize = chunk[8224] as usize;

            let y_i = Fr::from_be_bytes_mod_order(&chunk[8225..8257]);

            let prover_query = ProverQuery {
                commitment,
                poly: lagrange_basis,
                point: z_i,
                result: y_i,
            };
            prover_queries.push(prover_query);
        }
    }
    let precomp = PrecomputedWeights::new(256);


    let crs = CRS::new(256, PEDERSEN_SEED);
    let mut transcript = Transcript::new(b"verkle");

    let proof = MultiPoint::open(
        crs.clone(),
        &precomp,
        &mut transcript,
        prover_queries,
    );
    proof.to_bytes().unwrap()
}


fn exposed_verify_call(input: Vec<u8>) -> bool {
    // Define the chunk size 32+1+32 = 65 bytes for C_i, z_i, y_i
    let chunk_size = 65;
    // Create an iterator over the input Vec<u8>
    let chunked_data = input.chunks(chunk_size);


    let mut verifier_queries: Vec<VerifierQuery> = Vec::new();

    for (_i, chunk) in chunked_data.enumerate() {
        let c_i = Element::from_bytes(&chunk[0..32]).unwrap();


        let z_i: Fr = Fr::from(chunk[32] as u128);

        let y_i = Fr::from_be_bytes_mod_order(&chunk[33..65]);

        let verifier_query = VerifierQuery {
            commitment: c_i,
            point: z_i,
            result: y_i,
        };

        verifier_queries.push(verifier_query);
    }

    let precomp = PrecomputedWeights::new(256);


    let crs = CRS::new(256, PEDERSEN_SEED);
    let mut transcript = Transcript::new(b"verkle");


    //TODO: process proof bytes
    let proof_bytes = [0u8; 256];

    let proof = MultiPointProof::from_bytes(&proof_bytes, 256).unwrap();

    let result = proof.check(&crs, &precomp, &verifier_queries,&mut transcript);
    result
}


// Helper for group_to_field
pub(crate)fn group_to_field(point: &Element) -> Fr {
    let base_field = point.map_to_field();
    let mut bytes = [0u8; 32];
    base_field
        .serialize(&mut bytes[..])
        .expect("could not serialise point into a 32 byte array");
    Fr::from_le_bytes_mod_order(&bytes)
}


#[test]
fn test_exposed_pedersen_hash() {
    let input = [167, 193, 134, 127, 101, 201, 125, 133, 93, 73, 253, 222, 238, 22, 188, 227, 193, 221, 183, 73, 85, 116, 113, 10, 172, 220, 152, 93, 7, 18, 133, 50, 176, 18, 222, 120, 221, 51, 160, 163, 54, 161, 15, 203, 174, 234, 12, 223, 129, 48, 85, 67, 27, 204, 93, 224, 124, 148, 116, 102, 156, 30, 114, 234];

    let result = exposed_pedersen_hash(input);

    let expected = [0, 36, 192, 4, 159, 203, 95, 99, 186, 161, 2, 23, 116, 186, 110, 246, 122, 87, 32, 211, 218, 235, 31, 41, 158, 1, 37, 224, 151, 187, 39, 31];
    assert_eq!(result, expected);
}

#[test]
fn test_exposed_pedersen_commit_to_fr() {
    let input: [u8; 32] = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1];

    let result = exposed_pedersen_commit_to_fr(input.to_vec());

    let bases = CRS::new(1, PEDERSEN_SEED);

    let first = bases.G.first().unwrap();

    let scalar = group_to_field(&first);
    let mut scalar_bytes = [0u8; 32];
    scalar.serialize(&mut scalar_bytes[..]).expect("could not serialise Fr into a 32 byte array");
    scalar_bytes.reverse();
    assert_eq!(result, scalar_bytes);
}
