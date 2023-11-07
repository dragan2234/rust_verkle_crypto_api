use bandersnatch::fr;
use verkle_spec::*;
use verkle_trie::*;
use ipa_multipoint::{*, multiproof::MultiPoint, lagrange_basis::LagrangeBasis};
use std::*;
use ark_ff::fields::PrimeField;
use ipa_multipoint::crs::CRS;
use banderwagon::multi_scalar_mul;
use ark_serialize::CanonicalSerialize;
use ipa_multipoint::lagrange_basis::PrecomputedWeights;
use ipa_multipoint::transcript::Transcript;
use std::time::{Instant, Duration};
use ipa_multipoint::multiproof::ProverQuery;
use ipa_multipoint::multiproof::VerifierQuery;

const PEDERSEN_SEED: &[u8] = b"eth_verkle_oct_2021";

fn exposed_pedersen_hash(input: [u8;64]) -> [u8;32] {
    let mut address32 = [0u8; 32];

    address32.copy_from_slice(&input[0..32]);

    let mut trie_index= [0u8; 32];

    trie_index.copy_from_slice(&input[32..64]);
    trie_index.reverse(); // reverse for little endian per specs

    let base_hash = hash_addr_int(&address32, &trie_index);

    let result = base_hash.as_fixed_bytes();
    *result
}

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


fn exposed_pedersen_commit_to_element(input: Vec<u8>) -> [u8;32] {
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
        let commit_bytes = commit.to_bytes();
        commit_bytes
}

fn exposed_group_to_field(input: [u8;32]) -> [u8;32] {
    let mut bytes = [0u8; 32];
    let point = Element::from_bytes(&input).unwrap();
    let base_field = point.map_to_field();
    base_field
        .serialize(&mut bytes[..])
        .expect("could not serialise point into a 32 byte array");
    bytes
}

fn exposed_prove_call(input: Vec<u8>) -> Vec<u8> {
    // Define the chunk size (8257 bytes)
    // C_i, f_i(X), z_i, y_i
    // 32, 8192, 1, 32 
    // = 8257
    let chunk_size = 8257;
    // Create an iterator over the input Vec<u8>
    let chunked_data = input.chunks(chunk_size);

    let mut prover_queries: Vec<ProverQuery> = Vec::new();



    for (i, chunk) in chunked_data.enumerate() {
        if chunk.len() >= chunk_size {
            let data = chunk.clone();
            let commitment = Element::from_bytes(&data[0..32]).unwrap();
    
            // Create f_x from the next 8192 bytes
            let f_i_x: Vec<u8> = chunk[32..8224].to_vec();

            let chunked_f_i_x_data = f_i_x.chunks(32);

            let mut collect_lagrange_basis: Vec<Fr> = Vec::new();
            for (j, chunk_f_i_x) in chunked_f_i_x_data.enumerate() {
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

    for (i, chunk) in chunked_data.enumerate() {
        let C_i = Element::from_bytes(&chunk[0..32]).unwrap();


        let z_i: Fr = Fr::from(chunk[32] as u128);

        let y_i = Fr::from_be_bytes_mod_order(&chunk[33..65]);

        let verifier_query = VerifierQuery {
            commitment: C_i,
            point: z_i,
            result: y_i,
        };

        verifier_queries.push(verifier_query);
    }

    // TODO: make verifier struct, expose multiproof.check call

    true
}



// Helper function to hash an address and an integer taken from rust-verkle/verkle-specs.
pub(crate) fn hash_addr_int(addr: &[u8; 32], integer: &[u8; 32]) -> H256 {

    let address_bytes = addr;

    let integer_bytes = integer;
    let mut hash_input = [0u8; 64];
    let (first_half, second_half) = hash_input.split_at_mut(32);

    // Copy address and index into slice, then hash it
    first_half.copy_from_slice(address_bytes);
    second_half.copy_from_slice(integer_bytes);

    hash64(hash_input)
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
    let mut input = [167, 193, 134, 127, 101, 201, 125, 133, 93, 73, 253, 222, 238, 22, 188, 227, 193, 221, 183, 73, 85, 116, 113, 10, 172, 220, 152, 93, 7, 18, 133, 50, 176, 18, 222, 120, 221, 51, 160, 163, 54, 161, 15, 203, 174, 234, 12, 223, 129, 48, 85, 67, 27, 204, 93, 224, 124, 148, 116, 102, 156, 30, 114, 234];


    let start = Instant::now();
    let result = exposed_pedersen_hash(input);
    let elapsed = start.elapsed();
    println!("Time elapsed: {:?}", elapsed);


    let expected = [0, 36, 192, 4, 159, 203, 95, 99, 186, 161, 2, 23, 116, 186, 110, 246, 122, 87, 32, 211, 218, 235, 31, 41, 158, 1, 37, 224, 151, 187, 39, 31];
    assert_eq!(result, expected);
}

#[test]
fn test_exposed_pedersen_commit_to_fr() {
    let input: [u8; 32] = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1];

    let start = Instant::now();
    let result = exposed_pedersen_commit_to_fr(input.to_vec());

    let bases = CRS::new(1, PEDERSEN_SEED);

    let first = bases.G.first().unwrap();

    let scalar = group_to_field(&first);
    let mut scalar_bytes = [0u8; 32];
    scalar.serialize(&mut scalar_bytes[..]).expect("could not serialise Fr into a 32 byte array");
    scalar_bytes.reverse();
    let elapsed = start.elapsed();
    println!("Time elapsed: {:?}", elapsed);
    assert_eq!(result, scalar_bytes);
}
