<h1> DEPRECATED </h1>
Rust-verkle cryptography API inspired by https://hackmd.io/@6iQDuIePQjyYBqDChYw_jg/H1xXvMatq


Every method expects raw bytes and return raw bytes so it can be used in FFI calls.

Exposes 4 methods enough for computing root_hash of the trie and tested against https://github.com/ethereum/go-verkle. It doesn't use proper multi_scalar_mul call so it's not yet performant enough - optimizations are needed:

- exposed_pedersen_hash
- exposed_pedersen_commit_to_fr
- exposed_pedersen_commit_to_element
- exposed_group_to_field


Exposes 2 more methods for generating the proof and verifying:
- exposed_prove_call
- exposed_verify_call

And 1 method for updating the commitment
- exposed_update_commitment
  
These are still in progress
