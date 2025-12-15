# Original

degree_bits = 16
free_gates = 1296 (2%)
timed "MainPod::prove": 9.201466328s

```
[2025-12-10T16:54:38Z DEBUG pod2::cache::mem] getting rec_main_pod_verifier_circuit_data from the mem cache
[2025-12-10T16:54:38Z INFO  pod2::cache::mem] building rec_main_pod_verifier_circuit_data and storing to the mem cache
[2025-12-10T16:54:38Z DEBUG pod2::cache::mem] getting rec_main_pod_circuit_data from the mem cache
[2025-12-10T16:54:38Z INFO  pod2::cache::mem] building rec_main_pod_circuit_data and storing to the mem cache
[2025-12-10T16:54:38Z DEBUG pod2::cache::mem] getting standard_rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T16:54:38Z INFO  pod2::cache::mem] building standard_rec_main_pod_common_circuit_data and storing to the mem cache
timed "common_data_for_recursion I::build": 1.023167079s
[2025-12-10T16:54:39Z DEBUG plonky2::plonk::circuit_builder] Degree before blinding & padding: 40110
[2025-12-10T16:54:39Z DEBUG plonky2::plonk::circuit_builder] Degree after blinding & padding: 65536
[2025-12-10T16:54:44Z DEBUG plonky2::plonk::circuit_builder] Building circuit took 5.282049s
timed "common_data_for_recursion builder.build": 5.374253836s
[2025-12-10T16:54:44Z DEBUG pod2::backends::plonky2::recursion::circuit] degree_bits = 16, free_gates = 1296
timed "common_data_for_recursion": 6.564223093s
timed "RecursiveCircuit<I>::build_targets": 1.212922552s
[2025-12-10T16:54:45Z DEBUG plonky2::plonk::circuit_builder] Degree before blinding & padding: 52442
[2025-12-10T16:54:45Z INFO  plonky2::plonk::circuit_builder] Adding 3446 blinding terms for witness polynomials, and 3448*2 for Z polynomi
als
[2025-12-10T16:54:45Z DEBUG plonky2::plonk::circuit_builder] Degree after blinding & padding: 65536
[2025-12-10T16:54:50Z DEBUG plonky2::plonk::circuit_builder] Building circuit took 5.1591444s
timed "RecursiveCircuit<I> build": 5.250955828s
timed "recursive MainPod circuit_data": 13.030159218s
[2025-12-10T16:54:51Z DEBUG pod2::cache::mem] built standard_rec_main_pod_common_circuit_data in 13.24052202s
[2025-12-10T16:54:51Z DEBUG pod2::cache::mem] getting standard_rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T16:54:51Z DEBUG pod2::cache::mem] found standard_rec_main_pod_common_circuit_data in the mem cache
timed "RecursiveCircuit<I>::build_targets": 1.219316233s
[2025-12-10T16:54:52Z DEBUG plonky2::plonk::circuit_builder] Degree before blinding & padding: 52442
[2025-12-10T16:54:52Z INFO  plonky2::plonk::circuit_builder] Adding 3446 blinding terms for witness polynomials, and 3448*2 for Z polynomi
als
[2025-12-10T16:54:52Z DEBUG plonky2::plonk::circuit_builder] Degree after blinding & padding: 65536
[2025-12-10T16:54:57Z DEBUG plonky2::plonk::circuit_builder] Building circuit took 5.249776s
timed "RecursiveCircuit<I> build": 5.342362628s
timed "recursive MainPod circuit_data padded": 6.563720917s
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] built rec_main_pod_circuit_data in 19.804340479s
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] getting rec_main_pod_circuit_data from the mem cache
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] found rec_main_pod_circuit_data in the mem cache
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] built rec_main_pod_verifier_circuit_data in 19.805149844s
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] getting rec_main_pod_verifier_circuit_data from the mem cache
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] found rec_main_pod_verifier_circuit_data in the mem cache
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] getting empty_pod from the mem cache
[2025-12-10T16:54:57Z INFO  pod2::cache::mem] building empty_pod and storing to the mem cache
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] getting standard_empty_pod_circuit_data from the mem cache
[2025-12-10T16:54:57Z INFO  pod2::cache::mem] building standard_empty_pod_circuit_data and storing to the mem cache
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] getting standard_rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T16:54:57Z DEBUG pod2::cache::mem] found standard_rec_main_pod_common_circuit_data in the mem cache
[2025-12-10T16:54:57Z DEBUG plonky2::plonk::circuit_builder] Degree before blinding & padding: 52449
[2025-12-10T16:54:57Z INFO  plonky2::plonk::circuit_builder] Adding 3446 blinding terms for witness polynomials, and 3448*2 for Z polynomi
als
[2025-12-10T16:54:57Z DEBUG plonky2::plonk::circuit_builder] Degree after blinding & padding: 65536
[2025-12-10T16:55:04Z DEBUG plonky2::plonk::circuit_builder] Building circuit took 6.1992974s
timed "EmptyPod build": 6.205766886s
[2025-12-10T16:55:04Z DEBUG pod2::cache::mem] built standard_empty_pod_circuit_data in 6.222396084s
[2025-12-10T16:55:04Z DEBUG pod2::cache::mem] getting standard_empty_pod_circuit_data from the mem cache
[2025-12-10T16:55:04Z DEBUG pod2::cache::mem] found standard_empty_pod_circuit_data in the mem cache
timed "EmptyPod prove": 8.810148517s
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] built empty_pod in 15.032835718s
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] getting empty_pod from the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] found empty_pod in the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] getting rec_main_pod_common_hash from the mem cache
[2025-12-10T16:55:12Z INFO  pod2::cache::mem] building rec_main_pod_common_hash and storing to the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] getting rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T16:55:12Z INFO  pod2::cache::mem] building rec_main_pod_common_circuit_data and storing to the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] getting rec_main_pod_circuit_data from the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] found rec_main_pod_circuit_data in the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] built rec_main_pod_common_circuit_data in 13.365µs
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] getting rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] found rec_main_pod_common_circuit_data in the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] built rec_main_pod_common_hash in 155.203µs
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] getting rec_main_pod_common_hash from the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] found rec_main_pod_common_hash in the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] getting rec_main_pod_circuit_data from the mem cache
[2025-12-10T16:55:12Z DEBUG pod2::cache::mem] found rec_main_pod_circuit_data in the mem cache
timed "MainPod::prove": 9.201466328s
[2025-12-10T16:55:22Z DEBUG pod2::cache::mem] getting rec_main_pod_common_hash from the mem cache
[2025-12-10T16:55:22Z DEBUG pod2::cache::mem] found rec_main_pod_common_hash in the mem cache
[2025-12-10T16:55:22Z DEBUG pod2::cache::mem] getting rec_main_pod_verifier_circuit_data from the mem cache
[2025-12-10T16:55:22Z DEBUG pod2::cache::mem] found rec_main_pod_verifier_circuit_data in the mem cache
```

# Double

```
	max_statements: 48 * 2,
	max_public_statements: 8,
	num_public_statements_hash: 16,
	max_statement_args: 5,
	max_operation_args: 5,
	max_custom_predicate_batches: 4 * 2,
	max_custom_predicate_verifications: 8 * 2,
	max_custom_predicate_arity: 5,
	max_custom_predicate_wildcards: 8 * 2,
	max_custom_batch_size: 4 * 2,
	max_merkle_proofs_containers: 20 * 2,
	max_merkle_tree_state_transition_proofs_containers: 6 * 2,
	max_depth_mt_containers: 32,
	max_depth_mt_vds: 6, // up to 64 (2^6) different pod circuits
	max_public_key_of: 2 * 2,
	max_signed_by: 4 * 2,
```

degree_bits = 17
free_gates = 12041 (9%)
timed "MainPod::prove": 20.614747907s

```
[2025-12-10T17:03:05Z DEBUG pod2::cache::mem] getting rec_main_pod_verifier_circuit_data from the mem cache
[2025-12-10T17:03:05Z INFO  pod2::cache::mem] building rec_main_pod_verifier_circuit_data and storing to the mem cache
[2025-12-10T17:03:05Z DEBUG pod2::cache::mem] getting rec_main_pod_circuit_data from the mem cache
[2025-12-10T17:03:05Z INFO  pod2::cache::mem] building rec_main_pod_circuit_data and storing to the mem cache
[2025-12-10T17:03:05Z DEBUG pod2::cache::mem] getting standard_rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T17:03:05Z INFO  pod2::cache::mem] building standard_rec_main_pod_common_circuit_data and storing to the mem cache
timed "common_data_for_recursion I::build": 2.58019125s
[2025-12-10T17:03:07Z DEBUG plonky2::plonk::circuit_builder] Degree before blinding & padding: 96589
[2025-12-10T17:03:07Z DEBUG plonky2::plonk::circuit_builder] Degree after blinding & padding: 131072
[2025-12-10T17:03:19Z DEBUG plonky2::plonk::circuit_builder] Building circuit took 11.662376s
timed "common_data_for_recursion builder.build": 11.896920299s
[2025-12-10T17:03:19Z DEBUG pod2::backends::plonky2::recursion::circuit] degree_bits = 17, free_gates = 12041
timed "common_data_for_recursion": 14.821398999s
timed "RecursiveCircuit<I>::build_targets": 2.855917211s
[2025-12-10T17:03:23Z DEBUG plonky2::plonk::circuit_builder] Degree before blinding & padding: 120162
[2025-12-10T17:03:23Z INFO  plonky2::plonk::circuit_builder] Adding 3614 blinding terms for witness polynomials, and 3616*2 for Z polynomi
als
[2025-12-10T17:03:23Z DEBUG plonky2::plonk::circuit_builder] Degree after blinding & padding: 131072
[2025-12-10T17:03:34Z DEBUG plonky2::plonk::circuit_builder] Building circuit took 11.511771s
timed "RecursiveCircuit<I> build": 11.733444082s
timed "recursive MainPod circuit_data": 29.41298904s
[2025-12-10T17:03:35Z DEBUG pod2::cache::mem] built standard_rec_main_pod_common_circuit_data in 29.796513627s
[2025-12-10T17:03:35Z DEBUG pod2::cache::mem] getting standard_rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T17:03:35Z DEBUG pod2::cache::mem] found standard_rec_main_pod_common_circuit_data in the mem cache
timed "RecursiveCircuit<I>::build_targets": 2.869011717s
[2025-12-10T17:03:38Z DEBUG plonky2::plonk::circuit_builder] Degree before blinding & padding: 120162
[2025-12-10T17:03:38Z INFO  plonky2::plonk::circuit_builder] Adding 3614 blinding terms for witness polynomials, and 3616*2 for Z polynomi
als
[2025-12-10T17:03:38Z DEBUG plonky2::plonk::circuit_builder] Degree after blinding & padding: 131072
[2025-12-10T17:03:49Z DEBUG plonky2::plonk::circuit_builder] Building circuit took 11.712139s
timed "RecursiveCircuit<I> build": 11.930841837s
timed "recursive MainPod circuit_data padded": 14.801985258s
[2025-12-10T17:03:49Z DEBUG pod2::cache::mem] built rec_main_pod_circuit_data in 44.598735191s
[2025-12-10T17:03:49Z DEBUG pod2::cache::mem] getting rec_main_pod_circuit_data from the mem cache
[2025-12-10T17:03:49Z DEBUG pod2::cache::mem] found rec_main_pod_circuit_data in the mem cache
[2025-12-10T17:03:49Z DEBUG pod2::cache::mem] built rec_main_pod_verifier_circuit_data in 44.599736036s
[2025-12-10T17:03:49Z DEBUG pod2::cache::mem] getting rec_main_pod_verifier_circuit_data from the mem cache
[2025-12-10T17:03:49Z DEBUG pod2::cache::mem] found rec_main_pod_verifier_circuit_data in the mem cache
[2025-12-10T17:03:49Z DEBUG pod2::cache::mem] getting empty_pod from the mem cache
[2025-12-10T17:03:49Z INFO  pod2::cache::mem] building empty_pod and storing to the mem cache
[2025-12-10T17:03:49Z DEBUG pod2::cache::mem] getting standard_empty_pod_circuit_data from the mem cache
[2025-12-10T17:03:49Z INFO  pod2::cache::mem] building standard_empty_pod_circuit_data and storing to the mem cache
[2025-12-10T17:03:50Z DEBUG pod2::cache::mem] getting standard_rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T17:03:50Z DEBUG pod2::cache::mem] found standard_rec_main_pod_common_circuit_data in the mem cache
[2025-12-10T17:03:50Z DEBUG plonky2::plonk::circuit_builder] Degree before blinding & padding: 120169
[2025-12-10T17:03:50Z INFO  plonky2::plonk::circuit_builder] Adding 3614 blinding terms for witness polynomials, and 3616*2 for Z polynomi
als
[2025-12-10T17:03:50Z DEBUG plonky2::plonk::circuit_builder] Degree after blinding & padding: 131072
[2025-12-10T17:04:04Z DEBUG plonky2::plonk::circuit_builder] Building circuit took 14.135221s
timed "EmptyPod build": 14.151183145s
[2025-12-10T17:04:04Z DEBUG pod2::cache::mem] built standard_empty_pod_circuit_data in 14.19692074s
[2025-12-10T17:04:04Z DEBUG pod2::cache::mem] getting standard_empty_pod_circuit_data from the mem cache
[2025-12-10T17:04:04Z DEBUG pod2::cache::mem] found standard_empty_pod_circuit_data in the mem cache
timed "EmptyPod prove": 19.262431543s
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] built empty_pod in 33.459697262s
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] getting empty_pod from the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] found empty_pod in the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] getting rec_main_pod_common_hash from the mem cache
[2025-12-10T17:04:23Z INFO  pod2::cache::mem] building rec_main_pod_common_hash and storing to the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] getting rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T17:04:23Z INFO  pod2::cache::mem] building rec_main_pod_common_circuit_data and storing to the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] getting rec_main_pod_circuit_data from the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] found rec_main_pod_circuit_data in the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] built rec_main_pod_common_circuit_data in 15.019µs
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] getting rec_main_pod_common_circuit_data from the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] found rec_main_pod_common_circuit_data in the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] built rec_main_pod_common_hash in 168.808µs
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] getting rec_main_pod_common_hash from the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] found rec_main_pod_common_hash in the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] getting rec_main_pod_circuit_data from the mem cache
[2025-12-10T17:04:23Z DEBUG pod2::cache::mem] found rec_main_pod_circuit_data in the mem cache
timed "MainPod::prove": 20.614747907s
[2025-12-10T17:04:44Z DEBUG pod2::cache::mem] getting rec_main_pod_common_hash from the mem cache
[2025-12-10T17:04:44Z DEBUG pod2::cache::mem] found rec_main_pod_common_hash in the mem cache
[2025-12-10T17:04:44Z DEBUG pod2::cache::mem] getting rec_main_pod_verifier_circuit_data from the mem cache
[2025-12-10T17:04:44Z DEBUG pod2::cache::mem] found rec_main_pod_verifier_circuit_data in the mem cache
```
