# Signature


For POD2 signatures, we use [Schnorr](https://en.wikipedia.org/wiki/Schnorr_signature) signature over the [EcGFp5 curve](https://eprint.iacr.org/2022/274), with Poseidon as the hash function.

The message is a single backend `Value`.  To sign a dictionary, the signer signs its Merkle root; the frontend `SignedDict` bundles a `Dictionary`, the signer's public key and the signature.  A `SignedBy(msg, pk)` [statement](./statements.md) is proved in a MainPOD by verifying the signature in-circuit.

Let $G$ be the generator of the curve group, of order $n$, and let $H$ be the Poseidon hash, whose output is interpreted as an integer.

### keygen()
secret key: $sk \xleftarrow{R} \mathbb{Z}_n$<br>
public key: $pk := -sk \cdot G$<br>
return $(sk, pk)$

### sign(sk, m)
$k \xleftarrow{R} \mathbb{Z}_n$<br>
$r := k \cdot G$<br>
$e := H(r_u, m)$<br>
$s := k + sk \cdot e \mod n$<br>
return $(sig:=(s, e))$

### verify(pk, m, sig)
$(s, e) = sig$<br>
$r := s \cdot G + e \cdot pk$<br>
return $H(r_u, m) \stackrel{?}{=} e$

Here $r_u$ is the $u$-coordinate of the point $r$, which uniquely identifies the point in the EcGFp5 group.

## Older version

The previously used signature scheme was proof-based signatures using Plonky2 proofs, following [https://eprint.iacr.org/2024/1553](https://eprint.iacr.org/2024/1553) and [https://jdodinh.io/assets/files/m-thesis.pdf](https://jdodinh.io/assets/files/m-thesis.pdf), where the public key is $pk := H(sk)$ and a signature is a Plonky2 proof of knowledge of $sk$ for the given $pk$ and message.  It was replaced by the elliptic curve Schnorr signature presented above.
