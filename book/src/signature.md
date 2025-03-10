# Signature


Current signature scheme used is proof-based signatures using Plonky2 proofs, following [https://eprint.iacr.org/2024/1553](https://eprint.iacr.org/2024/1553) and [https://jdodinh.io/assets/files/m-thesis.pdf](https://jdodinh.io/assets/files/m-thesis.pdf). This comes from [Polygon Miden's RPO STARK-based](https://github.com/0xPolygonMiden/crypto/blob/d2a67396053fded90ec72690404c8c7728b98e4e/src/dsa/rpo_stark/signature/mod.rs#L129) signatures.

In future iterations we may replace it by other signature schemes (either elliptic curve based scheme on a Golilocks-prime friendly curve, or a lattice based scheme).



### generate_params()
$pp$: plonky2 circuit prover params<br>
$vp$: plonky2 circuit verifier params<br>
return $(pp, vp)$

### keygen()
secret key: $sk \xleftarrow{R} \mathbb{F}^4$<br>
public key: $pk := H(sk)$ [^1]<br>
return $(sk, pk)$

### sign(pp, sk, m)
$pk := H(sk)$<br>
$s := H(pk, m)$<br>
$\pi = plonky2.Prove(pp, sk, pk, m, s)$<br>
return $(sig:=\pi)$

### verify(vp, sig, pk, m)
$\pi = sig$<br>
$s := H(pk, m)$<br>
return $plonky2.Verify(vp, \pi, pk, m, s)$


### Plonky2 circuit
private inputs: $(sk)$<br>
public inputs: $(pk, m, s)$<br>
$pk \stackrel{!}{=} H(sk)$<br>
$s \stackrel{!}{=} H(pk, m)$


<br><br>

[^1]: The [2024/1553 paper](https://eprint.iacr.org/2024/1553) uses $pk:=H(sk||0^4)$ to have as input (to the hash) 8 field elements, to be able to reuse the same instance of the RPO hash as the one they use later in the signature (where it hashes 8 field elements).
