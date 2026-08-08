# Digest — misra.pdf

Source: `/home/goutev/Desktop/symmetry/par/misra.pdf`

## Bibliographic note

- Title: *Entropy and Prime Number Distribution; (a Non-heuristic Approach)*
- Author: Alec Misra
- Date in PDF: February 6, 2006

## Core proposal

The paper proposes an entropy-style reading of prime number distribution by
combining Boltzmann/Shannon logarithmic entropy with the Prime Number Theorem:

```text
S^ = log x
π(x) ≈ x / log x
therefore S^ ≈ x / π(x)
```

It then interprets

```text
E(x) = x / π(x)
```

as a dimensionless entropy of the integer continuum.

The paper also adopts a nonstandard convention counting `1` as a prime-like/base
entropy unit, giving `π₁(1)=1` and therefore `E₁(1)=1`.  With this convention:

```text
π₁(10)=5, π₁(11)=6, π₁(12)=6, π₁(13)=7, π₁(14)=7
E₁(10)=2, E₁(11)=11/6, E₁(12)=2, E₁(13)=13/7, E₁(14)=2
```

The finite decrease from `E₁(10)` to `E₁(11)` is called an “entropy reversal”.

## Theorem-honesty audit

The finite counting arithmetic is formalizable and has been proved in Lean.

The large claims are **not** accepted as proofs:

- “entropy proves RH” is socketed;
- “entropy proves P ≠ NP” is socketed and should not be treated as a valid proof;
- “entropy proves infinitely many twin primes” is socketed and should not be treated as a valid proof;
- treating `1` as prime is represented as a named convention `MisraPrimeLike`, not a replacement for `Nat.Prime`.

The theorem-honest bridge is:

```text
finite prime-like counting convention + exact rational entropy examples
+ explicit sockets for PNT/RH/P-vs-NP/twin-prime claims.
```

## Formal artifacts

- Lean: `proofs/MisraPrimeEntropyDigest.lean`
- SymPy witness: `proofs/misra_prime_entropy_digest.py`
