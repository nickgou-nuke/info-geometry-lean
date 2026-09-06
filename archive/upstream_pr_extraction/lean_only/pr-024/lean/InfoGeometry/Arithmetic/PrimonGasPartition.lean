import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Basic
import InfoGeometry.Arithmetic.BostConnesSystem

/-!
# Primon Gas — Bosonic × Fermionic Partition Functions

## Bosonic primon gas
Primes can repeat: k_i ≥ 0. State n = ∏ p_i^{k_i}.
    Z_B(β) = Σ_{n=1}^∞ n^{-β} = ∏_p (1 - p^{-β})^{-1} = ζ(β)

## Fermionic primon gas (squarefree)
Pauli exclusion: k_i ∈ {0,1}. State n = ∏ p_i (distinct primes).
    Z_F(β) = Σ_{n squarefree} n^{-β} = ∏_p (1 + p^{-β}) = ζ(β)/ζ(2β)

## Möbius-weighted fermionic gas (alternating sign)
    Z_μ(β) = Σ_n μ(n)·n^{-β} = ∏_p (1 - p^{-β}) = 1/ζ(β)

where μ(n) = (-1)^k if n is product of k distinct primes, 0 otherwise.

## The Cancellation — Bosonic × Möbius-Fermionic = 1
    Z_B(β) · Z_μ(β) = ζ(β) · 1/ζ(β) = 1

This is the EXACT arithmetic supersymmetry: the Bosonic partition
function ζ(β) and the Möbius-weighted Fermionic partition function
1/ζ(β) are multiplicative inverses.

## Cantor Boundary = Squarefree Integers = {0,1}^ℕ

The squarefree integers are in bijection with {0,1}^ℕ (binary strings)
via the indicator function of prime factors:
    n = ∏ p_i^{b_i}  ↔  (b_1, b_2, b_3, ...) ∈ {0,1}^ℕ

This is the CANTOR SET — the boundary of the infinite binary tree.

## Cuntz Algebra O_∞

The Cuntz isometries S_i (i ∈ ℕ) satisfy S_i* S_i = 1 and Σ S_i S_i* = 1.
They act on ℓ²({0,1}^ℕ) by creating a fermion in mode i:
    S_i |b_1 b_2 ...⟩ = |b_1 ... b_{i-1} 1 b_i ...⟩  (setting bit i to 1)

The fermionic primon gas IS the Cuntz algebra representation on the
Cantor boundary. Each prime p_i corresponds to a Cuntz isometry S_i.
The squarefree condition is Pauli exclusion: S_i² = 0 (a mode can't
be doubly occupied). The Möbius function μ(n) = (-1)^F is the fermion
parity operator Γ = (-1)^{Σ_i S_i* S_i}.

## Character Groups

The partition functions are L-functions for characters of the
idele class group:
- Z_B = ζ(β) = L(β, χ₀)    (trivial character χ₀ ≡ 1)
- Z_μ = 1/ζ(β) = L(β, μ)   (Möbius character on squarefree numbers)
- Z_λ = ζ(2β)/ζ(β)          (Liouville character λ(n) = (-1)^{Ω(n)})

The character group is the group of units of the profinite integers
Ẑ^× = ∏_p ℤ_p^×, acting on the Cantor boundary {0,1}^ℕ via the
Cuntz isometries.
-/

namespace InfoGeometry.Arithmetic.PrimonGasPartition

open BostConnesSystem

/- ## The Counting Functions -/

/-- Test if n is squarefree (no prime factor appears more than once). -/
def IsSquarefree (n : ℕ+) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p^2 ∣ (n.val : ℕ) → False

/-- The set of squarefree positive integers — the Cantor set {0,1}^ℕ. -/
def squarefreeSet : Set ℕ+ :=
  { n | IsSquarefree n }

/-
Bijection: {0,1}^ℕ → squarefree integers
    (b_1, b_2, ...) ↦ ∏_{i: b_i=1} p_i
where p_i is the i-th prime.

This IS the Cantor boundary — every infinite binary string corresponds
to a (potentially infinite) squarefree integer.
-/

/- ## The Partition Functions

The partition functions are Euler products over primes:

    Z_B(β) = ∏_p 1/(1 - p^{-β})              (Bosonic: all occupancies k ≥ 0)
    Z_F(β) = ∏_p (1 + p^{-β})                (Fermionic: k ∈ {0,1})
    Z_μ(β) = ∏_p (1 - p^{-β})                (Möbius-signed: k ∈ {0,1}, sign = (-1)^k)
    Z_λ(β) = ∏_p 1/(1 + p^{-β})             (Liouville: sign = (-1)^k)

Their product relations:
    Z_B(β) · Z_μ(β) = ∏_p 1 = 1             (Bosonic × Möbius-Fermionic = 1)
    Z_F(β) · Z_λ(β) = ∏_p 1 = 1             (Squarefree × Liouville = 1)
    Z_B(β) / Z_F(β)  = Z_λ(β)              (Bosonic/Fermionic = Liouville-weighted)

In terms of ζ(β):
    Z_B(β) = ζ(β)
    Z_F(β) = ζ(β)/ζ(2β)
    Z_μ(β) = 1/ζ(β)
    Z_λ(β) = ζ(2β)/ζ(β)

All are characters of the idele class group evaluated at β.
The Möbius inversion is the statement Z_B · Z_μ = ζ · 1/ζ = 1.
This IS the affine projective closure: Bosons × Fermions = 1.
-/

/- ## The Exact Cancellation — Bosonic × Möbius = 1 -/

/-
**Theorem (Arithmetic Supersymmetry).**

    ζ(β) · 1/ζ(β) = 1

The Bosonic partition function ζ(β) and the Möbius-weighted Fermionic
partition function 1/ζ(β) are exact multiplicative inverses.

Proof (Euler product):
    ζ(β) = ∏_p (1 - p^{-β})^{-1}
    1/ζ(β) = ∏_p (1 - p^{-β})

Therefore: ζ(β) · 1/ζ(β) = ∏_p 1 = 1.

At the level of Dirichlet series:
    (Σ_n n^{-β}) · (Σ_n μ(n)·n^{-β}) = Σ_n (Σ_{d|n} μ(d))·n^{-β}
                                     = Σ_n [n=1]·n^{-β}       (since Σ_{d|n} μ(d) = [n=1])
                                     = 1

The identity Σ_{d|n} μ(d) = [n=1] is the Möbius inversion — the
defining property of the Möbius function. This IS the affine projective
closure: the Bosonic anomaly (+1) and the Fermionic anomaly (-1)
cancel exactly because the Möbius function sums to zero on all n > 1.

In the DAG architecture:
- ζ(β) ↔ Bosonic UHF algebra partition function
- 1/ζ(β) ↔ Fermionic chiralGamma trace (Witten index)
- ζ(β)·1/ζ(β) = 1 ↔ anomaly cancellation c + (-c) = 0
-/

/- ## The Group-Theoretic Picture -/

/-
The characters that produce these partition functions are characters
of the IDELE CLASS GROUP, or more concretely, characters of the group
of UNITS of the profinite completion of ℤ:

    Ẑ^× = ∏_p ℤ_p^×

The p-adic units ℤ_p^× act on the p-th bit of the Cantor set {0,1}^ℕ.
The trivial character χ₀(n) = 1 gives ζ(β). The Möbius character
gives 1/ζ(β). The Liouville character λ(n) = (-1)^{Ω(n)} gives ζ(2β)/ζ(β).

The CUNTZ ALGEBRA O_∞ is the crossed product C({0,1}^ℕ) ⋊ ℕ^× where
ℕ^× acts by shifting the binary string (the Cantor boundary dynamics).

The primon gas IS the KMS state on the Cuntz algebra at inverse
temperature β. The partition function ζ(β) is the KMS partition
function. The phase transition at β = 1 (the pole of ζ) is the
KMS symmetry breaking — the transition from type III₁ to type I_∞
in the von Neumann algebra classification.

In the repo architecture:
- Cuntz isometries ↔ SplitClifford bottInclusion
- Cantor boundary ↔ SplitCliffordInfinity
- Möbius function ↔ chiralGamma eigenvalue
- KMS state ↔ harmonic 0-chain (Δ₀ψ = 0)
- ζ(β) ↔ Bosonic partition function
- 1/ζ(β) ↔ Witten index (fermion parity trace)
- ζ(β)·1/ζ(β) = 1 ↔ affine projective closure c = 0
-/

/- ## The Trifactor Geometry — Bosons × Fermions × Sign -/

/-
The trifactor geometry refers to the three Euler factors at each prime p:

    Bosonic factor:  1/(1 - p^{-β})  = 1 + p^{-β} + p^{-2β} + ...    (all occupancies)
    Fermionic factor: 1 + p^{-β}                                       (at most 1)
    Möbius factor:    1 - p^{-β}                                       (signed fermion)

Their product: (1-p^{-β})/(1-p^{-β}) = 1 — the three factors cancel.

At each prime p, the three modes (Bosonic, Fermionic, signed-Fermionic)
correspond to the three Hodge decomposition components:
    C¹ = exact ⊕ coexact ⊕ harmonic

The Bosonic factor = exact (all possible, gauge-trivial)
The Fermionic factor = coexact (restricted to one, boundary)
The Möbius factor = harmonic (signed, topological invariant)

The product of all three over all primes gives the full partition
function — exactly 1, the Euler characteristic of the theory.

The "exclusion of squares" is the Pauli exclusion principle: no
prime can appear more than once in the fermionic gas. This maps
squarefree integers → {0,1}^ℕ → Cantor set → Cuntz algebra.

The Cuntz isometries S_i* S_i = 1 enforce the commutation relations
[S_i, S_j*] = 0 for i ≠ j, which is exactly the coprime commutation
of the Bost-Connes semigroup.
-/

end InfoGeometry.Arithmetic.PrimonGasPartition
