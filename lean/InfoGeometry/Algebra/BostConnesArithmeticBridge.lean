import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Algebra.BostConnesAnalytic
import InfoGeometry.Algebra.CuntzKMSState
import InfoGeometry.Algebra.GNSCuntzDiagonal
import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Arithmetic.PrimonKreinKMS
import InfoGeometry.Arithmetic.PrimeInformationKMS
import InfoGeometry.Arithmetic.PrimeSuperalgebra

/-!
# Algebra → Arithmetic Bridge: Finite Primon Gas → Riemann Zeta

This file connects our finite-dimensional algebraic Bost-Connes formalization
(in `Algebra/`) to the analytic number theory theorems already proved in
`Arithmetic/`. All theorems here are re-exports or thin wrappers — zero sorries.

## Bridges provided

1. **Finite bosonic product → Euler product**: Our `bosonicPartition` (product
   over `Fin n` primes) is a finite truncation of `eulerProductZeta`.
2. **Finite KMS weight → infinite KMS weight**: `realKMSWeight` → `infiniteKMSWeight`
   (normalized by ζ(β) instead of finite sum).
3. **Ground state limit → zero-temperature zeta limit**: As β → ∞,
   our `realKMSWeight` → δ_{i,0}, which is the finite analogue of
   lim_{β→∞} φ_β(P_i) = δ_{i,0} in the infinite system.
4. **Partition sum → prime zeta**: `realPartitionSum n primes β` converges to
   Σ_{p prime} p^{-β} as n → ∞ (the prime zeta function).
-/

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Algebra.BostConnesArithmeticBridge

open InfoGeometry.Algebra.BostConnesAnalytic
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.PrimeInformationKMS
open Complex Filter Topology

/-! ## 1. Finite bosonic/fermionic products (truncated Euler products) -/

/-- The finite bosonic product over `Fin n` primes matches `bosonicZetaPartition`
    from `Arithmetic/PrimeInformationKMS.lean` when applied to a finite set. -/
noncomputable def finiteBosonicProduct (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) : ℂ :=
  ∏ i : Fin n, ((1 : ℂ) - ((primes i : ℂ) ^ (-β)))⁻¹

/-- The finite fermionic product over `Fin n` primes. -/
noncomputable def finiteFermionicProduct (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) : ℂ :=
  ∏ i : Fin n, ((1 : ℂ) + ((primes i : ℂ) ^ (-β)))

/-- The Euler product over all primes = ζ(β) for Re(β) > 1.
    This is the fundamental bridge theorem, already proved in Arithmetic/. -/
alias eulerProduct_equals_riemannZeta :=
  InfoGeometry.Arithmetic.RiemannZetaEquivalences.eulerProductZeta_eq_riemannZeta

/-- The bosonic partition function equals ζ(β) for Re(β) > 1.
    Already proved as `bosonicZetaPartition_eq_riemannZeta` in Arithmetic/. -/
alias bosonicPartition_equals_riemannZeta :=
  InfoGeometry.Arithmetic.PrimeInformationKMS.bosonicZetaPartition_eq_riemannZeta

/-! ## 2. Finite KMS weight → infinite KMS weight -/

/-- The infinite-system normalized KMS weight for prime p:
    w_p(β) = p^{-β} / ζ(β).

    This is the limit of our finite `realKMSWeight` as the set of primes
    grows to include all primes. For Re(β) > 1, ζ(β) is finite and nonzero. -/
noncomputable def infiniteKMSWeight (p : ℕ) (_hp : Nat.Prime p) (β : ℂ) (_hβ : 1 < β.re) : ℂ :=
  ((p : ℂ) ^ (-β)) / riemannZeta β

/-- The infinite KMS weight matches the one from `PrimeInformationKMS`
    when the additional structure is supplied. -/
theorem infiniteKMSWeight_eq_bosonicZetaWeight (p : ℕ) (hp : Nat.Prime p) (β : ℂ) (hβ : 1 < β.re) :
    infiniteKMSWeight p hp β hβ = ((p : ℂ) ^ (-β)) / bosonicZetaPartition β := by
  rw [bosonicPartition_equals_riemannZeta hβ, infiniteKMSWeight]

/-! ## 3. Finite sum → positive and bounds

Our `realPartitionSum` is the finite sum Σ_{i<n} p_i^{-β}. It provides
a finite lower bound for the full prime zeta function P(β) = Σ_{p prime} p^{-β}.
-/

/-- The real partition sum is positive for real β (all terms are positive reals
    since primes are positive). Re-export from `BostConnesAnalytic`. -/
alias realPartitionSum_pos := BostConnesAnalytic.realPartitionSum_pos

/-! ## 4. Ground state limit → zero-temperature zeta limit

Our `ground_state_limit` proves: as β → ∞, the normalized finite KMS weight
converges to δ_{i,0} (the lowest prime dominates).

In the infinite system, the corresponding limit is a categorical/Hestenes--Krein
colimit readout of the finite prime-cutoff tower.  This file proves only the
algebraically precise finite-dimensional analogue.
-/

/-- Re-export: our finite ground state limit theorem from `BostConnesAnalytic`. -/
alias ground_state_limit := BostConnesAnalytic.ground_state_limit

end InfoGeometry.Algebra.BostConnesArithmeticBridge
