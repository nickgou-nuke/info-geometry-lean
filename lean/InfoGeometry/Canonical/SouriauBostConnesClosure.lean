import Mathlib
open Real Finset

/-!
# Souriau–Bost–Connes Closure

## Theorem 1: Weyl denominator = reciprocal primon partition

Z_P(β) = 1 / Δ_{A₁^P}(e^{-β log ·})

Proof: Euler product factorization → ∏ a⁻¹ = (∏ a)⁻¹

Zero global axioms. Zero sorries.
-/
noncomputable def primonPartition (P : Finset ℕ) (β : ℝ) : ℝ :=
  ∏ p ∈ P, (1 - (p : ℝ) ^ (-β : ℝ))⁻¹

noncomputable def weylDenominator (P : Finset ℕ) (β : ℝ) : ℝ :=
  ∏ p ∈ P, (1 - (p : ℝ) ^ (-β : ℝ))

/--
**Theorem**: The primon gas partition function is the inverse of the
Weyl denominator. This is the algebraic identity that closes the
Bulk → Boundary thermodynamic bridge.

Z_P(β) = (Δ(e^{-β log}))⁻¹

Proved by `Finset.prod_inv_distrib`.
-/
theorem weylDenom_eq_partition_inv (P : Finset ℕ) (β : ℝ) (hβpos : β > 0) :
    primonPartition P β = (weylDenominator P β)⁻¹ := by
  unfold primonPartition weylDenominator
  rw [Finset.prod_inv_distrib]
