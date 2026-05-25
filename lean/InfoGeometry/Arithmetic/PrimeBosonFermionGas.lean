import Mathlib

/-!
# Finite prime boson/fermion cancellation

Finite algebraic theorem:

  `(∏ p ∈ S, (1 - x p)⁻¹) * (∏ p ∈ S, (1 - x p)) = 1`

under the local nonzero condition `1 - x p ≠ 0`.

This is the finite theorem-root behind the formal cancellation
`ζ(s) * (1 / ζ(s)) = 1`, but no infinite product or zeta claim is made here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeBosonFermionGas

open scoped BigOperators

variable {ι R : Type*} [Field R]

/-- Finite signed fermion / Möbius Euler factor product. -/
def signedFermionPartition (S : Finset ι) (x : ι → R) : R :=
  ∏ p ∈ S, (1 - x p)

/-- Finite boson Euler factor product. -/
def bosonPartition (S : Finset ι) (x : ι → R) : R :=
  ∏ p ∈ S, (1 - x p)⁻¹

/--
Finite boson × signed-fermion cancellation.

This is the real algebraic lemma:
the inverse Euler factors cancel the signed fermion Euler factors.
-/
theorem boson_mul_signedFermion_cancel
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    bosonPartition S x * signedFermionPartition S x = 1 := by
  unfold bosonPartition signedFermionPartition
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p hp
  exact inv_mul_cancel₀ (h p hp)

/--
Finite signed-fermion × boson cancellation.

Same result with the factors reversed.
-/
theorem signedFermion_mul_boson_cancel
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    signedFermionPartition S x * bosonPartition S x = 1 := by
  unfold bosonPartition signedFermionPartition
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p hp
  exact mul_inv_cancel₀ (h p hp)

/-! ## Real lemma: logarithm of a positive finite product -/

/--
For a positive finite family, the logarithm of the product is the sum of the
logarithms.

This is the direct proof needed for prime log-volume:
`log (∏ p, v p) = ∑ p, log (v p)`.
No certificate field, no wrapper structure.
-/
theorem log_prod_of_pos
    {ι : Type*}
    (s : Finset ι)
    (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) :
    Real.log (s.prod f) = s.sum (fun i => Real.log (f i)) := by
  refine Real.log_prod ?_
  intro i hi
  exact ne_of_gt (hf i hi)

end InfoGeometry.Arithmetic.PrimeBosonFermionGas
