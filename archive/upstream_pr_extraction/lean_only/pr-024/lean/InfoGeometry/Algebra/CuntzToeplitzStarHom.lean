import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz-Toeplitz StarRing

Extends `CuntzTensorQuotient.lean` with the `StarRing` instance for
`CuntzToeplitzAlg n`.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzTensorQuotient

/-! ## Dagger descends through the Toeplitz relation -/

theorem dagger_CuntzToeplitzRel {n : ℕ} : ∀ {x y : CuntzTensor n},
    CuntzToeplitzRel n x y → CuntzToeplitzRel n (star x) (star y) := by
  intro x y h; rcases h with ⟨i, j⟩
  by_cases hij : i = j
  · subst j; simpa using CuntzToeplitzRel.orth (n := n) i i
  · have hji : j ≠ i := fun h => hij h.symm
    simpa [hij, hji] using CuntzToeplitzRel.orth (n := n) j i

/-! ## StarRing for the Cuntz-Toeplitz algebra -/

instance (n : ℕ) : StarRing (CuntzToeplitzAlg n) :=
  RingQuot.starRing (CuntzToeplitzRel n) (fun _ _ h => dagger_CuntzToeplitzRel h)

/-- Star on the Toeplitz quotient map commutes with the dagger. -/
theorem star_toeplitzMk (n : ℕ) (x : CuntzTensor n) :
    star (toeplitzMk n x) = toeplitzMk n (star x) := by
  change star ((RingQuot.mkAlgHom ℂ (CuntzToeplitzRel n)) x) =
    (RingQuot.mkAlgHom ℂ (CuntzToeplitzRel n)) (star x)
  simp [RingQuot.mkAlgHom_def, RingQuot.mkRingHom_def]
  rfl

/-- Star swaps Toeplitz S with Sdag. -/
@[simp] theorem star_toeplitzS (n : ℕ) (i : Fin n) :
    star (toeplitzS n i) = toeplitzSdag n i := by
  rw [toeplitzS, toeplitzSdag, star_toeplitzMk, star_S]

@[simp] theorem star_toeplitzSdag (n : ℕ) (i : Fin n) :
    star (toeplitzSdag n i) = toeplitzS n i := by
  rw [toeplitzSdag, toeplitzS, star_toeplitzMk, star_Sdag]

end InfoGeometry.Algebra.CuntzTensorQuotient
