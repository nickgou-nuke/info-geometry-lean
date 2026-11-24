/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Lie.CanonicalZornRegularOperators
import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Invertibility of the native real split-octonion right regular operator

The existing right regular operator acts on the full native `CanonicalZorn`
carrier. Kirmse contraction gives its inverse on the nonzero-norm locus.
Conversely, norm multiplicativity prevents a null multiplier from having
the unit in its image.

The null direction includes the zero element and every nonzero null element;
it does not impose a trace-zero or imaginary hypothesis. Composition takes
place in the associative endomorphism algebra. The left-operator inverse
and unit criterion are owned by `CanonicalZornRegularNorm`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionRegularInvertibility

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge (realCrossProduct3
  realZornCompositionDatum)
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis (CanonicalZorn
  rightMultiplication)
open InfoGeometry.Lie.SplitOctonionImaginaryAction (canonicalConj
  canonicalVectorEquiv_canonicalConj vector_norm_eq_canonical_det
  canonical_kirmse_right)

local notation "N" => ZornMatrix.detZ realCrossProduct3

private theorem canonicalConj_involutive (X : CanonicalZorn) :
    canonicalConj (canonicalConj X) = X := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj,
    InfoGeometry.Algebra.ZornVectorMatrix.conj_conj]

private theorem determinant_conj (X : CanonicalZorn) :
    N (canonicalConj X) = N X := by
  rw [← vector_norm_eq_canonical_det, canonicalVectorEquiv_canonicalConj,
    InfoGeometry.Algebra.ZornVectorMatrix.norm_conj,
    vector_norm_eq_canonical_det]

private theorem determinant_one : N (1 : CanonicalZorn) = 1 := by
  rw [← vector_norm_eq_canonical_det, canonicalVectorEquiv_one,
    InfoGeometry.Algebra.ZornVectorMatrix.norm_one]

private theorem determinant_mul (X Y : CanonicalZorn) :
    N (X * Y) = N X * N Y := by
  exact realZornCompositionDatum.detZ_mul X Y

/-- Right multiplication by the conjugate contracts the original right action. -/
theorem rightMultiplication_conjugate_mul (X : CanonicalZorn) :
    rightMultiplication (canonicalConj X) * rightMultiplication X =
      N X • (1 : Module.End ℝ CanonicalZorn) := by
  apply LinearMap.ext
  intro Y
  exact canonical_kirmse_right X Y

/-- The conjugate also gives the opposite-order right contraction. -/
theorem rightMultiplication_mul_conjugate (X : CanonicalZorn) :
    rightMultiplication X * rightMultiplication (canonicalConj X) =
      N X • (1 : Module.End ℝ CanonicalZorn) := by
  simpa only [canonicalConj_involutive, determinant_conj] using
    rightMultiplication_conjugate_mul (canonicalConj X)

/-- The actual regular right action as a unit of the endomorphism algebra.
Its inverse is the reciprocal norm times right multiplication by the conjugate. -/
def rightMultiplicationUnit (X : CanonicalZorn) (hX : N X ≠ 0) :
    (Module.End ℝ CanonicalZorn)ˣ where
  val := rightMultiplication X
  inv := (N X)⁻¹ • rightMultiplication (canonicalConj X)
  val_inv := by
    rw [mul_smul_comm, rightMultiplication_mul_conjugate, smul_smul,
      inv_mul_cancel₀ hX, one_smul]
  inv_val := by
    rw [smul_mul_assoc, rightMultiplication_conjugate_mul, smul_smul,
      inv_mul_cancel₀ hX, one_smul]

/-- A nonzero norm gives a bijective native right operator. -/
theorem rightMultiplication_bijective_of_det_ne_zero
    (X : CanonicalZorn) (hX : N X ≠ 0) :
    Function.Bijective (rightMultiplication X) := by
  exact (Module.End.isUnit_iff _).mp (rightMultiplicationUnit X hX).isUnit

/-- Surjectivity of the native right action is equivalent to a nonzero norm.
The forward implication tests whether the unit can lie in its image. -/
theorem rightMultiplication_surjective_iff (X : CanonicalZorn) :
    Function.Surjective (rightMultiplication X) ↔ N X ≠ 0 := by
  constructor
  · intro h hX
    obtain ⟨Y, hY⟩ := h (1 : CanonicalZorn)
    have hnorm := congrArg (fun Z : CanonicalZorn => N Z) hY
    change N (Y * X) = N (1 : CanonicalZorn) at hnorm
    rw [determinant_mul, determinant_one, hX, MulZeroClass.mul_zero] at hnorm
    exact zero_ne_one hnorm
  · intro hX
    exact (rightMultiplication_bijective_of_det_ne_zero X hX).2

/-- The native right operator is bijective exactly off the full split null cone. -/
theorem rightMultiplication_bijective_iff (X : CanonicalZorn) :
    Function.Bijective (rightMultiplication X) ↔ N X ≠ 0 := by
  exact ⟨fun h => (rightMultiplication_surjective_iff X).mp h.2,
    rightMultiplication_bijective_of_det_ne_zero X⟩

/-- Native ring-unit formulation of the right-operator criterion. -/
theorem rightMultiplication_isUnit_iff (X : CanonicalZorn) :
    IsUnit (rightMultiplication X) ↔ N X ≠ 0 := by
  rw [Module.End.isUnit_iff, rightMultiplication_bijective_iff]

/-- Singularity includes both zero and nonzero null right multipliers. -/
theorem rightMultiplication_not_bijective_iff (X : CanonicalZorn) :
    ¬ Function.Bijective (rightMultiplication X) ↔ N X = 0 := by
  rw [rightMultiplication_bijective_iff, not_not]

end InfoGeometry.Lie.SplitOctonionRegularInvertibility

end
