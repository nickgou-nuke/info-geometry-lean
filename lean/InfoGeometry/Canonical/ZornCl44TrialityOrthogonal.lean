/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCl44Triality
import Mathlib.Algebra.Lie.SkewAdjoint

/-!
# The three infinitesimal triality actions preserve the split norm

These additions certify that the vector and two chiral spinor bivectors
belong to Mathlib's Lie subalgebra of skew-adjoint endomorphisms of the
associated Zorn bilinear form.  The spinor proofs use the adjoint identity
`B(a * x, y) = B(x, conjugate a * y)` and composition of adjoint pairs.

The carrier and form are those of `ZornCl44Triality`; no norm-preservation
assumption is supplied by the caller.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCl44Triality

open ZornMatrix ZornClifford

/-- The vector bivector is infinitesimally orthogonal for the native split form. -/
theorem vectorBivector_skew (a b v w : ZornMatrix ℝ) :
    zornBilin (vectorBivector a b v) w =
      -zornBilin v (vectorBivector a b w) := by
  simp only [vectorBivector_apply, LinearMap.map_sub₂, LinearMap.map_smul₂,
    map_sub, map_smul, smul_eq_mul]
  rw [zornBilin_symm v a, zornBilin_symm v b]
  ring

/-- The same property in Mathlib's native adjoint-pair language. -/
theorem vectorBivector_isSkewAdjoint (a b : ZornMatrix ℝ) :
    zornBilin.IsSkewAdjoint (vectorBivector a b) := by
  intro v w
  change zornBilin (vectorBivector a b v) w =
    zornBilin v (-(vectorBivector a b w))
  rw [map_neg]
  exact vectorBivector_skew a b v w

/-- Conjugation is an involution on the existing canonical Zorn carrier. -/
@[simp] theorem zornConj_involutive (a : ZornMatrix ℝ) :
    zornConj (zornConj a) = a := by
  apply ZornMatrix.ext <;> simp [zornConj]

/-- Left multiplication by the conjugate is the adjoint of left multiplication. -/
theorem zornBilin_left_adjoint (a x y : ZornMatrix ℝ) :
    zornBilin (a * x) y = zornBilin x (zornConj a * y) := by
  simp [zornBilin_apply, ZornMatrix.mul, zornConj, dot, cross]
  ring

/-- The corresponding adjoint formula for right multiplication. -/
theorem zornBilin_right_adjoint (a x y : ZornMatrix ℝ) :
    zornBilin (x * a) y = zornBilin x (y * zornConj a) := by
  simp [zornBilin_apply, ZornMatrix.mul, zornConj, dot, cross]
  ring

theorem leftMulLinear_isAdjointPair (a : ZornMatrix ℝ) :
    LinearMap.IsAdjointPair zornBilin zornBilin
      (leftMulLinear a) (leftMulLinear (zornConj a)) :=
  zornBilin_left_adjoint a

theorem rightMulLinear_isAdjointPair (a : ZornMatrix ℝ) :
    LinearMap.IsAdjointPair zornBilin zornBilin
      (rightMulLinear a) (rightMulLinear (zornConj a)) :=
  zornBilin_right_adjoint a

/-- Any real multiple of the difference of mutually adjoint maps is skew-adjoint. -/
theorem adjoint_difference_isSkewAdjoint
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (P Q : Module.End ℝ V) (r : ℝ)
    (hPQ : LinearMap.IsAdjointPair B B P Q)
    (hQP : LinearMap.IsAdjointPair B B Q P) :
    B.IsSkewAdjoint (r • (P - Q)) := by
  intro x y
  change B (r • (P x - Q x)) y = B x (-(r • (P y - Q y)))
  simp only [LinearMap.map_smul₂, LinearMap.map_sub₂,
    map_neg, map_smul, map_sub, smul_eq_mul]
  rw [hPQ x y, hQP x y]
  rw [mul_sub, mul_sub, neg_sub]

/-- The positive-chirality triality action preserves the same split quadratic form. -/
theorem spinBivPlus_isSkewAdjoint (a b : ZornMatrix ℝ) :
    zornBilin.IsSkewAdjoint (spinBivPlus a b) := by
  apply adjoint_difference_isSkewAdjoint zornBilin
    (leftMulLinear a * leftMulLinear (zornConj b))
    (leftMulLinear b * leftMulLinear (zornConj a)) (1 / 4 : ℝ)
  · simpa only [zornConj_involutive] using
      (leftMulLinear_isAdjointPair a).mul
        (leftMulLinear_isAdjointPair (zornConj b))
  · simpa only [zornConj_involutive] using
      (leftMulLinear_isAdjointPair b).mul
        (leftMulLinear_isAdjointPair (zornConj a))

/-- The negative-chirality triality action also preserves the split quadratic form. -/
theorem spinBivMinus_isSkewAdjoint (a b : ZornMatrix ℝ) :
    zornBilin.IsSkewAdjoint (spinBivMinus a b) := by
  apply adjoint_difference_isSkewAdjoint zornBilin
    (leftMulLinear (zornConj a) * leftMulLinear b)
    (leftMulLinear (zornConj b) * leftMulLinear a) (1 / 4 : ℝ)
  · simpa only [zornConj_involutive] using
      (leftMulLinear_isAdjointPair (zornConj a)).mul
        (leftMulLinear_isAdjointPair b)
  · simpa only [zornConj_involutive] using
      (leftMulLinear_isAdjointPair (zornConj b)).mul
        (leftMulLinear_isAdjointPair a)

theorem spinBivPlus_skew (a b v w : ZornMatrix ℝ) :
    zornBilin (spinBivPlus a b v) w =
      -zornBilin v (spinBivPlus a b w) := by
  simpa only [Pi.neg_apply, map_neg] using spinBivPlus_isSkewAdjoint a b v w

theorem spinBivMinus_skew (a b v w : ZornMatrix ℝ) :
    zornBilin (spinBivMinus a b v) w =
      -zornBilin v (spinBivMinus a b w) := by
  simpa only [Pi.neg_apply, map_neg] using spinBivMinus_isSkewAdjoint a b v w

/-- The three triality operators lie in the native orthogonal Lie subalgebra. -/
theorem vectorBivector_mem_skewAdjointLieSubalgebra (a b : ZornMatrix ℝ) :
    vectorBivector a b ∈ skewAdjointLieSubalgebra zornBilin := by
  change vectorBivector a b ∈ zornBilin.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  exact vectorBivector_isSkewAdjoint a b

theorem spinBivPlus_mem_skewAdjointLieSubalgebra (a b : ZornMatrix ℝ) :
    spinBivPlus a b ∈ skewAdjointLieSubalgebra zornBilin := by
  change spinBivPlus a b ∈ zornBilin.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  exact spinBivPlus_isSkewAdjoint a b

theorem spinBivMinus_mem_skewAdjointLieSubalgebra (a b : ZornMatrix ℝ) :
    spinBivMinus a b ∈ skewAdjointLieSubalgebra zornBilin := by
  change spinBivMinus a b ∈ zornBilin.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  exact spinBivMinus_isSkewAdjoint a b

/-- The vector bivector as an actual element of the split-form orthogonal Lie algebra. -/
def vectorOrthogonalBivector (a b : ZornMatrix ℝ) :
    skewAdjointLieSubalgebra zornBilin :=
  ⟨vectorBivector a b, vectorBivector_mem_skewAdjointLieSubalgebra a b⟩

/-- The positive spinor bivector in the same native orthogonal Lie algebra. -/
def plusOrthogonalBivector (a b : ZornMatrix ℝ) :
    skewAdjointLieSubalgebra zornBilin :=
  ⟨spinBivPlus a b, spinBivPlus_mem_skewAdjointLieSubalgebra a b⟩

/-- The negative spinor bivector in the same native orthogonal Lie algebra. -/
def minusOrthogonalBivector (a b : ZornMatrix ℝ) :
    skewAdjointLieSubalgebra zornBilin :=
  ⟨spinBivMinus a b, spinBivMinus_mem_skewAdjointLieSubalgebra a b⟩

end InfoGeometry.Canonical.ZornCl44Triality
