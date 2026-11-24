/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornRegularOperators
import InfoGeometry.Canonical.ZornCliffordRepresentation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Norm and units of the native Zorn left action

The existing linear lift of the real Zorn carrier takes values in the
associative ring of endomorphisms. Alternativity gives its square and
polarization laws; the existing conjugate contraction gives its inverse
exactly when the real split norm is nonzero.

The matrix theorem identifies the determinant's zero set in any genuine
eight-element basis. It does not assert a formula for the determinant's
nonzero values or faithfulness of the full Clifford algebra action.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornRegularNorm

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

/-- The native unit acts as the identity on the full Zorn module. -/
@[simp] theorem leftRegular_one :
    leftRegularRepresentation (1 : CanonicalZorn) = 1 := by
  apply LinearMap.ext
  intro X
  change (1 : CanonicalZorn) * X = X
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.one_mul X

/-- The square law follows from left alternativity of the source product. -/
theorem leftRegular_square (Z : CanonicalZorn) :
    leftRegularRepresentation Z * leftRegularRepresentation Z =
      leftRegularRepresentation (Z * Z) := by
  apply LinearMap.ext
  intro W
  change Z * (Z * W) = (Z * Z) * W
  apply InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.injective
  simp only [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_mul]
  have h := InfoGeometry.Algebra.ZornVectorMatrix.associator_left_alternative
    (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv Z)
    (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv W)
  change InfoGeometry.Algebra.ZornVectorMatrix.mul
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv Z)
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv Z))
      (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv W) -
    InfoGeometry.Algebra.ZornVectorMatrix.mul
      (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv Z)
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv Z)
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv W)) = 0 at h
  exact (sub_eq_zero.mp h).symm

/-- Polarization holds for every pair of source elements, including those
with nonzero trace. The right side need not be a scalar operator. -/
theorem leftRegular_anticommutator (X Y : CanonicalZorn) :
    leftRegularRepresentation X * leftRegularRepresentation Y +
        leftRegularRepresentation Y * leftRegularRepresentation X =
      leftRegularRepresentation (X * Y + Y * X) := by
  have h := leftRegular_square (X + Y)
  simp only [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add,
    map_add, add_mul, mul_add, leftRegular_square] at h
  have hc := congrArg (fun T : Module.End ℝ CanonicalZorn =>
    T - leftRegularRepresentation (X * X) - leftRegularRepresentation (Y * Y)) h
  rw [map_add]
  convert hc using 1 <;> abel

/-- Left multiplication followed by conjugate-left multiplication contracts
to the existing split norm on every state. -/
theorem leftRegular_mul_conj (Z : CanonicalZorn) :
    leftRegularRepresentation Z * leftRegularRepresentation (zornConj Z) =
      zornNormFun Z • (1 : Module.End ℝ CanonicalZorn) := by
  apply LinearMap.ext
  intro W
  exact mul_zornConj_mul Z W

/-- The reverse composition has the same scalar value. -/
theorem conj_mul_leftRegular (Z : CanonicalZorn) :
    leftRegularRepresentation (zornConj Z) * leftRegularRepresentation Z =
      zornNormFun Z • (1 : Module.End ℝ CanonicalZorn) := by
  apply LinearMap.ext
  intro W
  exact zornConj_mul_mul Z W

/-- The inverse candidate is an actual right inverse when the norm is nonzero. -/
theorem leftRegular_mul_inverse (Z : CanonicalZorn) (hZ : zornNormFun Z ≠ 0) :
    leftRegularRepresentation Z *
        ((zornNormFun Z)⁻¹ • leftRegularRepresentation (zornConj Z)) = 1 := by
  rw [mul_smul_comm, leftRegular_mul_conj, smul_smul,
    inv_mul_cancel₀ hZ, one_smul]

/-- The same candidate is also a left inverse in the associative operator ring. -/
theorem inverse_mul_leftRegular (Z : CanonicalZorn) (hZ : zornNormFun Z ≠ 0) :
    ((zornNormFun Z)⁻¹ • leftRegularRepresentation (zornConj Z)) *
        leftRegularRepresentation Z = 1 := by
  rw [smul_mul_assoc, conj_mul_leftRegular, smul_smul,
    inv_mul_cancel₀ hZ, one_smul]

/-- A real Zorn left operator is a unit exactly off the split-null cone.
The converse uses cancellation by an actual unit and the established
injectivity of the linear lift; it makes no associativity assumption on Zorn. -/
theorem isUnit_leftRegular_iff (Z : CanonicalZorn) :
    IsUnit (leftRegularRepresentation Z) ↔ zornNormFun Z ≠ 0 := by
  constructor
  · intro hunit hnorm
    have hconj : leftRegularRepresentation (zornConj Z) = 0 :=
      hunit.mul_left_cancel (by
        rw [mul_zero, leftRegular_mul_conj, hnorm, zero_smul])
    have hconjZ : zornConj Z = 0 :=
      leftRegularRepresentation_injective (hconj.trans (map_zero leftRegularRepresentation).symm)
    have hZ : Z = 0 := by
      simpa only [zornConj, neg_neg, neg_zero] using congrArg zornConj hconjZ
    have hzero : leftRegularRepresentation Z = 0 := by
      rw [hZ, map_zero]
    have h10 : (1 : Module.End ℝ CanonicalZorn) = 0 :=
      hunit.mul_left_cancel (by rw [mul_one, mul_zero, hzero])
    have hscalar := congrArg (fun T : Module.End ℝ CanonicalZorn =>
      (T (1 : CanonicalZorn)).a) h10
    simp at hscalar
  · intro hnorm
    exact ⟨⟨leftRegularRepresentation Z,
      (zornNormFun Z)⁻¹ • leftRegularRepresentation (zornConj Z),
      leftRegular_mul_inverse Z hnorm, inverse_mul_leftRegular Z hnorm⟩, rfl⟩

/-- Singularity of the actual eight-by-eight regular matrix is precisely
nullity of the split norm, independently of the chosen basis. -/
theorem det_leftRegular_eq_zero_iff
    (b : Module.Basis (Fin 8) ℝ CanonicalZorn) (Z : CanonicalZorn) :
    Matrix.det (LinearMap.toMatrix b b (leftRegularRepresentation Z)) = 0 ↔
      zornNormFun Z = 0 := by
  have h : Matrix.det (LinearMap.toMatrix b b (leftRegularRepresentation Z)) ≠ 0 ↔
      zornNormFun Z ≠ 0 := by
    calc
      Matrix.det (LinearMap.toMatrix b b (leftRegularRepresentation Z)) ≠ 0 ↔
          IsUnit (Matrix.det (LinearMap.toMatrix b b (leftRegularRepresentation Z))) :=
        isUnit_iff_ne_zero.symm
      _ ↔ IsUnit (LinearMap.toMatrix b b (leftRegularRepresentation Z)) :=
        (Matrix.isUnit_iff_isUnit_det _).symm
      _ ↔ IsUnit (leftRegularRepresentation Z) := LinearMap.isUnit_toMatrix_iff b
      _ ↔ zornNormFun Z ≠ 0 := isUnit_leftRegular_iff Z
  simpa only [not_not] using not_congr h

end InfoGeometry.Lie.CanonicalZornRegularNorm
