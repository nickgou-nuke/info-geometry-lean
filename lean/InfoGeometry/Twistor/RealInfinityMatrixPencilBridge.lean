/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealInfinityMatrixPencil
import InfoGeometry.Twistor.RealInfinityTwistor

/-!
# The real infinity matrix pencil and the genuine dual-valued form

The native sum-indexed coordinates are `Sum.elim z.1 z.2`. The lower matrix
represents the already-owned real infinity form, and the upper matrix
represents its pullback by the already-owned block rotation.

The final identity specifies the second-argument convention for metric
raising: `g(z, OΛ w) = Iflat(z,w) + Λ Iupper(z,w)`. Thus the matrix operator
is related to the genuine bilinear form by an explicit equality; the form
and the operator remain different typed objects.

For the existing curried map `z ↦ infinityTwistor z`, the corresponding
metric dual representative has the opposite sign, as stated separately.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealInfinityMatrixPencilBridge

open Matrix
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Quantum.NeutralKreinMajoranaFrame
open InfoGeometry.Twistor.RealTwistorBlockInversion
open InfoGeometry.Twistor.RealInfinityTwistor
open InfoGeometry.Twistor.RealInfinityMatrixPencil
open scoped Matrix

/-- The lower native matrix represents the existing map into the genuine dual. -/
theorem infinityLowerMatrix_pairing (z w : TwistorSpace) :
    dotProduct (Sum.elim z.1 z.2)
        (infinityLowerMatrix *ᵥ Sum.elim w.1 w.2) =
      infinityTwistor z w := by
  simp [infinityLowerMatrix, Eminus, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_two, sub_eq_add_neg] <;> ring

/-- The upper matrix is the existing real infinity form after block rotation. -/
theorem infinityUpperMatrix_pairing (z w : TwistorSpace) :
    dotProduct (Sum.elim z.1 z.2)
        (infinityUpperMatrix *ᵥ Sum.elim w.1 w.2) =
      infinityTwistor (blockRotation z) (blockRotation w) := by
  simp [infinityUpperMatrix, Eminus, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_two, blockRotation_apply,
    sub_eq_add_neg] <;> ring

/-- The pencil is a sum of the two specified bilinear forms. -/
theorem infinityMatrixPencil_pairing (Λ : ℝ) (z w : TwistorSpace) :
    dotProduct (Sum.elim z.1 z.2)
        (infinityMatrixPencil Λ *ᵥ Sum.elim w.1 w.2) =
      infinityTwistor z w +
        Λ * infinityTwistor (blockRotation z) (blockRotation w) := by
  simp only [infinityMatrixPencil, Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul, infinityLowerMatrix_pairing,
    infinityUpperMatrix_pairing, smul_eq_mul]

/-- This is the explicit duality identity justifying metric raising in the
second argument. It is independent of any Hermitian or spacetime interpretation. -/
theorem raisedInfinityMatrix_pairing (Λ : ℝ) (z w : TwistorSpace) :
    dotProduct (Sum.elim z.1 z.2)
        (kreinMetric 2 *ᵥ (raisedInfinityMatrix Λ *ᵥ Sum.elim w.1 w.2)) =
      infinityTwistor z w +
        Λ * infinityTwistor (blockRotation z) (blockRotation w) := by
  rw [Matrix.mulVec_mulVec, metric_mul_raisedInfinityMatrix]
  exact infinityMatrixPencil_pairing Λ z w

/-- The existing dual-valued form curries its first argument. Its metric dual
representative is `-OΛ z`; alternation accounts for this sign. -/
theorem raisedInfinityMatrix_curried_pairing (Λ : ℝ) (z w : TwistorSpace) :
    dotProduct (Sum.elim w.1 w.2)
        (kreinMetric 2 *ᵥ ((-raisedInfinityMatrix Λ) *ᵥ Sum.elim z.1 z.2)) =
      infinityTwistor z w +
        Λ * infinityTwistor (blockRotation z) (blockRotation w) := by
  rw [Matrix.neg_mulVec, Matrix.mulVec_neg, dotProduct_neg,
    raisedInfinityMatrix_pairing]
  rw [infinityTwistor_skew w z,
    infinityTwistor_skew (blockRotation w) (blockRotation z)]
  ring

end InfoGeometry.Twistor.RealInfinityMatrixPencilBridge
