/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationRightLogarithmicForm
import InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
import InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Ordered second derivatives of invertible operator amplitudes

For the existing derivation action, the right logarithmic form satisfies an
exact noncommutative Riccati identity. Its ordered second quotient is not
automatically self-adjoint. In the full complex matrix algebra the defect is
an explicit commutator, and Mathlib's self-adjoint part gives the symmetric
quotient. The norm estimate retains the inverse-amplitude factor.

These are algebraic and normed operator statements. No spatial Laplacian,
spacetime metric, curvature bound, or continuation through a nonunit is
constructed or inferred.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationAmplitudeGeometry

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities
open InfoGeometry.Geometry.AssociativeGaugeConnection (conjugate)

section Derivations

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- The second represented derivative divided on the right by the unit amplitude. -/
def rightAmplitudeSecondDerivative (g : Aˣ) (x : K.L) : A :=
  K.operatorAction x (K.operatorAction x (g : A)) * (↑g⁻¹ : A)

/-- The logarithmic Riccati identity retains the ordered square. -/
theorem rightLogarithmicOneForm_riccati (g : Aˣ) (x : K.L) :
    K.operatorAction x (rightLogarithmicOneForm K g x) +
      rightLogarithmicOneForm K g x * rightLogarithmicOneForm K g x =
        rightAmplitudeSecondDerivative K g x := by
  simp only [rightLogarithmicOneForm_apply, rightAmplitudeSecondDerivative]
  rw [K.operatorAction_leibniz, operatorAction_inv_unit]
  noncomm_ring

/-- Squaring an amplitude does not simply double its right logarithmic form. -/
theorem rightLogarithmicOneForm_square_defect (g : Aˣ) (x : K.L) :
    rightLogarithmicOneForm K (g * g) x - 2 • rightLogarithmicOneForm K g x =
      ((g : A) * rightLogarithmicOneForm K g x -
        rightLogarithmicOneForm K g x * (g : A)) * (↑g⁻¹ : A) := by
  rw [rightLogarithmicOneForm_mul]
  simp only [conjugate, two_nsmul, sub_mul, mul_assoc, Units.mul_inv, mul_one]
  abel

/-- The mixed product term keeps its order; no commutation of amplitudes is used. -/
theorem rightAmplitudeSecondDerivative_mul (g h : Aˣ) (x : K.L) :
    rightAmplitudeSecondDerivative K (g * h) x =
      rightAmplitudeSecondDerivative K g x +
        conjugate g (rightAmplitudeSecondDerivative K h x) +
          2 • (rightLogarithmicOneForm K g x *
            conjugate g (rightLogarithmicOneForm K h x)) := by
  simp only [rightAmplitudeSecondDerivative, rightLogarithmicOneForm_apply,
    Units.val_mul, mul_inv_rev, K.operatorAction_leibniz, map_add, conjugate,
    add_mul, two_nsmul, mul_assoc, Units.mul_inv_cancel_left,
    Units.inv_mul_cancel_left]
  abel

/-- A finite family of derivation directions gives the sum of the exact identities. -/
theorem sum_rightLogarithmicOneForm_riccati {ι : Type*} [Fintype ι]
    (g : Aˣ) (directions : ι → K.L) :
    (∑ i, K.operatorAction (directions i)
        (rightLogarithmicOneForm K g (directions i))) +
      (∑ i, rightLogarithmicOneForm K g (directions i) *
        rightLogarithmicOneForm K g (directions i)) =
      ∑ i, rightAmplitudeSecondDerivative K g (directions i) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => rightLogarithmicOneForm_riccati K g (directions i)

end Derivations

section Matrices

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- Specialization to the existing full matrix derivation lane and native inner action. -/
def matrixAmplitudeQuotient (H : Mat) (g : Matˣ) : Mat :=
  rightAmplitudeSecondDerivative (matrixDerivationsLane ℂ n) g
    (matrixInnerLieHom ℂ n H)

theorem matrixAmplitudeQuotient_eq (H : Mat) (g : Matˣ) :
    matrixAmplitudeQuotient H g = ⁅H, ⁅H, (g : Mat)⁆⁆ * (↑g⁻¹ : Mat) := rfl

/-- Two adjoint reversals make the double commutator self-adjoint. -/
theorem double_lie_isSelfAdjoint {H A : Mat}
    (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint ⁅H, ⁅H, A⁆⁆ := by
  change star ⁅H, ⁅H, A⁆⁆ = ⁅H, ⁅H, A⁆⁆
  simp only [Ring.lie_def, star_sub, star_mul, hH.star_eq, hA.star_eq]
  noncomm_ring

/-- Invertibility is genuine, so taking the adjoint preserves the same inverse. -/
theorem inverse_amplitude_isSelfAdjoint {g : Matˣ}
    (hg : IsSelfAdjoint (g : Mat)) : IsSelfAdjoint (↑g⁻¹ : Mat) := by
  have hunit : IsSelfAdjoint g := Units.ext hg.star_eq
  exact congrArg (fun u : Matˣ => (u : Mat)) hunit.inv.star_eq

/-- The adjoint reverses the quotient's order. -/
theorem star_matrixAmplitudeQuotient {H : Mat} {g : Matˣ}
    (hH : IsSelfAdjoint H) (hg : IsSelfAdjoint (g : Mat)) :
    star (matrixAmplitudeQuotient H g) =
      (↑g⁻¹ : Mat) * ⁅H, ⁅H, (g : Mat)⁆⁆ := by
  rw [matrixAmplitudeQuotient_eq, star_mul,
    (inverse_amplitude_isSelfAdjoint hg).star_eq,
    (double_lie_isSelfAdjoint hH hg).star_eq]

/-- Exact obstruction to treating an ordered amplitude quotient as an observable. -/
theorem matrixAmplitudeQuotient_adjoint_defect {H : Mat} {g : Matˣ}
    (hH : IsSelfAdjoint H) (hg : IsSelfAdjoint (g : Mat)) :
    matrixAmplitudeQuotient H g - star (matrixAmplitudeQuotient H g) =
      ⁅⁅H, ⁅H, (g : Mat)⁆⁆, (↑g⁻¹ : Mat)⁆ := by
  rw [star_matrixAmplitudeQuotient hH hg, matrixAmplitudeQuotient_eq]
  rfl

/-- Commutation is a necessary and sufficient conclusion, not an ambient restriction. -/
theorem matrixAmplitudeQuotient_isSelfAdjoint_iff {H : Mat} {g : Matˣ}
    (hH : IsSelfAdjoint H) (hg : IsSelfAdjoint (g : Mat)) :
    IsSelfAdjoint (matrixAmplitudeQuotient H g) ↔
      Commute ⁅H, ⁅H, (g : Mat)⁆⁆ (↑g⁻¹ : Mat) := by
  change star (matrixAmplitudeQuotient H g) = matrixAmplitudeQuotient H g ↔ _
  rw [star_matrixAmplitudeQuotient hH hg, matrixAmplitudeQuotient_eq]
  exact eq_comm

/-- The native self-adjoint part supplies the symmetrized operator quotient. -/
theorem selfAdjointPart_matrixAmplitudeQuotient {H : Mat} {g : Matˣ}
    (hH : IsSelfAdjoint H) (hg : IsSelfAdjoint (g : Mat)) :
    (selfAdjointPart ℝ (matrixAmplitudeQuotient H g) : Mat) =
      (1 / 2 : ℝ) • (⁅H, ⁅H, (g : Mat)⁆⁆ * (↑g⁻¹ : Mat) +
        (↑g⁻¹ : Mat) * ⁅H, ⁅H, (g : Mat)⁆⁆) := by
  rw [selfAdjointPart_apply_coe, star_matrixAmplitudeQuotient hH hg,
    matrixAmplitudeQuotient_eq]
  norm_num

open scoped Matrix.Norms.L2Operator

/-- The native matrix operator norm gives a commutator bound without commutation. -/
theorem norm_lie_le_twice (H A : Mat) : ‖⁅H, A⁆‖ ≤ 2 * ‖H‖ * ‖A‖ := by
  calc
    ‖⁅H, A⁆‖ ≤ ‖H * A‖ + ‖A * H‖ := norm_sub_le _ _
    _ ≤ ‖H‖ * ‖A‖ + ‖A‖ * ‖H‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖H‖ * ‖A‖ := by ring

/-- Control requires an inverse-amplitude bound; invertibility alone gives no uniform bound. -/
theorem norm_matrixAmplitudeQuotient_le (H : Mat) (g : Matˣ) :
    ‖matrixAmplitudeQuotient H g‖ ≤
      4 * ‖H‖ ^ 2 * ‖(g : Mat)‖ * ‖(↑g⁻¹ : Mat)‖ := by
  rw [matrixAmplitudeQuotient_eq]
  calc
    ‖⁅H, ⁅H, (g : Mat)⁆⁆ * (↑g⁻¹ : Mat)‖ ≤
        ‖⁅H, ⁅H, (g : Mat)⁆⁆‖ * ‖(↑g⁻¹ : Mat)‖ := norm_mul_le _ _
    _ ≤ (2 * ‖H‖ * ‖⁅H, (g : Mat)⁆‖) * ‖(↑g⁻¹ : Mat)‖ :=
      mul_le_mul_of_nonneg_right (norm_lie_le_twice H _) (norm_nonneg _)
    _ ≤ (2 * ‖H‖ * (2 * ‖H‖ * ‖(g : Mat)‖)) * ‖(↑g⁻¹ : Mat)‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_lie_le_twice H _) (by positivity)) (norm_nonneg _)
    _ = 4 * ‖H‖ ^ 2 * ‖(g : Mat)‖ * ‖(↑g⁻¹ : Mat)‖ := by ring

end Matrices

end InfoGeometry.OperatorAlgebra.DerivationAmplitudeGeometry
