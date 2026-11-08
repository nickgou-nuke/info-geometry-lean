import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.EulerLimitCommute

Finite Euler-step commutation lemma for matrix operators.
-/

namespace InfoGeometry.Canonical.EulerLimitCommute

open Matrix

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- One finite Euler step: `I + cX`. -/
def eulerStep (c : ℝ) (X : M2R) : M2R :=
  (1 : M2R) + c • X

/--
If `X` and `Y` commute, then their finite Euler steps commute
for all real step sizes `c,d`.
-/
theorem eulerStep_commute (c d : ℝ) (X Y : M2R) (h_comm : X * Y = Y * X) :
    eulerStep c X * eulerStep d Y = eulerStep d Y * eulerStep c X := by
  unfold eulerStep
  ext i j <;> fin_cases i <;> fin_cases j
  · have h00 := congrArg (fun M : M2R => M 0 0) h_comm
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at h00 ⊢
    have h00' := congrArg (fun z : ℝ => (c * d) * z) h00
    nlinarith [h00']
  · have h01 := congrArg (fun M : M2R => M 0 1) h_comm
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at h01 ⊢
    have h01' := congrArg (fun z : ℝ => (c * d) * z) h01
    nlinarith [h01']
  · have h10 := congrArg (fun M : M2R => M 1 0) h_comm
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at h10 ⊢
    have h10' := congrArg (fun z : ℝ => (c * d) * z) h10
    nlinarith [h10']
  · have h11 := congrArg (fun M : M2R => M 1 1) h_comm
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at h11 ⊢
    have h11' := congrArg (fun z : ℝ => (c * d) * z) h11
    nlinarith [h11']

/--
If two Euler steps commute, all finite powers commute.
-/
theorem eulerStep_pow_commute
    (c d : ℝ) (X Y : M2R) (h_comm : X * Y = Y * X) (m n : ℕ) :
    (eulerStep c X) ^ m * (eulerStep d Y) ^ n =
      (eulerStep d Y) ^ n * (eulerStep c X) ^ m := by
  have hstep : eulerStep c X * eulerStep d Y = eulerStep d Y * eulerStep c X :=
    eulerStep_commute c d X Y h_comm
  have hstepComm : Commute (eulerStep c X) (eulerStep d Y) := by
    exact hstep
  have hpowR : Commute (eulerStep c X) ((eulerStep d Y) ^ n) :=
    hstepComm.pow_right n
  have hpowBoth : Commute ((eulerStep c X) ^ m) ((eulerStep d Y) ^ n) :=
    hpowR.pow_left m
  exact hpowBoth.eq

/--
Finite Euler-product power identity under commutation.
-/
theorem eulerStep_mul_pow
    (c d : ℝ) (X Y : M2R) (h_comm : X * Y = Y * X) (n : ℕ) :
    (eulerStep c X * eulerStep d Y) ^ n =
      (eulerStep c X) ^ n * (eulerStep d Y) ^ n := by
  have hstep : Commute (eulerStep c X) (eulerStep d Y) := by
    exact eulerStep_commute c d X Y h_comm
  simpa using hstep.mul_pow n

/--
Commutator readout: commuting Euler steps have zero commutator.
-/
theorem eulerStep_commutator_zero
    (c d : ℝ) (X Y : M2R) (h_comm : X * Y = Y * X) :
    eulerStep c X * eulerStep d Y - eulerStep d Y * eulerStep c X = 0 := by
  have h := eulerStep_commute c d X Y h_comm
  exact sub_eq_zero.mpr h

/-- Base Euler iterate at exponent `0`. -/
@[simp] theorem eulerStep_pow_zero (c : ℝ) (X : M2R) :
    (eulerStep c X) ^ (0 : ℕ) = (1 : M2R) := by
  simp

/-- Base Euler iterate at exponent `1`. -/
@[simp] theorem eulerStep_pow_one (c : ℝ) (X : M2R) :
    (eulerStep c X) ^ (1 : ℕ) = eulerStep c X := by
  simp

/-- Recursive Euler iterate step. -/
@[simp] theorem eulerStep_pow_succ (c : ℝ) (X : M2R) (n : ℕ) :
    (eulerStep c X) ^ (n + 1) = (eulerStep c X) ^ n * eulerStep c X := by
  simp [pow_succ]

/--
Finite first-order Euler product expansion:
`(I + cX)(I + cY) = I + c(X+Y) + c^2 XY`.
-/
theorem eulerStep_mul_sameScale
    (c : ℝ) (X Y : M2R) :
    eulerStep c X * eulerStep c Y =
      (1 : M2R) + c • (X + Y) + (c * c) • (X * Y) := by
  unfold eulerStep
  ext i j <;> fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

end InfoGeometry.Canonical.EulerLimitCommute
