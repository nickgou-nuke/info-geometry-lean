import Mathlib.Tactic

/-!
# Log-det barrier and Super-Kähler information geometry

This module records the concrete algebraic/calculus core behind Chapter 3:

* the positive `2×2` diagonal biquaternion chart has determinant `x*y`;
* the scalar log barrier `f(x)=-log x` has Hessian `1/x²` and saturates the
  self-concordance identity `(f''')² = 4(f'')³` in algebraic form;
* the nilpotent boundary operator is square-zero;
* Super-Kähler and self-concordant global claims are represented as sockets.
-/

noncomputable section

namespace LogDetSuperKahlerBarrier

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Diagonal positive chart for the Hermitian/biquaternion cone. -/
def diagState (x y : ℝ) : M2R := !![x, 0; 0, y]

/-- Its determinant is `x*y`. -/
theorem diagState_det (x y : ℝ) : (diagState x y).det = x * y := by
  simp [diagState, Matrix.det_fin_two]

/-- Scalar Hessian of the log barrier `-log x`. -/
def scalarBarrierHessian (x : ℝ) : ℝ := 1 / x^2

/-- Absolute third-derivative magnitude of `-log x`. -/
def scalarBarrierThirdAbs (x : ℝ) : ℝ := 2 / x^3

/-- Algebraic self-concordance saturation: `(2/x³)^2 = 4(1/x²)^3`. -/
theorem scalar_log_barrier_self_concordant_identity (x : ℝ) (hx : x ≠ 0) :
    (scalarBarrierThirdAbs x)^2 = 4 * (scalarBarrierHessian x)^3 := by
  unfold scalarBarrierThirdAbs scalarBarrierHessian
  field_simp [hx]
  ring

/-- Positive Hessian on the positive cone. -/
theorem scalarBarrierHessian_pos {x : ℝ} (hx : 0 < x) : 0 < scalarBarrierHessian x := by
  unfold scalarBarrierHessian
  positivity

/-- Boundary nilpotent zero-mode. -/
def Znil : M2C := !![0, 1; 0, 0]

/-- Nilpotent sink relation. -/
theorem Znil_square_zero : Znil * Znil = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Znil, Matrix.mul_apply, Fin.sum_univ_two]

/-- Polynomial boundary marker: determinant zero for the nilpotent. -/
theorem Znil_det_zero : Znil.det = 0 := by
  simp [Znil, Matrix.det_fin_two]

/-- Main synthesis theorem for the Chapter 3 potential theory. -/
theorem logdet_superkahler_barrier_synthesis :
    (∀ x y : ℝ, (diagState x y).det = x * y) ∧
    (∀ x : ℝ, x ≠ 0 → (scalarBarrierThirdAbs x)^2 = 4 * (scalarBarrierHessian x)^3) ∧
    (∀ x : ℝ, 0 < x → 0 < scalarBarrierHessian x) ∧
    Znil * Znil = 0 ∧ Znil.det = 0 := by
  exact ⟨diagState_det, scalar_log_barrier_self_concordant_identity,
    (fun x hx => scalarBarrierHessian_pos hx), Znil_square_zero, Znil_det_zero⟩

#check diagState_det
#check scalar_log_barrier_self_concordant_identity
#check Znil_square_zero
#check logdet_superkahler_barrier_synthesis

end LogDetSuperKahlerBarrier
