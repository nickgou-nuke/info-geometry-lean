import Mathlib
import InfoGeometry.Physics.FiniteRelativeModularOperator

/-!
# Finite relative modular logarithmic bridge

This owner stays on the faithful diagonal matrix-unit basis.  It defines the
left/right surprisal action directly and proves its eigenvalue formula.  No
general matrix logarithm or Tomita--Takesaki functional calculus is claimed.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteRelativeModularLogBridge

open InfoGeometry.Physics.FiniteRelativeModularOperator
open InfoGeometry.Physics.RegularBimoduleCommutant

noncomputable def relativeLogEigenvalue (p q : ℝ) : ℝ :=
  -Real.log p + Real.log q

theorem relativeLogEigenvalue_eq_neg_log_ratio
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    relativeLogEigenvalue p q = -Real.log (p / q) := by
  unfold relativeLogEigenvalue
  rw [Real.log_div hp.ne' hq.ne']
  ring

theorem relativeLogEigenvalue_swap
    (p q : ℝ) :
    relativeLogEigenvalue q p = -relativeLogEigenvalue p q := by
  unfold relativeLogEigenvalue
  ring

noncomputable def leftSurprisalMatrix {n : ℕ} (p : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => ((-Real.log (p i) : ℝ) : ℂ))

noncomputable def rightSurprisalMatrix {n : ℕ} (q : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun j => ((-Real.log (q j) : ℝ) : ℂ))

noncomputable def relativeLogAction {n : ℕ} (p q : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  leftAction (R := ℂ) (leftSurprisalMatrix p) -
    rightAction (R := ℂ) (rightSurprisalMatrix q)

theorem diagonal_mul_matrixUnit {n : ℕ} (d : Fin n → ℂ) (i j : Fin n) :
    Matrix.diagonal d * matrixUnit i j =
      d i • matrixUnit i j := by
  ext a b
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      simp [matrixUnit, Matrix.diagonal_mul]
    · simp [matrixUnit, Matrix.diagonal_mul, hb]
  · simp [matrixUnit, Matrix.diagonal_mul, ha]

theorem matrixUnit_mul_diagonal {n : ℕ} (d : Fin n → ℂ) (i j : Fin n) :
    matrixUnit i j * Matrix.diagonal d =
      d j • matrixUnit i j := by
  ext a b
  by_cases hb : b = j
  · subst b
    by_cases ha : a = i
    · subst a
      simp [matrixUnit, Matrix.mul_diagonal]
    · simp [matrixUnit, Matrix.mul_diagonal, ha]
  · simp [matrixUnit, Matrix.mul_diagonal, hb]

theorem leftSurprisalAction_matrixUnit
    {n : ℕ} (p : Fin n → ℝ) (i j : Fin n) :
    leftAction (R := ℂ) (leftSurprisalMatrix p) (matrixUnit i j) =
      ((-Real.log (p i) : ℝ) : ℂ) • matrixUnit i j := by
  unfold leftAction leftSurprisalMatrix
  simp only [leftAction_apply]
  exact diagonal_mul_matrixUnit (fun i => ((-Real.log (p i) : ℝ) : ℂ)) i j

theorem rightSurprisalAction_matrixUnit
    {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) :
    rightAction (R := ℂ) (rightSurprisalMatrix q) (matrixUnit i j) =
      ((-Real.log (q j) : ℝ) : ℂ) • matrixUnit i j := by
  unfold rightAction rightSurprisalMatrix
  simp only [rightAction_apply]
  exact matrixUnit_mul_diagonal (fun j => ((-Real.log (q j) : ℝ) : ℂ)) i j

theorem relativeLogAction_eq_leftRightSurprisal
    {n : ℕ} (p q : Fin n → ℝ) :
    relativeLogAction p q =
      leftAction (R := ℂ) (leftSurprisalMatrix p) -
        rightAction (R := ℂ) (rightSurprisalMatrix q) := rfl

theorem relativeLogAction_matrixUnit
    {n : ℕ} (p q : Fin n → ℝ) (i j : Fin n) :
    relativeLogAction p q (matrixUnit i j) =
      ((relativeLogEigenvalue (p i) (q j) : ℝ) : ℂ) • matrixUnit i j := by
  simp only [relativeLogAction, LinearMap.sub_apply, leftSurprisalMatrix, rightSurprisalMatrix,
    leftAction_apply, rightAction_apply]
  rw [diagonal_mul_matrixUnit, matrixUnit_mul_diagonal]
  unfold relativeLogEigenvalue
  ext a b
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    simp [matrixUnit, ha, hb] <;> ring

end InfoGeometry.OperatorAlgebra.FiniteRelativeModularLogBridge
