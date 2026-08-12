import InfoGeometry.OperatorAlgebra.FiniteRelativeModularOperator

/-!
# Finite relative modular logarithmic bridge

This owner stays on the faithful diagonal matrix-unit basis.  It defines the
left/right surprisal action directly and proves its eigenvalue formula.  No
general matrix logarithm or Tomita--Takesaki functional calculus is claimed.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteRelativeModularLogBridge

open InfoGeometry.OperatorAlgebra.FiniteRelativeModularOperator
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

noncomputable def leftSurprisalMatrix {n : ℕ} (p : Fin n → ℝ) : MatrixCarrier n :=
  Matrix.diagonal (fun i => ((-Real.log (p i) : ℝ) : ℂ))

noncomputable def rightSurprisalMatrix {n : ℕ} (q : Fin n → ℝ) : MatrixCarrier n :=
  Matrix.diagonal (fun j => ((-Real.log (q j) : ℝ) : ℂ))

noncomputable def relativeLogAction {n : ℕ} (p q : Fin n → ℝ) : EndCarrier n :=
  leftAction (R := ℂ) (leftSurprisalMatrix p) -
    rightAction (R := ℂ) (rightSurprisalMatrix q)

theorem diagonal_mul_matrixUnit {n : ℕ} (d : Fin n → ℂ) (i j : Fin n) :
    Matrix.diagonal d * Matrix.single i j 1 =
      d i • Matrix.single i j 1 := by
  ext a b
  by_cases ha : a = i
  · subst a
    simp [Matrix.diagonal_mul, Matrix.single]
  · have hia : ¬ i = a := fun h => ha h.symm
    simp [Matrix.diagonal_mul, Matrix.single, hia]

theorem matrixUnit_mul_diagonal {n : ℕ} (d : Fin n → ℂ) (i j : Fin n) :
    Matrix.single i j 1 * Matrix.diagonal d =
      d j • Matrix.single i j 1 := by
  ext a b
  by_cases hb : b = j
  · subst b
    simp [Matrix.mul_diagonal, Matrix.single]
  · have hjb : ¬ j = b := fun h => hb h.symm
    simp [Matrix.mul_diagonal, Matrix.single, hjb]

theorem leftSurprisalAction_matrixUnit
    {n : ℕ} (p : Fin n → ℝ) (i j : Fin n) :
    leftAction (R := ℂ) (leftSurprisalMatrix p) (matrixUnit i j) =
      ((-Real.log (p i) : ℝ) : ℂ) • matrixUnit i j := by
  unfold leftAction leftSurprisalMatrix
  simpa only [LinearMap.mulLeft_apply] using
    (diagonal_mul_matrixUnit
      (fun i => ((-Real.log (p i) : ℝ) : ℂ)) i j)

theorem rightSurprisalAction_matrixUnit
    {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) :
    rightAction (R := ℂ) (rightSurprisalMatrix q) (matrixUnit i j) =
      ((-Real.log (q j) : ℝ) : ℂ) • matrixUnit i j := by
  unfold rightAction rightSurprisalMatrix
  simpa only [LinearMap.mulRight_apply] using
    (matrixUnit_mul_diagonal
      (fun j => ((-Real.log (q j) : ℝ) : ℂ)) i j)

theorem relativeLogAction_eq_leftRightSurprisal
    {n : ℕ} (p q : Fin n → ℝ) :
    relativeLogAction p q =
      leftAction (R := ℂ) (leftSurprisalMatrix p) -
        rightAction (R := ℂ) (rightSurprisalMatrix q) := rfl

theorem relativeLogAction_matrixUnit
    {n : ℕ} (p q : Fin n → ℝ) (i j : Fin n) :
    relativeLogAction p q (matrixUnit i j) =
      ((relativeLogEigenvalue (p i) (q j) : ℝ) : ℂ) • matrixUnit i j := by
  unfold relativeLogAction leftSurprisalMatrix rightSurprisalMatrix
  change (Matrix.diagonal (fun i => ((-Real.log (p i) : ℝ) : ℂ)) *
      matrixUnit i j) -
      (matrixUnit i j * Matrix.diagonal (fun j => ((-Real.log (q j) : ℝ) : ℂ))) = _
  unfold matrixUnit
  rw [diagonal_mul_matrixUnit, matrixUnit_mul_diagonal]
  unfold relativeLogEigenvalue
  ext a b
  by_cases hia : i = a <;> by_cases hjb : j = b <;>
    simp [Matrix.single, hia, hjb]

end InfoGeometry.OperatorAlgebra.FiniteRelativeModularLogBridge
