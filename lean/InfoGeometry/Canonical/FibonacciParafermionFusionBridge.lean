import InfoGeometry.Canonical.FibonacciParafermionAtoms
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/-!
# InfoGeometry.Canonical.FibonacciParafermionFusionBridge

Theorem-only bridge between the real finite atom presentation in
`FibonacciParafermionAtoms` and the complex four-anyon matrix presentation in
`FiniteFibonacciFusionMatrix`.

This file adds no wrappers or packets.  It only identifies the explicit matrix
surfaces after coefficient extension `ℝ → ℂ`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.FibonacciParafermionFusionBridge

open Matrix
open FibonacciParafermionAtoms
open FiniteFibonacciFusionMatrix

/-- The real two-channel atom `F_matrix` is the real-coefficient specialization of the complex fusion matrix. -/
theorem ofReal_F_matrix (a b : ℝ) :
    Matrix.map (F_matrix a b) Complex.ofRealHom = fibonacciFusionMatrix (a : ℂ) (b : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [F_matrix, fibonacciFusionMatrix]

/-- The real diagonal braid atom is the real-coefficient specialization of the complex `R` matrix. -/
theorem ofReal_R_matrix (q : Units ℝ) :
    Matrix.map (R_matrix (q : ℝ)) Complex.ofRealHom =
      fibonacciRMatrix (Units.map Complex.ofRealHom.toMonoidHom q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R_matrix, fibonacciRMatrix]
  all_goals rfl

/-- The real dual-basis braid atom `B = F R F` is the real-coefficient specialization of the complex middle-generator matrix. -/
theorem ofReal_B_matrix (a b : ℝ) (q : Units ℝ) :
    Matrix.map (B_matrix a b (q : ℝ)) Complex.ofRealHom =
      fibonacciBMatrix (Units.map Complex.ofRealHom.toMonoidHom q) (a : ℂ) (b : ℂ) := by
  simp [B_matrix, fibonacciBMatrix, Matrix.map_mul, ofReal_F_matrix, ofReal_R_matrix, mul_assoc]

/-- The real Fibonacci relation implied by the standard complex four-anyon scalar constraints. -/
theorem real_IsFibonacciRelation_of_complex_constraints
    {a b : ℝ} (hb : b ^ 2 = a) (ha : a ^ 2 + a = 1) :
    IsFibonacciRelation a b := by
  unfold IsFibonacciRelation
  calc
    a ^ 2 + b ^ 2 = a ^ 2 + a := by rw [hb]
    _ = 1 := ha

/-- Under the standard scalar constraints, the real involutive `F`-matrix agrees with the complex four-anyon involution. -/
theorem ofReal_F_matrix_sq
    {a b : ℝ} (hb : b ^ 2 = a) (ha : a ^ 2 + a = 1) :
    Matrix.map (F_matrix a b * F_matrix a b) Complex.ofRealHom =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.map_mul, ofReal_F_matrix]
  have hbC : ((b : ℂ) ^ 2) = (a : ℂ) := by
    exact_mod_cast hb
  have haC : ((a : ℂ) ^ 2) + (a : ℂ) = 1 := by
    exact_mod_cast ha
  simpa using fibonacciFusionMatrix_sq (τ := (a : ℂ)) (s := (b : ℂ)) hbC haC

end InfoGeometry.Canonical.FibonacciParafermionFusionBridge
