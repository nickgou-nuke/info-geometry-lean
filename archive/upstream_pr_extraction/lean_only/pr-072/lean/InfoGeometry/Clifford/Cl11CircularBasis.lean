import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import InfoGeometry.Clifford.Cl11SheetDiracMatrices

noncomputable section

namespace InfoGeometry.Clifford

variable {B : Type*} [Ring B]

section Hyperbolic

variable [Algebra ℚ B]

/-- The hyperbolic/Witt eigenprojectors for the causal basis. -/
def p_plus : Matrix (Fin 2) (Fin 2) B :=
  !![(1 / 2 : ℚ) • 1, (1 / 2 : ℚ) • 1;
     (1 / 2 : ℚ) • 1, (1 / 2 : ℚ) • 1]

def p_minus : Matrix (Fin 2) (Fin 2) B :=
  !![(1 / 2 : ℚ) • 1, -(1 / 2 : ℚ) • 1;
     -(1 / 2 : ℚ) • 1, (1 / 2 : ℚ) • 1]

macro "hyperbolic_ring" : tactic => `(tactic| {
  simp [p_plus, p_minus, I_mat, Matrix.mul_apply, Algebra.smul_def, ← map_mul, ← map_add, ← map_sub, ← map_neg, map_zero, map_one]
  try congr 1
  try ring_nf
  try norm_num
  try ring
})

@[simp]
theorem p_plus_sq : p_plus (B := B) * p_plus = p_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> hyperbolic_ring

@[simp]
theorem p_minus_sq : p_minus (B := B) * p_minus = p_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> hyperbolic_ring

@[simp]
theorem p_plus_mul_p_minus : p_plus (B := B) * p_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> hyperbolic_ring

theorem p_plus_add_p_minus : p_plus (B := B) + p_minus = I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> hyperbolic_ring

end Hyperbolic

section Circular

variable [Algebra ℂ B]

/-- The circular/helicity eigenprojectors for the relative phase axis K. -/
def c_plus : Matrix (Fin 2) (Fin 2) B :=
  !![(1 / 2 : ℂ) • 1, -(Complex.I / 2 : ℂ) • 1;
     (Complex.I / 2 : ℂ) • 1, (1 / 2 : ℂ) • 1]

def c_minus : Matrix (Fin 2) (Fin 2) B :=
  !![(1 / 2 : ℂ) • 1, (Complex.I / 2 : ℂ) • 1;
     -(Complex.I / 2 : ℂ) • 1, (1 / 2 : ℂ) • 1]

macro "complex_ring" : tactic => `(tactic| {
  simp [c_plus, c_minus, I_mat, Matrix.mul_apply, Algebra.smul_def, ← map_mul, ← map_add, ← map_sub, ← map_neg, map_zero, map_one]
  try congr 1
  try ring_nf
  try simp [Complex.I_sq]
  try ring
})

@[simp]
theorem c_plus_sq : c_plus (B := B) * c_plus = c_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> complex_ring

@[simp]
theorem c_minus_sq : c_minus (B := B) * c_minus = c_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> complex_ring

@[simp]
theorem c_plus_mul_c_minus : c_plus (B := B) * c_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> complex_ring

theorem c_plus_add_c_minus : c_plus (B := B) + c_minus = I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> complex_ring

end Circular

end InfoGeometry.Clifford
