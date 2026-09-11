import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl11SheetDiracMatrices

namespace InfoGeometry.Clifford

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-- The Witt annihilation operator (circular basis corresponding to the real Clifford plane). -/
def e_plus : Matrix (Fin 2) (Fin 2) B :=
  !![(1 / 2 : ℚ) • 1, (1 / 2 : ℚ) • 1;
     -(1 / 2 : ℚ) • 1, -(1 / 2 : ℚ) • 1]

/-- The Witt creation operator. -/
def e_minus : Matrix (Fin 2) (Fin 2) B :=
  !![(1 / 2 : ℚ) • 1, -(1 / 2 : ℚ) • 1;
     (1 / 2 : ℚ) • 1, -(1 / 2 : ℚ) • 1]

@[simp]
theorem e_plus_sq : e_plus (B := B) * e_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e_plus, Matrix.mul_apply, Algebra.smul_def, ← map_mul, ← map_add]

@[simp]
theorem e_minus_sq : e_minus (B := B) * e_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e_minus, Matrix.mul_apply, Algebra.smul_def, ← map_mul, ← map_add]

/-- The canonical anticommutation CAR relation. -/
theorem e_plus_mul_e_minus_add_e_minus_mul_e_plus :
    e_plus (B := B) * e_minus + e_minus * e_plus = I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e_plus, e_minus, I_mat, Algebra.smul_def, ← map_mul, ← map_add, ← map_sub, ← map_neg, map_zero, map_one]
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end InfoGeometry.Clifford
