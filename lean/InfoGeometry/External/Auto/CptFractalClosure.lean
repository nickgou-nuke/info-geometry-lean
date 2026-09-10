import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# CPT light-cone nilpotent atoms

Two concrete `2×2` light-cone generators are square-zero, and the diagonal
scale generator acts with opposite weights.
-/

namespace CptFractalClosure

open Matrix Complex

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Forward light-cone nilpotent. -/
def n_plus : M2C := !![0, 1; 0, 0]

/-- Backward light-cone nilpotent. -/
def n_minus : M2C := !![0, 0; 1, 0]

/-- Diagonal scale/CPT grading generator. -/
def D_gen : M2C := !![1, 0; 0, -1]

/-- `n₊²=0`. -/
theorem light_cone_nilpotent_plus : n_plus * n_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [n_plus, Matrix.mul_apply]

/-- `n₋²=0`. -/
theorem light_cone_nilpotent_minus : n_minus * n_minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [n_minus, Matrix.mul_apply]

/-- The scale generator gives weight `+2` on `n₊` by commutator. -/
theorem conformal_scale_plus : D_gen * n_plus - n_plus * D_gen = (2 : ℂ) • n_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [D_gen, n_plus, Matrix.mul_apply]

/-- The scale generator gives weight `-2` on `n₋` by commutator. -/
theorem conformal_scale_minus : D_gen * n_minus - n_minus * D_gen = (-2 : ℂ) • n_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [D_gen, n_minus, Matrix.mul_apply]

/-- Consolidated finite CPT light-cone identities. -/
theorem cpt_light_cone_identities :
    n_plus * n_plus = 0 ∧ n_minus * n_minus = 0 ∧
    D_gen * n_plus - n_plus * D_gen = (2 : ℂ) • n_plus ∧
    D_gen * n_minus - n_minus * D_gen = (-2 : ℂ) • n_minus := by
  constructor
  · exact light_cone_nilpotent_plus
  constructor
  · exact light_cone_nilpotent_minus
  constructor
  · exact conformal_scale_plus
  · exact conformal_scale_minus

end CptFractalClosure
