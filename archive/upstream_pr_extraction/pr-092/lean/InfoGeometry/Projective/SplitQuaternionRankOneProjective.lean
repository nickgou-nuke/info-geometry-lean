import InfoGeometry.Algebra.SplitQuaternionMatrices
import InfoGeometry.Projective.MobiusLoxodromicSpectralParameter
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Rank-one projective readout of the split-quaternion slice

This file keeps the real split-quaternion matrix packet and its complex
projective readout separate.  The real matrices give the Cartan/root
relations; the existing complex Möbius owner supplies the affine `ℂP¹`
action.  No identification of the real carrier with `ℂP¹` is assumed.
-/

namespace InfoGeometry.Projective.SplitQuaternionRankOneProjective

noncomputable section

open InfoGeometry.Algebra.SplitQuaternionMatrices
open InfoGeometry.Projective.MobiusLoxodromicSpectralParameter

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

def axis : M2R := sqK

def rootPlus : M2R := (1 / 2 : ℝ) • (sqJ + sqI)

def rootMinus : M2R := (1 / 2 : ℝ) • (sqJ - sqI)

theorem axis_eq_diagonal :
    axis = !![(1 : ℝ), 0; 0, -1] := by
  simp [axis, sqK]

theorem rootPlus_eq_matrix :
    rootPlus = !![(0 : ℝ), 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rootPlus, sqI, sqJ]

theorem rootMinus_eq_matrix :
    rootMinus = !![(0 : ℝ), 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rootMinus, sqI, sqJ]

theorem rootPlus_sq_zero : rootPlus * rootPlus = (0 : M2R) := by
  rw [rootPlus_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axis, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootMinus_sq_zero : rootMinus * rootMinus = (0 : M2R) := by
  rw [rootMinus_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem axis_rootPlus_commutator :
    axis * rootPlus - rootPlus * axis = (2 : ℝ) • rootPlus := by
  rw [axis_eq_diagonal, rootPlus_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem axis_rootMinus_commutator :
    axis * rootMinus - rootMinus * axis = (-2 : ℝ) • rootMinus := by
  rw [axis_eq_diagonal, rootMinus_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem rootPlus_rootMinus_products :
    rootPlus * rootMinus = (1 / 2 : ℝ) • ((1 : M2R) + axis) := by
  change rootPlus * rootMinus = (1 / 2 : ℝ) • ((1 : M2R) + sqK)
  rw [rootPlus_eq_matrix, rootMinus_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axis, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootMinus_rootPlus_products :
    rootMinus * rootPlus = (1 / 2 : ℝ) • ((1 : M2R) - axis) := by
  change rootMinus * rootPlus = (1 / 2 : ℝ) • ((1 : M2R) - sqK)
  rw [rootPlus_eq_matrix, rootMinus_eq_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axis, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem root_commutator :
    rootPlus * rootMinus - rootMinus * rootPlus = axis := by
  change rootPlus * rootMinus - rootMinus * rootPlus = sqK
  rw [rootPlus_rootMinus_products, rootMinus_rootPlus_products]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axis, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem root_anticommutator :
    rootPlus * rootMinus + rootMinus * rootPlus = (1 : M2R) := by
  rw [rootPlus_rootMinus_products, rootMinus_rootPlus_products]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axis, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem root_rank_one_packet :
    rootPlus * rootPlus = 0 ∧
      rootMinus * rootMinus = 0 ∧
      axis * rootPlus - rootPlus * axis = (2 : ℝ) • rootPlus ∧
      axis * rootMinus - rootMinus * axis = (-2 : ℝ) • rootMinus ∧
      rootPlus * rootMinus - rootMinus * rootPlus = axis :=
  ⟨rootPlus_sq_zero, rootMinus_sq_zero, axis_rootPlus_commutator,
    axis_rootMinus_commutator, root_commutator⟩

theorem rootPlus_is_splitQuaternion_combination :
    rootPlus = (1 / 2 : ℝ) • sqJ + (1 / 2 : ℝ) • sqI := by
  unfold rootPlus
  module

theorem rootMinus_is_splitQuaternion_combination :
    rootMinus = (1 / 2 : ℝ) • sqJ - (1 / 2 : ℝ) • sqI := by
  unfold rootMinus
  module

theorem complex_projective_flow_action (t : ℝ) (z : ℂ) :
    projectiveAction (asMobius (-(t : ℂ) / 2)) z = Complex.exp (-(t : ℂ)) * z := by
  rw [asMobius_action]
  congr 1
  ring

theorem complex_projective_flow_fixes_zero (t : ℝ) :
    projectiveAction (asMobius (-(t : ℂ) / 2)) 0 = 0 := by
  simp [complex_projective_flow_action]

end
end InfoGeometry.Projective.SplitQuaternionRankOneProjective
