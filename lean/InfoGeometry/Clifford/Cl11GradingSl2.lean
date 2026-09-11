import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitQuaternionMatrixModel
import InfoGeometry.Physics.ParabolicClock
import Mathlib.Algebra.Lie.OfAssociative

open scoped Matrix

namespace InfoGeometry.Clifford.Cl11GradingSl2

noncomputable section

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.SplitQuaternionMatrixModel

def E : Matrix (Fin 2) (Fin 2) ℝ := splitNilpotentPlus

def F : Matrix (Fin 2) (Fin 2) ℝ := splitNilpotentMinus

def H : Matrix (Fin 2) (Fin 2) ℝ :=
  splitIdempotentPlus - splitIdempotentMinus

theorem E_sq : E * E = 0 := by
  exact splitNilpotentPlus_sq

theorem F_sq : F * F = 0 := by
  exact splitNilpotentMinus_sq

theorem bracket_H_E : ⁅H, E⁆ = (2 : ℝ) • E := by
  rw [Ring.lie_def]
  simp only [H, E, splitNilpotents_explicit, splitIdempotents_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem bracket_H_F : ⁅H, F⁆ = (-2 : ℝ) • F := by
  rw [Ring.lie_def]
  simp only [H, F, splitNilpotents_explicit, splitIdempotents_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem bracket_E_F : ⁅E, F⁆ = H := by
  rw [Ring.lie_def]
  simp only [H, E, F, splitNilpotents_explicit, splitIdempotents_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num

theorem parabolicSL2Triple :
    ⁅H, E⁆ = (2 : ℝ) • E ∧
      ⁅H, F⁆ = (-2 : ℝ) • F ∧
      ⁅E, F⁆ = H := by
  exact ⟨bracket_H_E, bracket_H_F, bracket_E_F⟩

noncomputable def clE : CliffordAlgebra q11 :=
  cl11EquivMat.symm E

noncomputable def clF : CliffordAlgebra q11 :=
  cl11EquivMat.symm F

noncomputable def clH : CliffordAlgebra q11 :=
  cl11EquivMat.symm H

theorem cl_bracket_H_E : ⁅clH, clE⁆ = (2 : ℝ) • clE := by
  apply cl11EquivMat.injective
  change cl11EquivMat (clH * clE - clE * clH) = _
  simpa only [clH, clE, map_sub, map_mul, map_smul,
    AlgEquiv.apply_symm_apply] using bracket_H_E

theorem cl_bracket_H_F : ⁅clH, clF⁆ = (-2 : ℝ) • clF := by
  apply cl11EquivMat.injective
  change cl11EquivMat (clH * clF - clF * clH) = _
  simpa only [clH, clF, map_sub, map_mul, map_smul,
    AlgEquiv.apply_symm_apply] using bracket_H_F

theorem cl_bracket_E_F : ⁅clE, clF⁆ = clH := by
  apply cl11EquivMat.injective
  change cl11EquivMat (clE * clF - clF * clE) = _
  simpa only [clE, clF, clH, map_sub, map_mul,
    AlgEquiv.apply_symm_apply] using bracket_E_F

theorem cl11ParabolicSL2Triple :
    ⁅clH, clE⁆ = (2 : ℝ) • clE ∧
      ⁅clH, clF⁆ = (-2 : ℝ) • clF ∧
      ⁅clE, clF⁆ = clH := by
  exact ⟨cl_bracket_H_E, cl_bracket_H_F, cl_bracket_E_F⟩

theorem parabolicClock_eq_E :
    InfoGeometry.Physics.K (R := ℝ) = E := by
  simpa [InfoGeometry.Physics.K, E, splitNilpotentPlus] using
    (InfoGeometry.Clifford.SplitQ11CausalCone.matrix_causal_nulls_explicit).1.symm

theorem clE_maps_to_parabolicClock :
    cl11EquivMat clE = InfoGeometry.Physics.K (R := ℝ) := by
  rw [parabolicClock_eq_E]
  simp [clE]

end

end InfoGeometry.Clifford.Cl11GradingSl2
