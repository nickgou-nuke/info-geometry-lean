import InfoGeometry.Algebra.MatrixCyclotomics
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

namespace InfoGeometry.Algebra.ParabolicJordanZorn

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.GrandUnification.Matrix2KANPauliChain
open InfoGeometry.Algebra.MatrixCyclotomics

abbrev Vec2 := Fin 2 → ℝ

def firstBasisVector : Vec2 := ![1, 0]

def shearEnd (parameter : ℝ) : Module.End ℝ Vec2 := (NPart parameter).mulVecLin

theorem firstBasisVector_ne_zero : firstBasisVector ≠ 0 := by
  intro hequal
  have hentry := congrFun hequal 0
  norm_num [firstBasisVector] at hentry

theorem shear_exact_index_two (parameter : ℝ) (hnonzero : parameter ≠ 0) :
    (NPart parameter - 1) ^ 2 = 0 ∧ NPart parameter - 1 ≠ 0 := by
  refine ⟨shear_unipotent parameter, ?_⟩
  intro hequal
  exact hnonzero ((NPart_eq_one_iff parameter).mp (sub_eq_zero.mp hequal))

theorem fixed_iff_second_coordinate_zero (parameter : ℝ) (hnonzero : parameter ≠ 0)
    (vector : Vec2) : shearEnd parameter vector = vector ↔ vector 1 = 0 := by
  constructor
  · intro hequal
    have hfirst := congrFun hequal 0
    simp [shearEnd, Matrix.mulVecLin_apply, NPart, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at hfirst
    have hproduct : parameter * vector 1 = 0 := by linarith
    exact (mul_eq_zero.mp hproduct).resolve_left hnonzero
  · intro hsecond
    ext index
    fin_cases index <;>
      simp [shearEnd, Matrix.mulVecLin_apply, NPart, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, hsecond]

theorem eigenspace_one (parameter : ℝ) (hnonzero : parameter ≠ 0) :
    (shearEnd parameter).eigenspace 1 = Submodule.span ℝ {firstBasisVector} := by
  ext vector
  rw [Module.End.mem_eigenspace_iff, one_smul,
    fixed_iff_second_coordinate_zero parameter hnonzero, Submodule.mem_span_singleton]
  constructor
  · intro hsecond
    refine ⟨vector 0, ?_⟩
    ext index
    fin_cases index <;> simp [firstBasisVector, hsecond]
  · rintro ⟨coefficient, hequal⟩
    have hsecond := congrFun hequal 1
    simpa [firstBasisVector] using hsecond.symm

theorem eigenspace_one_finrank (parameter : ℝ) (hnonzero : parameter ≠ 0) :
    Module.finrank ℝ ((shearEnd parameter).eigenspace 1) = 1 := by
  rw [eigenspace_one parameter hnonzero]
  exact finrank_span_singleton firstBasisVector_ne_zero

theorem eigenvalue_eq_one (parameter eigenvalue : ℝ) (vector : Vec2)
    (hvector : vector ≠ 0) (heigen : shearEnd parameter vector = eigenvalue • vector) :
    eigenvalue = 1 := by
  by_contra hvalue
  have hfirst := congrFun heigen 0
  have hsecond := congrFun heigen 1
  simp [shearEnd, Matrix.mulVecLin_apply, NPart, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at hfirst hsecond
  have hfactor : 1 - eigenvalue ≠ 0 := sub_ne_zero.mpr (Ne.symm hvalue)
  have hsecond_zero : vector 1 = 0 := by
    have hproduct : (1 - eigenvalue) * vector 1 = 0 := by nlinarith
    exact (mul_eq_zero.mp hproduct).resolve_left hfactor
  have hfirst_zero : vector 0 = 0 := by
    have hproduct : (1 - eigenvalue) * vector 0 = 0 := by
      rw [hsecond_zero] at hfirst
      nlinarith
    exact (mul_eq_zero.mp hproduct).resolve_left hfactor
  apply hvector
  ext index
  fin_cases index <;> assumption

theorem hasEigenvector_iff (parameter eigenvalue : ℝ) (vector : Vec2) :
    (shearEnd parameter).HasEigenvector eigenvalue vector ↔
      eigenvalue = 1 ∧ shearEnd parameter vector = vector ∧ vector ≠ 0 := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨heigen, hvector⟩
    have hvalue := eigenvalue_eq_one parameter eigenvalue vector hvector heigen
    exact ⟨hvalue, by simpa [hvalue] using heigen, hvector⟩
  · rintro ⟨rfl, hfixed, hvector⟩
    exact ⟨by simpa using hfixed, hvector⟩

theorem firstBasisVector_eigenvector (parameter : ℝ) :
    (shearEnd parameter).HasEigenvector 1 firstBasisVector := by
  rw [hasEigenvector_iff]
  refine ⟨rfl, ?_, firstBasisVector_ne_zero⟩
  ext index
  fin_cases index <;>
    simp [shearEnd, Matrix.mulVecLin_apply, NPart, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, firstBasisVector]

theorem not_similar_to_diagonal (parameter : ℝ) (hnonzero : parameter ≠ 0) :
    ¬ ∃ (basisMatrix : Mat2) (entries : Fin 2 → ℝ),
      basisMatrix.det ≠ 0 ∧
        NPart parameter * basisMatrix = basisMatrix * Matrix.diagonal entries := by
  rintro ⟨basisMatrix, entries, hdet, hequal⟩
  have hbottom : ∀ column, basisMatrix 1 column = 0 := by
    intro column
    let vector : Vec2 := fun row => basisMatrix row column
    have hvector : vector ≠ 0 := by
      intro hzero
      have hfirst := congrFun hzero 0
      have hsecond := congrFun hzero 1
      apply hdet
      fin_cases column <;>
        simp_all [vector, Matrix.det_fin_two]
    have heigen : shearEnd parameter vector = entries column • vector := by
      ext row
      have hentry := congrArg (fun matrix : Mat2 => matrix row column) hequal
      simpa [shearEnd, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Matrix.mul_apply, Matrix.diagonal, vector] using hentry
    have hvalue := eigenvalue_eq_one parameter (entries column) vector hvector heigen
    have hfixed : shearEnd parameter vector = vector := by simpa [hvalue] using heigen
    exact (fixed_iff_second_coordinate_zero parameter hnonzero vector).mp hfixed
  apply hdet
  simp [Matrix.det_fin_two, hbottom]

theorem shear_add (first second : ℝ) : NPart first * NPart second = NPart (first + second) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [NPart, Matrix.mul_apply, Fin.sum_univ_two]

theorem shear_pow (parameter : ℝ) (exponent : ℕ) :
    NPart parameter ^ exponent = NPart ((exponent : ℝ) * parameter) := by
  induction exponent with
  | zero =>
      ext row column
      fin_cases row <;> fin_cases column <;> simp [NPart]
  | succ exponent hinduction =>
      rw [pow_succ, hinduction, shear_add]
      congr 1
      push_cast
      ring

theorem shear_no_positive_period (parameter : ℝ) (hnonzero : parameter ≠ 0)
    (exponent : ℕ) (hpositive : 0 < exponent) : NPart parameter ^ exponent ≠ 1 := by
  rw [shear_pow, NPart_eq_one_iff]
  exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hpositive)) hnonzero

theorem inverse_parameter_not_transpose (parameter : ℝ) (hnonzero : parameter ≠ 0) :
    NPart (-parameter) ≠ (NPart parameter).transpose := by
  intro hequal
  have hentry := congrArg (fun matrix : Mat2 => matrix 0 1) hequal
  apply hnonzero
  simpa [NPart] using hentry

end InfoGeometry.Algebra.ParabolicJordanZorn
