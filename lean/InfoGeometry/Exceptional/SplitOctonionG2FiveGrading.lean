import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Contact grading of the native split-octonion derivation carrier

The dependency order is the native Cartan eigenbasis, its integer weight
readout, eigenspaces, dimensions, and homogeneous bracket closure.
The chosen Cartan parameter is `(1,0,-1)`. No Cantor boundary, nuclear
perturbation expansion, or topological defect is identified with this grading.
-/

noncomputable section

namespace InfoGeometry.Exceptional.SplitOctonionG2FiveGrading

open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Carrier := InfoGeometry.Lie.CanonicalZornCartanAdjointAction.Der

def contactCartan : TracelessWeight := tracelessWeightEquiv ![1, 0]

def rootGrade : Fin 14 → ℤ := ![-1, -1, -2, 0, -1, 1, 0, -1, 1, 0, 1, 2, 1, 0]

theorem rootGrade_readout (index : Fin 14) :
    rootWeight index contactCartan = (rootGrade index : ℝ) := by
  have hlast : (![1, 0, -1] : Fin 3 → ℝ) 2 = -1 := rfl
  fin_cases index <;>
    norm_num [rootWeight, coordWeight, contactCartan, tracelessWeightEquiv, rootGrade,
      Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, hlast]

def gradeSpace (degree : ℤ) : Submodule ℝ Carrier :=
  (adCartan contactCartan).eigenspace (degree : ℝ)

theorem mem_gradeSpace_iff (degree : ℤ) (operator : Carrier) :
    operator ∈ gradeSpace degree ↔
      ∀ index, rootGrade index ≠ degree →
        canonicalParameterLinearEquiv.symm operator index = 0 := by
  rw [gradeSpace, Module.End.mem_eigenspace_iff]
  constructor
  · intro heigen index hdegree
    have hcoordinate := congrFun (congrArg canonicalParameterLinearEquiv.symm heigen) index
    have hdiag := adCartanCoordinates_apply_diagonal contactCartan
      (canonicalParameterLinearEquiv.symm operator) index
    simp only [adCartanCoordinates_apply, LinearEquiv.apply_symm_apply] at hdiag
    rw [hdiag] at hcoordinate
    simp only [map_smul, Pi.smul_apply, smul_eq_mul] at hcoordinate
    rw [← rootWeight_eq_adCartanDiagonalCoefficient, rootGrade_readout] at hcoordinate
    have hne : (rootGrade index : ℝ) ≠ (degree : ℝ) := by exact_mod_cast hdegree
    exact (mul_eq_zero.mp (show ((rootGrade index : ℝ) - degree) *
      canonicalParameterLinearEquiv.symm operator index = 0 by
        nlinarith [hcoordinate])).resolve_left (sub_ne_zero.mpr hne)
  · intro hsupport
    apply canonicalParameterLinearEquiv.symm.injective
    rw [map_smul]
    funext index
    have hdiag := adCartanCoordinates_apply_diagonal contactCartan
      (canonicalParameterLinearEquiv.symm operator) index
    simp only [adCartanCoordinates_apply, LinearEquiv.apply_symm_apply] at hdiag
    rw [hdiag]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← rootWeight_eq_adCartanDiagonalCoefficient, rootGrade_readout]
    by_cases hdegree : rootGrade index = degree
    · rw [hdegree]
    · rw [hsupport index hdegree, mul_zero, mul_zero]

def gradeCoordinateEquiv (degree : ℤ) :
    gradeSpace degree ≃ₗ[ℝ] ({index : Fin 14 // rootGrade index = degree} → ℝ) where
  toFun operator index := canonicalParameterLinearEquiv.symm operator.val index.val
  invFun coordinates := ⟨canonicalParameterLinearEquiv
    (fun index => if hdegree : rootGrade index = degree then coordinates ⟨index, hdegree⟩ else 0), by
      rw [mem_gradeSpace_iff]
      intro index hdegree
      simp [hdegree]⟩
  left_inv operator := by
    apply Subtype.ext
    apply canonicalParameterLinearEquiv.symm.injective
    funext index
    simp only [LinearEquiv.symm_apply_apply]
    split_ifs with hdegree
    · rfl
    · exact ((mem_gradeSpace_iff degree operator.val).mp operator.property index hdegree).symm
  right_inv coordinates := by
    funext index
    simp [index.property]
  map_add' first second := by ext index; simp
  map_smul' scalar operator := by ext index; simp

theorem gradeSpace_finrank (degree : ℤ) :
    Module.finrank ℝ (gradeSpace degree) =
      Fintype.card {index : Fin 14 // rootGrade index = degree} := by
  simpa using (gradeCoordinateEquiv degree).finrank_eq

theorem contact_dimensions :
    Module.finrank ℝ (gradeSpace (-2)) = 1 ∧
    Module.finrank ℝ (gradeSpace (-1)) = 4 ∧
    Module.finrank ℝ (gradeSpace 0) = 4 ∧
    Module.finrank ℝ (gradeSpace 1) = 4 ∧
    Module.finrank ℝ (gradeSpace 2) = 1 := by
  simp only [gradeSpace_finrank]
  decide

theorem rootDerivation_mem_gradeSpace (index : Fin 14) :
    rootDerivation index ∈ gradeSpace (rootGrade index) := by
  rw [gradeSpace, Module.End.mem_eigenspace_iff]
  rw [adCartan_rootDerivation, rootGrade_readout]

theorem gradeSpaces_span : (⨆ degree : ℤ, gradeSpace degree) = ⊤ := by
  apply top_unique
  rw [← rootDerivationBasis_span]
  apply Submodule.span_le.mpr
  rintro operator ⟨index, rfl⟩
  rw [rootDerivationBasis_apply]
  exact (le_iSup gradeSpace (rootGrade index)) (rootDerivation_mem_gradeSpace index)

theorem gradeSpaces_independent : iSupIndep gradeSpace :=
  (adCartan contactCartan).eigenspaces_iSupIndep.comp Int.cast_injective

theorem rootGrade_bounds (index : Fin 14) : -2 ≤ rootGrade index ∧ rootGrade index ≤ 2 := by
  fin_cases index <;> norm_num [rootGrade]

theorem gradeSpace_eq_bot (degree : ℤ) (houtside : degree < -2 ∨ 2 < degree) :
    gradeSpace degree = ⊥ := by
  apply le_antisymm _ bot_le
  intro operator hoperator
  change operator = 0
  apply canonicalParameterLinearEquiv.symm.injective
  rw [map_zero]
  funext index
  exact (mem_gradeSpace_iff degree operator).mp hoperator index (by
    have hbounds := rootGrade_bounds index
    omega)

theorem bracket_mem_gradeSpace {firstDegree secondDegree : ℤ} {first second : Carrier}
    (hfirst : first ∈ gradeSpace firstDegree) (hsecond : second ∈ gradeSpace secondDegree) :
    ⁅first, second⁆ ∈ gradeSpace (firstDegree + secondDegree) := by
  rw [gradeSpace, Module.End.mem_eigenspace_iff] at *
  change ⁅(axialCartanLieEquiv contactCartan : Carrier), first⁆ = _ at hfirst
  change ⁅(axialCartanLieEquiv contactCartan : Carrier), second⁆ = _ at hsecond
  change ⁅(axialCartanLieEquiv contactCartan : Carrier), ⁅first, second⁆⁆ = _
  rw [leibniz_lie, hfirst, hsecond]
  rw [smul_lie, lie_smul, Int.cast_add, add_smul]

theorem grade_one_two_truncation {first second : Carrier}
    (hfirst : first ∈ gradeSpace 1) (hsecond : second ∈ gradeSpace 2) :
    ⁅first, second⁆ = 0 := by
  have hbracket := bracket_mem_gradeSpace hfirst hsecond
  norm_num only at hbracket
  rw [gradeSpace_eq_bot 3 (by omega)] at hbracket
  exact hbracket

theorem grade_two_abelian {first second : Carrier}
    (hfirst : first ∈ gradeSpace 2) (hsecond : second ∈ gradeSpace 2) :
    ⁅first, second⁆ = 0 := by
  have hbracket := bracket_mem_gradeSpace hfirst hsecond
  norm_num only at hbracket
  rw [gradeSpace_eq_bot 4 (by omega)] at hbracket
  exact hbracket

/-- Closure of the polarized nested bracket; no Kantor identities are assumed or inferred. -/
theorem polarized_triple_closed {first middle last : Carrier}
    (hfirst : first ∈ gradeSpace 1) (hmiddle : middle ∈ gradeSpace (-1))
    (hlast : last ∈ gradeSpace 1) : ⁅⁅first, middle⁆, last⁆ ∈ gradeSpace 1 := by
  have hbracket := bracket_mem_gradeSpace (bracket_mem_gradeSpace hfirst hmiddle) hlast
  norm_num only at hbracket
  exact hbracket

end InfoGeometry.Exceptional.SplitOctonionG2FiveGrading
