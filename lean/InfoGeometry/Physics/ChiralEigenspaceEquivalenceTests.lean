import InfoGeometry.Physics.ChiralEigenspaceEquivalence
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

namespace InfoGeometry.Physics.ChiralEigenspaceEquivalenceTests

open ChiralEigenspaceEquivalence InfoGeometry.Clifford.Cl11Matrix

abbrev massEnd (mass : ℝ) : Module.End ℝ (Fin 2 → ℝ) :=
  (diracOperator mass).mulVecLin
abbrev gradeEnd : Module.End ℝ (Fin 2 → ℝ) :=
  (chiralGrading : BdGBlock ℝ).mulVecLin

theorem grading_involution : gradeEnd.comp gradeEnd = LinearMap.id := by
  rw [gradeEnd, ← Matrix.mulVecLin_mul, chiralGrading_sq, Matrix.mulVecLin_one]

theorem mass_odd (mass : ℝ) :
    (massEnd mass).comp gradeEnd = -(gradeEnd.comp (massEnd mass)) := by
  apply LinearMap.ext
  intro vector
  funext coordinate
  fin_cases coordinate <;>
    simp [massEnd, gradeEnd, diracOperator, chiralGrading,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem positive_eigenvector (mass : ℝ) :
    (massEnd mass).HasEigenvector mass ![1, 1] := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · ext coordinate
    fin_cases coordinate <;>
      simp [massEnd, diracOperator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro hequal
    have hfirst := congrFun hequal 0
    norm_num at hfirst

example (mass : ℝ) : (massEnd mass).HasEigenvector (-mass) (gradeEnd ![1, 1]) :=
  map_hasEigenvector _ _ (mass_odd mass) grading_involution (positive_eigenvector mass)

example (mass value : ℝ) :
    (massEnd mass).HasEigenvalue value ↔ (massEnd mass).HasEigenvalue (-value) :=
  hasEigenvalue_iff_neg _ _ (mass_odd mass) grading_involution value

example (mass value : ℝ) (depth : ℕ∞) :
    Module.finrank ℝ ((massEnd mass).genEigenspace value depth) =
      Module.finrank ℝ ((massEnd mass).genEigenspace (-value) depth) :=
  genEigenspace_finrank_eq _ _ (mass_odd mass) grading_involution value depth

theorem mass_kernel_of_nonzero (mass : ℝ) (hnonzero : mass ≠ 0) :
    LinearMap.ker (massEnd mass) = ⊥ := by
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro vector hzero
  have hfirst := congrFun hzero 0
  have hsecond := congrFun hzero 1
  simp [diracOperator, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hfirst hsecond
  ext coordinate
  fin_cases coordinate
  · exact hsecond.resolve_left hnonzero
  · exact hfirst.resolve_left hnonzero

theorem zero_mass_kernel : LinearMap.ker (massEnd 0) = ⊤ := by
  ext vector
  simp [massEnd, diracOperator, dotProduct, Fin.sum_univ_two,
    funext_iff, Fin.forall_fin_two]

theorem mass_commutes_with_proposed_time_reversal_iff (mass : ℝ) :
    diracOperator mass * (-Eminus) = (-Eminus) * diracOperator mass ↔ mass = 0 := by
  constructor
  · intro hequal
    have hentry := congrArg (fun matrix : Mat2 => matrix 0 0) hequal
    simp [diracOperator, Eminus, Matrix.mul_apply, Fin.sum_univ_two] at hentry
    linarith
  · rintro rfl
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [diracOperator, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

theorem mass_anticommutes_with_proposed_particle_hole_iff (mass : ℝ) :
    diracOperator mass * J1 = -(J1 * diracOperator mass) ↔ mass = 0 := by
  constructor
  · intro hequal
    have hentry := congrArg (fun matrix : Mat2 => matrix 0 0) hequal
    simp [diracOperator, J1, Matrix.mul_apply, Fin.sum_univ_two] at hentry
    linarith
  · rintro rfl
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [diracOperator, J1, Matrix.mul_apply, Fin.sum_univ_two]

example (mass : ℝ) :
    chiralGrading * star (diracOperator mass) * chiralGrading = -diracOperator mass :=
  dirac_krein_adjoint mass

#print axioms genEigenspaceEquiv
#print axioms hasEigenvalue_iff_neg
#print axioms dirac_krein_adjoint
#print axioms mass_kernel_of_nonzero
#print axioms mass_commutes_with_proposed_time_reversal_iff
#print axioms mass_anticommutes_with_proposed_particle_hole_iff

end InfoGeometry.Physics.ChiralEigenspaceEquivalenceTests
