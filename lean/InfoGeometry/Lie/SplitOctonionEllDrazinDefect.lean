import InfoGeometry.Lie.SplitOctonionEllTrifactor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionAxialDrazinDefect
import InfoGeometry.Singular.Drazin

/-!
# Drazin defect of the ell-flow grading

This file specializes the ring-level Drazin equations directly to the native
endomorphism ring of `CanonicalZorn`.  No commutativity wrapper is used.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllDrazinDefect

open InfoGeometry.Lie.SplitOctonionEllTrifactor
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
open InfoGeometry.Lie.SplitOctonionAxialDrazinDefect
open InfoGeometry.Singular.Drazin

abbrev CZ := InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

def ellDrazinInverse : EndCZ := diagEllGrading
def ellDrazinProjector : EndCZ := diagEllGrading * ellDrazinInverse
def ellDrazinNullProjector : EndCZ := 1 - ellDrazinProjector

theorem ell_is_own_drazin_inverse :
    IsDrazinInverse diagEllGrading ellDrazinInverse 1 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · simpa [ellDrazinInverse, pow_three] using diagEllGrading_tripotent
  · rfl
  · simpa [ellDrazinInverse, pow_two, pow_three] using
      diagEllGrading_tripotent.symm

theorem ell_drazin_projector_eq_square :
    ellDrazinProjector = diagEllGrading ^ 2 := by
  apply LinearMap.ext
  intro Z
  change diagEllGrading (diagEllGrading Z) = (diagEllGrading ^ 2) Z
  rfl

/-! The historical `ell` Drazin owner and the native axial Peirce owner use
the same normalized diagonal grading.  Hence their support projectors are
definitionally the same operator after the proved grading bridge. -/
theorem ell_drazin_projector_eq_axial_drazinProjector :
    ellDrazinProjector =
      Drazin_Projector axialGrading axialGrading 1
        axialGrading_isDrazinInverse := by
  rw [ell_drazin_projector_eq_square]
  change diagEllGrading * diagEllGrading = axialGrading * axialGrading
  rw [InfoGeometry.Lie.SplitOctonionEllFlowOperator.diagEllGrading_eq_axialGrading]

/-! The complementary/defect projectors are the same native stationary
Peirce sector as well. -/
theorem ell_drazin_null_projector_eq_axialPZero :
    ellDrazinNullProjector = axialPZero := by
  unfold ellDrazinNullProjector
  rw [ell_drazin_projector_eq_axial_drazinProjector]
  exact axial_drazinComplement_eq_PZero

/-! The old defect projector therefore has the native stationary kernel as its
range, with no appeal to a separately named defect subspace. -/
theorem ell_drazin_null_range_eq_axial_kernel :
    LinearMap.range ellDrazinNullProjector = LinearMap.ker axialGrading := by
  rw [ell_drazin_null_projector_eq_axialPZero]
  exact axialPZero_range_eq_ker

theorem ell_drazin_projector_eq_active_trifactor :
    ellDrazinProjector = ellFlowPPlus + ellFlowPMinus := by
  rw [ell_drazin_projector_eq_square]
  apply LinearMap.ext
  intro Z
  change diagEllGrading (diagEllGrading Z) = _
  rw [diagEllGrading_sq_coord, LinearMap.add_apply,
    ellFlowPPlus_coord, ellFlowPMinus_coord]
  ext <;> simp

theorem ell_drazin_null_projector_eq_P_zero :
    ellDrazinNullProjector = ellFlowPZero := by
  apply LinearMap.ext
  intro Z
  rw [ellFlowPZero_apply]
  change Z - diagEllGrading (diagEllGrading Z) = _
  rfl

theorem ell_drazin_trifactor_capstone :
    IsDrazinInverse diagEllGrading ellDrazinInverse 1 ∧
      ellDrazinProjector = diagEllGrading ^ 2 ∧
      ellDrazinProjector = ellFlowPPlus + ellFlowPMinus ∧
      ellDrazinNullProjector = ellFlowPZero ∧
      diagEllGrading * ellDrazinNullProjector = 0 := by
  refine ⟨ell_is_own_drazin_inverse, ell_drazin_projector_eq_square,
    ell_drazin_projector_eq_active_trifactor,
    ell_drazin_null_projector_eq_P_zero, ?_⟩
  apply LinearMap.ext
  intro Z
  change diagEllGrading (Z - diagEllGrading (diagEllGrading Z)) = 0
  rw [map_sub]
  have h := congrArg (fun F : EndCZ => F Z) diagEllGrading_tripotent
  have h' : diagEllGrading (diagEllGrading (diagEllGrading Z)) =
      diagEllGrading Z := by
    simpa [pow_succ, pow_two, Module.End.mul_apply, LinearMap.comp_apply] using h
  rw [h']
  simp

end InfoGeometry.Lie.SplitOctonionEllDrazinDefect
