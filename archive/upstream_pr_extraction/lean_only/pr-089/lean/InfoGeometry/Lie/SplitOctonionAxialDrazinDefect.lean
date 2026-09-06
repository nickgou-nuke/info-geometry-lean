import InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
import InfoGeometry.Singular.Drazin

/-!
# Drazin defect of the diagonal split-octonion axial grading

This is the direct ring-level Drazin specialization of the canonical diagonal
Zorn grading.  The Drazin complement is proved equal to the stationary Peirce
projector, whose range was already identified with the grading kernel.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialDrazinDefect

open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
open InfoGeometry.Singular.Drazin
open InfoGeometry.Physics.Algebra

/-- The diagonal axial tripotent is its own index-one Drazin inverse. -/
theorem axialGrading_isDrazinInverse :
    IsDrazinInverse axialGrading axialGrading 1 := by
  refine IsDrazinInverse.mk ?_ rfl ?_
  · simpa [pow_three] using axialGrading_tripotent
  · simpa [pow_one, pow_two, pow_three] using axialGrading_tripotent.symm

/-- The Drazin regular/support projector is the active-sector projector. -/
theorem axial_drazinProjector_eq_active :
    Drazin_Projector axialGrading axialGrading 1
        axialGrading_isDrazinInverse =
      axialPPlus + axialPMinus := by
  change axialGrading * axialGrading =
    projPos axialGrading + projNeg axialGrading
  exact (projPos_add_projNeg (T := axialGrading)).symm

/-- The Drazin complement is exactly the stationary trifactor projector. -/
theorem axial_drazinComplement_eq_PZero :
    1 - Drazin_Projector axialGrading axialGrading 1
        axialGrading_isDrazinInverse = axialPZero := by
  rfl

/-- The Drazin defect subspace is exactly the stationary kernel. -/
theorem axial_drazinDefect_range_eq_ker :
    LinearMap.range
        (1 - Drazin_Projector axialGrading axialGrading 1
          axialGrading_isDrazinInverse) =
      LinearMap.ker axialGrading := by
  rw [axial_drazinComplement_eq_PZero]
  exact axialPZero_range_eq_ker

end InfoGeometry.Lie.SplitOctonionAxialDrazinDefect
