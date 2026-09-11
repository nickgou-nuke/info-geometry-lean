import InfoGeometry.Lie.SplitOctonionAxialClosedFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionAxialDrazinDefect

/-!
# Active-support grading of the diagonal axial tripotent

For the concrete tripotent `T = axialGrading`, this owner separates the two
operator gradings that are easy to conflate:

* `T` has signed weights `-1, 0, +1`;
* `Q = T²` records active support versus the stationary Drazin defect;
* `Γ = 2Q - I` is the corresponding involution.

All identities are proved in `Module.End ℝ (ZornMatrix ℝ)` and identified with
the already established Peirce and Drazin projectors.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialSupportGrading

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor
open InfoGeometry.Lie.SplitOctonionAxialDrazinDefect
open InfoGeometry.Singular.Drazin

abbrev CZ := ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- The active-support projector `Q = T²`. -/
def axialActiveSupport : EndCZ := axialGrading * axialGrading

/-- The active/defect involution `Γ = 2T² - I`. -/
def axialActiveDefectInvolution : EndCZ :=
  (2 : ℝ) • axialActiveSupport - 1

@[simp] theorem axialActiveSupport_apply (X : CZ) :
    axialActiveSupport X = { a := 0, b := 0, x := X.x, y := X.y } := by
  ext i <;> simp [axialActiveSupport, axialGrading, Module.End.mul_apply]

@[simp] theorem axialActiveDefectInvolution_apply (X : CZ) :
    axialActiveDefectInvolution X =
      { a := -X.a, b := -X.b, x := X.x, y := X.y } := by
  ext i <;>
    simp [axialActiveDefectInvolution, axialActiveSupport_apply,
      Equiv.smul_def, coordEquiv] <;> ring

/-- `Q` is exactly the native Drazin support projector. -/
theorem axialActiveSupport_eq_drazinProjector :
    axialActiveSupport =
      Drazin_Projector axialGrading axialGrading 1
        axialGrading_isDrazinInverse := by
  rfl

/-- `Q` is the sum of the two signed active Peirce sectors. -/
theorem axialActiveSupport_eq_PPlus_add_PMinus :
    axialActiveSupport = axialPPlus + axialPMinus := by
  rw [axialActiveSupport_eq_drazinProjector]
  exact axial_drazinProjector_eq_active

/-- The complement of `Q` is precisely the stationary/Drazin-defect
projector. -/
theorem one_sub_axialActiveSupport_eq_PZero :
    1 - axialActiveSupport = axialPZero := by
  rw [axialActiveSupport_eq_drazinProjector]
  exact axial_drazinComplement_eq_PZero

/-- The active support is idempotent. -/
theorem axialActiveSupport_idempotent :
    axialActiveSupport * axialActiveSupport = axialActiveSupport := by
  apply LinearMap.ext
  intro X
  ext i <;> simp [Module.End.mul_apply]

/-- The active/defect grading is a genuine involution. -/
theorem axialActiveDefectInvolution_sq :
    axialActiveDefectInvolution * axialActiveDefectInvolution = 1 := by
  apply LinearMap.ext
  intro X
  ext i <;> simp [Module.End.mul_apply]

/-- `Γ` acts by `-1` on the stationary Drazin-defect sector. -/
theorem axialActiveDefectInvolution_on_PZero (X : CZ) :
    axialActiveDefectInvolution (axialPZero X) = -axialPZero X := by
  rw [axialPZero_apply, axialActiveDefectInvolution_apply]
  ext i <;> simp

/-- `Γ` acts by `+1` on the positive active sector. -/
theorem axialActiveDefectInvolution_on_PPlus (X : CZ) :
    axialActiveDefectInvolution (axialPPlus X) = axialPPlus X := by
  rw [axialPPlus_apply, colorProject_apply,
    axialActiveDefectInvolution_apply]
  ext i <;> simp

/-- `Γ` acts by `+1` on the negative active sector. -/
theorem axialActiveDefectInvolution_on_PMinus (X : CZ) :
    axialActiveDefectInvolution (axialPMinus X) = axialPMinus X := by
  rw [axialPMinus_apply, anticolorProject_apply,
    axialActiveDefectInvolution_apply]
  ext i <;> simp

end InfoGeometry.Lie.SplitOctonionAxialSupportGrading
