import InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Singular.Drazin

/-!
# Native Drazin defect of the off-diagonal ell grading

The tripotent operator `ellGrading = (1/2) ad_lUnit` is its own index-one
Drazin inverse.  Consequently its Drazin support is `T²`, while the
complementary Drazin defect projector is exactly the native trifactor
projector `flowZero`.  Its range is therefore the actual kernel of `T`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllNativeDrazinDefect

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
open InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
open InfoGeometry.Singular.Drazin

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

/-- The native tripotent is its own Drazin inverse. -/
theorem ellGrading_isDrazinInverse :
    IsDrazinInverse ellGrading ellGrading 1 := by
  refine IsDrazinInverse.mk ?_ rfl ?_
  · simpa [pow_three] using ellGrading_tripotent
  · simpa [pow_two, pow_three] using ellGrading_tripotent.symm

/-- Native Drazin support projector `P_D = T Tᴰ = T²`. -/
def ellNativeDrazinProjector : EndCZ :=
  Drazin_Projector ellGrading ellGrading 1 ellGrading_isDrazinInverse

/-- Complementary Drazin defect projector. -/
def ellNativeDrazinDefect : EndCZ := 1 - ellNativeDrazinProjector

theorem ellNativeDrazinProjector_eq_square :
    ellNativeDrazinProjector = ellGrading * ellGrading := rfl

/-- Drazin support is the sum of the two active trifactor sectors. -/
theorem ellNativeDrazinProjector_eq_flowPlus_add_flowMinus :
    ellNativeDrazinProjector = flowPlus + flowMinus := by
  rw [ellNativeDrazinProjector_eq_square]
  unfold flowPlus flowMinus
  exact (InfoGeometry.Physics.Algebra.projPos_add_projNeg
    (T := ellGrading)).symm

/-- The complementary Drazin projector is exactly `P₀`. -/
theorem ellNativeDrazinDefect_eq_flowZero :
    ellNativeDrazinDefect = flowZero := rfl

/-- The Drazin defect space is the genuine stationary kernel. -/
theorem ellNativeDrazinDefect_range_eq_ker :
    LinearMap.range ellNativeDrazinDefect = LinearMap.ker ellGrading := by
  rw [ellNativeDrazinDefect_eq_flowZero]
  exact flow_zero_range_eq_ker

/-- The native grading annihilates its Drazin defect projector. -/
theorem ellGrading_mul_ellNativeDrazinDefect :
    ellGrading * ellNativeDrazinDefect = 0 := by
  rw [ellNativeDrazinDefect_eq_flowZero]
  exact flow_zero_annihilated

end InfoGeometry.Lie.SplitOctonionEllNativeDrazinDefect
