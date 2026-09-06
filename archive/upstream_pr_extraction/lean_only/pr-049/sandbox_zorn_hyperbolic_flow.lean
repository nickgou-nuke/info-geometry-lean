import InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
import InfoGeometry.Lie.SplitOctonionCircularNormCone

open InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
open InfoGeometry.Lie.SplitOctonionCircularNormCone
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Algebra.Zorn.ZornMatrix
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

noncomputable section

abbrev CZ := CanonicalZorn

/-- The hyperbolic exponential flow on CanonicalZorn, pulled back from circular coordinates. -/
def hyperbolicFlowZorn (t : ℝ) : CanonicalZorn →ₗ[ℝ] CanonicalZorn :=
  circularPeirceBasis.equivFun.symm.toLinearMap.comp
    ((hyperbolicFlowCoordinate t).comp circularPeirceBasis.equivFun.toLinearMap)

theorem hyperbolicFlowZorn_apply (t : ℝ) (X : CanonicalZorn) :
    hyperbolicFlowZorn t X =
      circularPeirceBasis.equivFun.symm (hyperbolicFlowCoordinate t (circularPeirceBasis.equivFun X)) := rfl

/-- The hyperbolic flow on CanonicalZorn preserves the zero-norm cone (and the full norm). -/
theorem hyperbolicFlowZorn_preserves_norm (t : ℝ) (X : CanonicalZorn) :
    detZ (hyperbolicFlowZorn t X) = detZ X := by
  have h1 (Y : CanonicalZorn) : detZ Y = circularNormQuad (circularPeirceBasis.equivFun Y) := by
    rw [circularNorm_eq Y, circularPeirceBasis_coordinate_eq_equivFun Y]
    rfl
  rw [h1, h1]
  have h2 : circularPeirceBasis.equivFun (hyperbolicFlowZorn t X) =
      hyperbolicFlowCoordinate t (circularPeirceBasis.equivFun X) := by
    rw [hyperbolicFlowZorn_apply]
    simp
  rw [h2]
  exact circularNormQuad_hyperbolicFlow t (circularPeirceBasis.equivFun X)

