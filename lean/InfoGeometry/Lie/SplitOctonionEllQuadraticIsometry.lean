import InfoGeometry.Lie.SplitOctonionEllClosedFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionErlangenInvariant

/-!
# Quadratic isometry of the projector-derived ell flow

This owner reuses the canonical quadratic map built from the native Zorn
determinant.  It promotes the already proved determinant preservation of the
closed `ell` flow to Mathlib's genuine `QuadraticMap.IsometryEquiv` API.
No multiplication-preservation or `G₂` claim is made.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllQuadraticIsometry

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.SplitOctonionErlangenInvariant

abbrev CZ := CanonicalZorn

/-- The closed projector-derived `ell` flow as a quadratic isometry of the
native determinant form. -/
def ellFlowPhiQuadraticIsometry (t : ℝ) :
    canonicalDetQuadratic.IsometryEquiv canonicalDetQuadratic :=
  { ellFlowPhiEquiv t with
    map_app' := fun X => by
      exact ellFlowPhi_preserves_det t X }

@[simp] theorem ellFlowPhiQuadraticIsometry_apply (t : ℝ) (X : CZ) :
    ellFlowPhiQuadraticIsometry t X = ellFlowPhi t X :=
  rfl

@[simp] theorem ellFlowPhiQuadraticIsometry_preserves_form
    (t : ℝ) (X : CZ) :
    canonicalDetQuadratic (ellFlowPhiQuadraticIsometry t X) =
      canonicalDetQuadratic X := by
  exact QuadraticMap.IsometryEquiv.map_app
    (ellFlowPhiQuadraticIsometry t) X

theorem ellFlowPhiQuadraticIsometry_preserves_det
    (t : ℝ) (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (ellFlowPhiQuadraticIsometry t X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X := by
  simpa [ellFlowPhiQuadraticIsometry_apply] using
    (ellFlowPhi_preserves_det t X)

end InfoGeometry.Lie.SplitOctonionEllQuadraticIsometry
