import InfoGeometry.Canonical.SplitG2DiscreteCalibration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.G2HolonomyGaugeConnections

namespace InfoGeometry.Canonical

/-!
# Finite curvature data for split-`G₂` transport

This file packages the discrete flatness predicate for a connection: every
chosen triangle has identity split-`G₂` curvature.  It does not identify this
finite predicate with smooth vanishing curvature or a manifold holonomy
theorem.
-/

structure SplitG2DiscreteCurvatureData (E : Type*) where
  connection : SplitG2GaugeConnection E
  flat_triangle : ∀ e₁ e₂ e₃ : E,
    curvature connection e₁ e₂ e₃ = SplitG2Automorphism.id

namespace SplitG2DiscreteCurvatureData

theorem flat_triangle_apply
    {E : Type*} (C : SplitG2DiscreteCurvatureData E)
    (e₁ e₂ e₃ : E) (x : imaginarySplitOctonion) :
    curvature C.connection e₁ e₂ e₃ x = x := by
  rw [C.flat_triangle e₁ e₂ e₃]
  rfl

theorem flat_triangle_preserves_threeForm
    {E : Type*} (C : SplitG2DiscreteCurvatureData E)
    (e₁ e₂ e₃ : E) (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (curvature C.connection e₁ e₂ e₃ x)
        (curvature C.connection e₁ e₂ e₃ y)
        (curvature C.connection e₁ e₂ e₃ z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact curvature_preserves_threeForm C.connection e₁ e₂ e₃ x y z

end SplitG2DiscreteCurvatureData

end InfoGeometry.Canonical
