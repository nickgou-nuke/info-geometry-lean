import InfoGeometry.Canonical.SplitG2DiscreteHodgeCalibration
import InfoGeometry.Canonical.SplitG2DiscreteCoframePullback
import InfoGeometry.Canonical.SplitG2DiscreteCurvatureWitness

namespace InfoGeometry.Canonical

/-!
# Discrete split-`G₂` forms bundle

This file packages the already verified finite split-`G₂` calibration,
coframe pullback, and flat-curvature property into one topological owner.
It does not introduce a smooth Hodge star or a manifold torsion-free theorem.
-/

/-- Topological bundle for the discrete split-`G₂` layer. -/
structure SplitG2DiscreteForms (E : Type*) (K : FiniteOrientedCellComplex) where
  calibration : SplitG2DiscreteHodgeCalibration K
  coframe : SplitG2DiscreteCoframe K
  curvatureWitness : SplitG2DiscreteCurvatureWitness E

namespace SplitG2DiscreteForms

variable {E : Type*} {K : FiniteOrientedCellComplex}

abbrev connection (D : SplitG2DiscreteForms E K) : SplitG2GaugeConnection E :=
  D.curvatureWitness.connection

abbrev phi (D : SplitG2DiscreteForms E K) : RationalColorCochain K 3 :=
  D.calibration.phi

abbrev psi (D : SplitG2DiscreteForms E K) : RationalColorCochain K 4 :=
  D.calibration.psi

theorem phi_closed (D : SplitG2DiscreteForms E K) :
    rationalCoboundary K 3 (phi D) = 0 :=
  D.calibration.phi_closed

theorem psi_closed (D : SplitG2DiscreteForms E K) :
    rationalCoboundary K 4 (psi D) = 0 :=
  D.calibration.psi_closed

theorem flat_triangle
    (D : SplitG2DiscreteForms E K)
    (e₁ e₂ e₃ : E) :
    curvature D.connection e₁ e₂ e₃ = SplitG2Automorphism.id :=
  D.curvatureWitness.flat_triangle e₁ e₂ e₃

theorem flat_triangle_apply
    (D : SplitG2DiscreteForms E K)
    (e₁ e₂ e₃ : E) (x : imaginarySplitOctonion) :
    curvature D.connection e₁ e₂ e₃ x = x := by
  rw [D.flat_triangle e₁ e₂ e₃]
  rfl

theorem flat_triangle_preserves_threeForm
    (D : SplitG2DiscreteForms E K)
    (e₁ e₂ e₃ : E)
    (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (curvature D.connection e₁ e₂ e₃ x)
        (curvature D.connection e₁ e₂ e₃ y)
        (curvature D.connection e₁ e₂ e₃ z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact D.curvatureWitness.flat_triangle_preserves_threeForm e₁ e₂ e₃ x y z

theorem torsion_free_socket
    (D : SplitG2DiscreteForms E K) :
    rationalCoboundary K 3 (phi D) = 0 ∧
      rationalCoboundary K 4 (psi D) = 0 ∧
      ∀ e₁ e₂ e₃ : E,
        curvature D.connection e₁ e₂ e₃ = SplitG2Automorphism.id :=
  ⟨D.phi_closed, D.psi_closed, D.curvatureWitness.flat_triangle⟩

end SplitG2DiscreteForms

end InfoGeometry.Canonical
