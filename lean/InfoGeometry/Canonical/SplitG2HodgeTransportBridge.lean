import InfoGeometry.Canonical.G2HolonomyGaugeConnections
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitG2HodgeDualFourForm

namespace InfoGeometry.Canonical

/-!
# Hodge-dual transport bridge for the finite split-`G₂` owner

This file deliberately keeps the Hodge operator as explicit data.  A
`SplitG2Automorphism` preserves the algebraic three-form, but preservation of a
chosen Hodge operator is an additional compatibility property.  Under that
property the associated four-form is transported invariantly.
-/

abbrev SplitG2Form (k : ℕ) :=
  AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin k)

/-- Pullback of an alternating form along a linear endomorphism. -/
noncomputable def pullbackForm (k : ℕ)
    (f : imaginarySplitOctonion →ₗ[ℚ] imaginarySplitOctonion)
    (ω : SplitG2Form k) : SplitG2Form k :=
  ω.compLinearMap f

@[simp] theorem pullbackForm_apply (k : ℕ)
    (f : imaginarySplitOctonion →ₗ[ℚ] imaginarySplitOctonion)
    (ω : SplitG2Form k) (v : Fin k → imaginarySplitOctonion) :
    pullbackForm k f ω v = ω (fun i => f (v i)) := by
  rfl

/-- A finite automorphism together with compatibility with the chosen Hodge
dual on three-forms. -/
structure SplitG2HodgeCompatibleAutomorphism
    (H : SplitG2HodgeDualData) where
  automorphism : SplitG2Automorphism
  star34_compatible :
    ∀ φ : SplitG2ThreeForms,
      pullbackForm 4 automorphism.toLinearEquiv
          (H.star34 φ) =
        H.star34 (pullbackForm 3 automorphism.toLinearEquiv φ)

namespace SplitG2HodgeCompatibleAutomorphism

def coassociativeFourForm
    (H : SplitG2HodgeDualData) (φ : SplitG2ThreeForms) :
    SplitG2FourForms :=
  H.star34 φ

theorem coassociativeFourForm_eq_hodgeStar
    (H : SplitG2HodgeDualData) (φ : SplitG2ThreeForms) :
    coassociativeFourForm H φ = H.star34 φ := rfl

theorem preserves_coassociativeFourForm
    (C : SplitG2HodgeCompatibleAutomorphism H)
    (φ : SplitG2ThreeForms)
    (hφ : pullbackForm 3 C.automorphism.toLinearEquiv φ = φ) :
    pullbackForm 4 C.automorphism.toLinearEquiv
        (coassociativeFourForm H φ) =
      coassociativeFourForm H φ := by
  rw [coassociativeFourForm, C.star34_compatible]
  rw [hφ]

theorem transport_preserves_threeForm
    (C : SplitG2HodgeCompatibleAutomorphism H)
    (φ : SplitG2ThreeForms)
    (hφ : pullbackForm 3 C.automorphism.toLinearEquiv φ = φ) :
    pullbackForm 3 C.automorphism.toLinearEquiv φ = φ := hφ

end SplitG2HodgeCompatibleAutomorphism

end InfoGeometry.Canonical
