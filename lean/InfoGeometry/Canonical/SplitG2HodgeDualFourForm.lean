import InfoGeometry.Canonical.SplitG2StructureOnImaginaryOctonions
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

namespace InfoGeometry.Canonical

/-!
# Explicit Hodge-dual data for the split `G₂` carrier

The imaginary split-octonion carrier already supplies the finite rational
vector space and a trilinear property.  A Hodge star is additional data: it
requires a metric, orientation, and degree reversal.  This owner therefore
uses Mathlib's `AlternatingMap` carriers and packages the degree `3 ↔ 4`
dual as a native `LinearEquiv`.  It does not claim that an arbitrary such
equivalence is the canonical Hodge star of a smooth `G₂` manifold.
-/

abbrev SplitG2ThreeForms :=
  AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin 3)

abbrev SplitG2FourForms :=
  AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin 4)

/-- Explicit degree-reversing Hodge data on the finite rational carrier. -/
abbrev SplitG2HodgeDualData :=
  SplitG2ThreeForms ≃ₗ[ℚ] SplitG2FourForms

namespace SplitG2HodgeDualData

abbrev star (H : SplitG2HodgeDualData) :
    SplitG2ThreeForms ≃ₗ[ℚ] SplitG2FourForms := H

end SplitG2HodgeDualData

theorem finrank_threeForms_eq_finrank_fourForms
    (H : SplitG2HodgeDualData) :
    Module.finrank ℚ SplitG2ThreeForms =
      Module.finrank ℚ SplitG2FourForms :=
  H.star.finrank_eq

namespace SplitG2HodgeDualData

/-- The degree `3 → 4` component of the native linear equivalence. -/
def star34 (H : SplitG2HodgeDualData) :
    SplitG2ThreeForms →ₗ[ℚ] SplitG2FourForms :=
  H.star.toLinearMap

/-- The inverse degree `4 → 3` component of the native linear equivalence. -/
def star43 (H : SplitG2HodgeDualData) :
    SplitG2FourForms →ₗ[ℚ] SplitG2ThreeForms :=
  H.star.symm.toLinearMap

def coassociativeFourForm
    (H : SplitG2HodgeDualData) (φ : SplitG2ThreeForms) :
    SplitG2FourForms :=
  H.star34 φ

theorem star43_star34
    (H : SplitG2HodgeDualData) (φ : SplitG2ThreeForms) :
    H.star43 (H.star34 φ) = φ := by
  simpa [star43, star34] using H.star.symm_apply_apply φ

theorem star34_star43
    (H : SplitG2HodgeDualData) (ψ : SplitG2FourForms) :
    H.star34 (H.star43 ψ) = ψ := by
  simpa [star43, star34] using H.star.apply_symm_apply ψ

theorem coassociativeFourForm_recovered
    (H : SplitG2HodgeDualData) (φ : SplitG2ThreeForms) :
    H.star43 (coassociativeFourForm H φ) = φ := by
  exact star43_star34 H φ

end SplitG2HodgeDualData

end InfoGeometry.Canonical
