import Mathlib

/-!
# InfoGeometry.Canonical.SharpAngleDivergenceOperators

Conservative Lean surface for sharp sector-angle bounds of divergence-form
operators with complex coefficients.

This file does not implement PDE regularity machinery. It records the
operator-level inequality interface needed downstream:

`|Im t(u,u)| ≤ κ * Re t(u,u)`.

The intended sharp choice is `κ = tan α`, where `α` comes from the localized
coefficient bound.
-/

namespace SharpAngleDivergenceOperators

open Real

universe u v

/--
Localized coefficient-angle data (`κ(x)`), together with its global sharp bound.
-/
structure CoefficientAngleDatum (Ω : Type u) where
  kappaAt : Ω → ℝ
  sharpKappa : ℝ
  kappa_le_sharp : ∀ x : Ω, kappaAt x ≤ sharpKappa
  sharp_nonneg : 0 ≤ sharpKappa

/--
Abstract sesquilinear-form interface for the sectorial estimate on the diagonal.
-/
structure SectorFormDatum (V : Type v) where
  form : V → V → ℂ
  kappa : ℝ
  kappa_nonneg : 0 ≤ kappa
  diag_sector_bound : ∀ u : V, |(form u u).im| ≤ kappa * (form u u).re

namespace SectorFormDatum

variable {V : Type v} (D : SectorFormDatum V)

/-- Direct readback: diagonal numerical range satisfies the sector bound. -/
theorem abs_im_diag_le_kappa_mul_re_diag (u : V) :
    |(D.form u u).im| ≤ D.kappa * (D.form u u).re :=
  D.diag_sector_bound u

/--
If `κ = tan α`, the diagonal numerical range lies in the angle-`α` sector
witnessed by the standard `|Im z| ≤ tan α * Re z` inequality.
-/
theorem abs_im_diag_le_tan_mul_re_diag
    {α : ℝ} (hκ : D.kappa = Real.tan α) (u : V) :
    |(D.form u u).im| ≤ Real.tan α * (D.form u u).re := by
  simpa [hκ] using D.diag_sector_bound u

end SectorFormDatum

/--
Transfer wrapper: instantiate a form-sector bound using a coefficient sharp
constant `sharpKappa`.
-/
structure DivergenceSharpAnglePacket (Ω : Type u) (V : Type v) where
  coeff : CoefficientAngleDatum Ω
  formData : SectorFormDatum V
  uses_sharp_constant : formData.kappa = coeff.sharpKappa

namespace DivergenceSharpAnglePacket

variable {Ω : Type u} {V : Type v} (P : DivergenceSharpAnglePacket Ω V)

/-- Readback theorem: the form sector bound is controlled by the sharp coefficient bound. -/
theorem abs_im_diag_le_sharp_mul_re_diag (u : V) :
    |(P.formData.form u u).im| ≤ P.coeff.sharpKappa * (P.formData.form u u).re := by
  simpa [P.uses_sharp_constant] using P.formData.diag_sector_bound u

end DivergenceSharpAnglePacket

end SharpAngleDivergenceOperators
