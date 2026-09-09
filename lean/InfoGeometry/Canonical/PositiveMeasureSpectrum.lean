import InfoGeometry.Canonical.CertifiedModularReduction
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Algebra.Algebra.StrictPositivity
import Mathlib.Analysis.InnerProductSpace.StarOrder

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.Positivity

variable {H₂ : Type*}
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable (c : CertifiedModularReduction (E := H₂))

local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Strict positivity of an operator on the Drazin-regular lane.
-/
@[rep_depth operator]
def IsStrictlyPositiveOnReg (A : H₂ →L[ℝ] H₂) : Prop :=
  ∀ v : H₂, v ≠ 0 → c.Preg v = v → 0 < inner ℝ v (A v)

/--
Concrete spectral-positivity discharge on the owner lane:
if `Δreg` is strictly positive as an ordered algebra element, then every spectral
value is strictly positive.
-/
@[rep_depth operator]
theorem regular_spectrum_positive_of_isStrictlyPositive
    (hStrict : IsStrictlyPositive c.Δreg) :
    c.RegularSpectrumPositive := by
  intro x hx
  exact IsStrictlyPositive.spectrum_pos (A := EndH) (𝕜 := ℝ) hStrict hx

/--
Concrete functional-calculus closure on the owner lane from strict positivity.
-/
@[rep_depth operator]
theorem log_defined_on_Δreg_of_isStrictlyPositive
    (hStrict : IsStrictlyPositive c.Δreg) :
    c.logAdmissible c.Δreg :=
  c.log_defined_on_Δreg_of_regularSpectrumPositive
    (regular_spectrum_positive_of_isStrictlyPositive (c := c) hStrict)

/--
Owner-certificate surface (no extra ad-hoc discharge classes):
if the repository already provides regular-spectrum positivity, log is admitted
on `Δreg`.
-/
@[rep_depth operator]
theorem log_defined_on_Δreg_of_regularSpectrumPositive
    (hPos : c.RegularSpectrumPositive) :
    c.logAdmissible c.Δreg :=
  c.log_defined_on_Δreg_of_regularSpectrumPositive hPos

end InfoGeometry.Canonical.Positivity
