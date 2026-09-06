import InfoGeometry.Canonical.PositiveMeasureSpectrum
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Canonical.Positivity

variable {H₂ : Type*}
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

@[rep_depth operator]
theorem finiteDiagonalShadowExcluded
    (c : CertifiedModularReduction (E := H₂))
    (hPos : c.RegularSpectrumPositive) :
    c.logAdmissible c.Δreg :=
  log_defined_on_Δreg_of_regularSpectrumPositive (c := c) hPos

@[rep_depth operator]
theorem finiteDiagonalShadowExcluded_of_isStrictlyPositive
    (c : CertifiedModularReduction (E := H₂))
    (hStrict : IsStrictlyPositive c.Δreg) :
    c.logAdmissible c.Δreg :=
  log_defined_on_Δreg_of_isStrictlyPositive (c := c) hStrict

end InfoGeometry.Canonical.Positivity
