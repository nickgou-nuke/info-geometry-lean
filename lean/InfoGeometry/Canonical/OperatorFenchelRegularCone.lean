import InfoGeometry.Canonical.FiniteDiagonalSpectrumDischarge
import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Canonical.OperatorialUncertainty
import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorFenchelRegularCone

Owner skeleton for operatorial Fenchel/Legendre statements on the doubled real
Krein carrier, explicitly gated by regular-branch positivity.
-/

namespace InfoGeometry.Canonical.OperatorFenchelRegularCone

open InfoGeometry.Canonical.Positivity
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.OperatorialUncertainty
open InfoGeometry.Geometry
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Regular positive operator cone on the Drazin regular block:
`Ω_D = {H | Preg * H * Preg = H ∧ spectrum(H) ⊆ (0,∞)}`.
-/
@[rep_depth operator]
def regularPositiveConeOmegaD
    (c : CertifiedModularReduction (E := H₂)) : Set EndH :=
  {H : EndH | compress (c.Preg) H = H ∧ spectrum ℝ H ⊆ Set.Ioi (0 : ℝ)}

/--
Operatorial Fenchel primal potential on the regular branch.
-/
@[rep_depth operator]
noncomputable def operatorFenchelPotentialOnRegularCone
    (ω : EndH →L[ℝ] ℝ) (H : EndH) : ℝ :=
  operatorMassieuPotential (E := E) ω H 1

/--
Operatorial Fenchel conjugate as the Legendre support supremum on `EndH`.
-/
@[rep_depth operator]
noncomputable def operatorFenchelConjugateOnRegularCone
    (ψ : EndH → ℝ) (η : EndH →L[ℝ] ℝ) : ℝ :=
  InfoGeometry.Geometry.legendre ψ η

/--
Fenchel-Young inequality on the doubled-Krein operator lane.

The positivity hypothesis is the owner gate that certifies `log` admissibility on
`Δreg`; the inequality is then the generic Fenchel statement on the same lane.
-/
@[rep_depth transport, capstone]
theorem operatorFenchelYoung_on_doubledKrein
    (c : CertifiedModularReduction (E := H₂))
    (hPos : c.RegularSpectrumPositive)
    (ω : EndH →L[ℝ] ℝ)
    (ψStar : (EndH →L[ℝ] ℝ) → ℝ)
    (hConj : IsFenchelMajorized (operatorFenchelPotentialOnRegularCone (E := E) ω) ψStar)
    (H : EndH)
    (η : EndH →L[ℝ] ℝ)
    (hH : H ∈ regularPositiveConeOmegaD c) :
    η H ≤ operatorFenchelPotentialOnRegularCone (E := E) ω H + ψStar η := by
  have _hLog : c.logAdmissible c.Δreg :=
    finiteDiagonalShadowExcluded (c := c) hPos
  have _hConeSupport : compress (c.Preg) H = H := hH.1
  have _hConePos : spectrum ℝ H ⊆ Set.Ioi (0 : ℝ) := hH.2
  exact fenchelYoung_ineq (hConj := hConj) H η

/--
Uncertainty bound as the symmetric (Jordan/Hessian) plus phase response split
on the same doubled-Krein lane.
-/
@[rep_depth krein, capstone]
theorem operatorUncertainty_from_hessianJordan
    (comparison : H₂)
    (X Y : EndH)
    (hX : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) X) :
    (InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
      (E := E) comparison X Y) ^ 2
      +
    (InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorPhase
      (E := E) comparison X Y) ^ 2
      ≤
    (InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
      (E := E) comparison X X)
      *
    (InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
      (E := E) comparison Y Y) := by
  exact comparisonStateGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear
    (E := E) comparison X Y hX

end Core

end InfoGeometry.Canonical.OperatorFenchelRegularCone
