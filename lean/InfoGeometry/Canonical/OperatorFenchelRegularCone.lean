import InfoGeometry.Canonical.FiniteDiagonalSpectrumDischarge
import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Canonical.OperatorialUncertainty
import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Geometry.LegendreHessianInverse
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorFenchelRegularCone

Owner skeleton for operatorial Fenchel/Legendre statements on the doubled real
Krein carrier, explicitly gated by regular-branch positivity.
-/

set_option linter.unusedSectionVars false

namespace OperatorFenchelRegularCone

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

`Ω_D = {H | Preg H Preg = H ∧ spectrum(H) ⊆ (0,∞)}`.

The first condition says the operator lives entirely on the Drazin regular
branch. The second condition is the spectral positivity gate needed for
operatorial logarithmic/Legendre analysis.
-/
@[rep_depth operator]
def regularPositiveConeOmegaD
    (c : CertifiedModularReduction (E := H₂)) : Set EndH :=
  {H : EndH | compress (c.Preg) H = H ∧ spectrum ℝ H ⊆ Set.Ioi (0 : ℝ)}

/-- Membership in the Drazin regular positive cone, unfolded. -/
@[simp]
theorem mem_regularPositiveConeOmegaD_iff
    (c : CertifiedModularReduction (E := H₂))
    (H : EndH) :
    H ∈ regularPositiveConeOmegaD c ↔
      compress c.Preg H = H ∧ spectrum ℝ H ⊆ Set.Ioi (0 : ℝ) :=
  Iff.rfl

/-- Operators in `Ω_D` are supported on the Drazin regular block. -/
theorem regularPositiveConeOmegaD_support
    {c : CertifiedModularReduction (E := H₂)}
    {H : EndH}
    (hH : H ∈ regularPositiveConeOmegaD c) :
    compress c.Preg H = H :=
  hH.1

/-- Operators in `Ω_D` have strictly positive spectrum. -/
theorem regularPositiveConeOmegaD_spectrum_pos
    {c : CertifiedModularReduction (E := H₂)}
    {H : EndH}
    (hH : H ∈ regularPositiveConeOmegaD c) :
    spectrum ℝ H ⊆ Set.Ioi (0 : ℝ) :=
  hH.2

/--
Operatorial Fenchel primal potential on the regular branch.
-/
@[rep_depth operator]
noncomputable def operatorFenchelPotentialOnRegularCone
    (ω : EndH →L[ℝ] ℝ) (H : EndH) : ℝ :=
  operatorMassieuPotential (E := E) ω H (1 : ℝ)

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
  -- Regular modular block is log-admissible.
  have _hLog : c.logAdmissible c.Δreg :=
    finiteDiagonalShadowExcluded (c := c) hPos
  -- The test operator is supported on the Drazin regular block.
  have _hConeSupport : compress c.Preg H = H :=
    regularPositiveConeOmegaD_support hH
  -- The test operator has strictly positive spectrum.
  have _hConePos : spectrum ℝ H ⊆ Set.Ioi (0 : ℝ) :=
    regularPositiveConeOmegaD_spectrum_pos hH
  exact fenchelYoung_ineq (hConj := hConj) H η

/--
Constructive operatorial Legendre inverse packet on the doubled-Krein lane.

This is the operator-lifted, dimension-agnostic replacement for scalar
inverse-Hessian prose: the inverse laws are carried by a continuous-linear
equivalence witness on `EndH`, not by ad hoc scalar assumptions.
-/
@[rep_depth thermo]
theorem operatorLegendreHessianInverse_packet_of_continuousLinearEquiv
    (D : LegendreContinuousLinearEquivInverseData EndH) :
    D.toLegendreHessianInverseContext.moment =
        dualCoord D.massieu D.beta
      ∧ D.entropyGradient D.toLegendreHessianInverseContext.moment = D.beta
      ∧ D.toLegendreHessianInverseContext.fisherHessian =
        hessian D.massieu D.beta
      ∧ D.toLegendreHessianInverseContext.entropyHessian =
        fderiv ℝ D.entropyGradient D.toLegendreHessianInverseContext.moment
      ∧ D.toLegendreHessianInverseContext.entropyHessian.comp
          D.toLegendreHessianInverseContext.fisherHessian =
        ContinuousLinearMap.id ℝ EndH
      ∧ D.toLegendreHessianInverseContext.fisherHessian.comp
          D.toLegendreHessianInverseContext.entropyHessian =
        ContinuousLinearMap.id ℝ (MomentCoord EndH) := by
  exact D.constructive_legendre_hessian_inverse_packet

/--
Operator-lane inverse law: entropy Hessian composed with Fisher Hessian is
identity on `EndH`.
-/
@[rep_depth thermo]
theorem operatorEntropyHessian_comp_operatorFisherHessian_eq_id_of_continuousLinearEquiv
    (D : LegendreContinuousLinearEquivInverseData EndH) :
    D.toLegendreHessianInverseContext.entropyHessian.comp
        D.toLegendreHessianInverseContext.fisherHessian =
      ContinuousLinearMap.id ℝ EndH := by
  exact D.toLegendreHessianInverseContext.entropyHessian_comp_fisherHessian

/--
Operator-lane inverse law: Fisher Hessian composed with entropy Hessian is
identity on the operator moment-coordinate space.
-/
@[rep_depth thermo]
theorem operatorFisherHessian_comp_operatorEntropyHessian_eq_id_of_continuousLinearEquiv
    (D : LegendreContinuousLinearEquivInverseData EndH) :
    D.toLegendreHessianInverseContext.fisherHessian.comp
        D.toLegendreHessianInverseContext.entropyHessian =
      ContinuousLinearMap.id ℝ (MomentCoord EndH) := by
  exact D.toLegendreHessianInverseContext.fisherHessian_comp_entropyHessian

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

end OperatorFenchelRegularCone
