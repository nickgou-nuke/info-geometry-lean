import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorFenchelRegularCone
import InfoGeometry.Canonical.SelfDualWeylRootKleinBridge

/-!
# InfoGeometry.Canonical.FenchelWeylSelfDualKleinBridge

Operator/geometry bridge packet for the finite self-dual + Fenchel + Weyl/Klein stage.

This packet is intentionally thin and explicit: it re-exports selected owner
theorems as stable aliases while keeping the noncommutative affine Weyl/Klein
relation visible at this boundary name.
-/

namespace InfoGeometry.Canonical.FenchelWeylSelfDualKleinBridge

set_option linter.unusedSectionVars false

noncomputable section

open Matrix
open BigOperators
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorFenchelRegularCone
open InfoGeometry.Canonical.SelfDualWeylRootKleinBridge

variable {E : Type 0}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Gate to the operator-cone owner theorem: support is fixed on the regular branch. -/
theorem regularPositiveConeΩD_support
    (c : CertifiedModularReduction (E := H₂))
    {H : EndH}
    (hH : regularPositiveConeOmegaD (E := E) c H) :
    compress c.Preg H = H :=
  InfoGeometry.Canonical.OperatorFenchelRegularCone.regularPositiveConeOmegaD_support
    (c := c) (H := H) hH

/-- Gate to the operator-cone owner theorem: positive spectrum on the regular branch. -/
theorem regularPositiveConeΩD_spectrum_pos
    (c : CertifiedModularReduction (E := H₂))
    {H : EndH}
    (hH : regularPositiveConeOmegaD (E := E) c H) :
    spectrum ℝ H ⊆ Set.Ioi (0 : ℝ) :=
  InfoGeometry.Canonical.OperatorFenchelRegularCone.regularPositiveConeOmegaD_spectrum_pos
    (c := c) (H := H) hH

/-- Gate to the operator-cone owner theorem: Fenchel–Young inequality on Ω_D. -/
theorem operatorFenchelYoung_dual_transport
    (c : CertifiedModularReduction (E := H₂))
    (hPos : c.RegularSpectrumPositive)
    (ω : EndH →L[ℝ] ℝ)
    (ψStar : (EndH →L[ℝ] ℝ) → ℝ)
    (hConj :
      InfoGeometry.Geometry.IsFenchelMajorized
        (operatorFenchelPotentialOnRegularCone (E := E) ω) ψStar)
    (H : EndH)
    (η : EndH →L[ℝ] ℝ)
    (hH : H ∈ regularPositiveConeOmegaD (E := E) c) :
    η H ≤ operatorFenchelPotentialOnRegularCone (E := E) ω H + ψStar η :=
  InfoGeometry.Canonical.OperatorFenchelRegularCone.operatorFenchelYoung_on_doubledKrein
    (E := E) c hPos ω ψStar hConj H η hH

/-- Gate to the operator-cone owner theorem: Legendre inverse Hessian packet. -/
theorem operatorLegendreHessianInverse_packet_operator
    (D : InfoGeometry.Geometry.LegendreContinuousLinearEquivInverseData EndH) :
    D.toLegendreHessianInverseContext.moment =
        InfoGeometry.Geometry.dualCoord D.massieu D.beta
      ∧ D.entropyGradient D.toLegendreHessianInverseContext.moment = D.beta
      ∧ D.toLegendreHessianInverseContext.fisherHessian =
        InfoGeometry.Geometry.hessian D.massieu D.beta
      ∧ D.toLegendreHessianInverseContext.entropyHessian =
        fderiv ℝ D.entropyGradient D.toLegendreHessianInverseContext.moment
      ∧ D.toLegendreHessianInverseContext.entropyHessian.comp
          D.toLegendreHessianInverseContext.fisherHessian =
        ContinuousLinearMap.id ℝ EndH
      ∧ D.toLegendreHessianInverseContext.fisherHessian.comp
          D.toLegendreHessianInverseContext.entropyHessian =
        ContinuousLinearMap.id ℝ (InfoGeometry.Geometry.MomentCoord EndH) :=
  InfoGeometry.Canonical.OperatorFenchelRegularCone.operatorLegendreHessianInverse_packet_of_continuousLinearEquiv
    (E := E) D

/-- Finite Klein/Weyl cocycle inherited from the root/Klein core:
`A W A⁻¹ = W · Bₓ`. -/
theorem kleinBottle_weyl_translation_relation :
    InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinA *
        InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinW *
      InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinA_inv =
      InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinW *
        InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinBx :=
  SelfDualWeylRootKleinBridge.kleinA_conj_kleinW_translation

/-- Reassociated form of the same cocycle:
`A·W = W·Bₓ·A`. -/
theorem kleinBottle_weyl_kleinReassoc :
    InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinA *
        InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinW =
      InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinW *
      InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinBx *
      InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinA :=
  SelfDualWeylRootKleinBridge.kleinA_mul_kleinW_eq_kleinW_mul_kleinBx_mul_kleinA

/-- Explicit non-commutation property kept at this bridge layer. -/
theorem kleinBottle_weyl_noncommute :
    InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinA *
      InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinW ≠
    InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinW *
      InfoGeometry.Canonical.SelfDualWeylRootKleinBridge.kleinA :=
  SelfDualWeylRootKleinBridge.kleinA_kleinW_noncommute

end

end InfoGeometry.Canonical.FenchelWeylSelfDualKleinBridge
