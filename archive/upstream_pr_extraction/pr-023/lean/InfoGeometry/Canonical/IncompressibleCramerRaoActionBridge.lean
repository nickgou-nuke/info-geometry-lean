import InfoGeometry.Canonical.ConformalAnomalySource
import InfoGeometry.Canonical.IncompressibleBitBridge
import InfoGeometry.Canonical.MongeAmpereCramerRao
import InfoGeometry.Canonical.WeylKKTAnomalyIdentity

/-!
# InfoGeometry.Canonical.IncompressibleCramerRaoActionBridge

Dimension-agnostic bridge from the operatorial Souriau-Fisher/Cramer-Rao
metric to the conformal normal/unit-of-action lane.

The redline sign convention is explicit:

`anomaly scale = Kähler/RN potential = - log(relative volume mode)`.

The metric is the primary operatorial datum. For the ordinary Hessian/
Cramer-Rao scalar shadow, the relative-volume mode is `|det(g_CR)|`. In
super/chiral settings this determinant shadow should be replaced by the
Berezinian/super-Berezinian owner surface, not silently reused. This file proves
the ordinary shadow bridge and keeps the readout equality as explicit data.

The dilation/Goldstone channel is not a new scalar charge here: it is the
existing Weyl/KKT chiral-scale readout. Once the operatorial metric-volume
potential forces `χ = 0`, the already-owned conformal/Weyl theorems collapse the
projector obstruction and the dilation commutator.
-/

namespace InfoGeometry.Canonical.IncompressibleCramerRaoActionBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.MongeAmpereCramerRao
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.IncompressibleBitBridge
open InfoGeometry.Canonical.WeylKKTAnomalyIdentity

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The Souriau-Fisher/Cramer-Rao metric as an operatorial readout.

This is the primary object in this bridge. Determinants and logarithms below are
scalar volume-potential shadows of this operator, not replacements for it.
-/
@[rep_depth operator]
noncomputable abbrev souriauFisherMetricOperator
    (H : HessianGeometry E) (x : E) : E →L[ℝ] E :=
  cramerRaoMetricOp H x

/--
The scalar volume shadow of the operatorial Souriau-Fisher metric.

This ordinary determinant readout is only the Hessian/Cramer-Rao shadow. The
super/chiral replacement point is the Berezinian/super-Berezinian owner lane.
-/
@[rep_depth krein]
noncomputable def souriauFisherMetricVolumeShadow
    (H : HessianGeometry E) (x : E) : ℝ :=
  |LinearMap.det (souriauFisherMetricOperator H x).toLinearMap|

/--
The Kähler/RN-style potential shadow: negative log relative metric volume.
-/
@[rep_depth transport]
noncomputable def souriauFisherMetricVolumePotential
    (H : HessianGeometry E) (x : E) : ℝ :=
  -Real.log (souriauFisherMetricVolumeShadow H x)

/--
The named operatorial Souriau-Fisher readout reduces to the repo's Cramer-Rao
metric operator owner.
-/
@[rep_depth operator]
theorem souriauFisherMetricOperator_eq_cramerRaoMetricOp
    (H : HessianGeometry E) (x : E) :
    souriauFisherMetricOperator H x = cramerRaoMetricOp H x :=
  rfl

/--
Readout identifying the conformal anomaly scale with the negative log-volume
potential shadow of the operatorial Souriau-Fisher metric.

The carrier `E` is arbitrary. This is explicit bridge data; it prevents the
false theorem "incompressibility alone implies normality".
-/
@[rep_depth transport]
structure CramerRaoNegLogVolumeAnomalyReadout
    (CI : ConformalInference E) (H : HessianGeometry E) where
  chiralScale_eq_metricVolumePotential :
    ∀ x : E, CI.chiralScale = souriauFisherMetricVolumePotential H x

namespace CramerRaoNegLogVolumeAnomalyReadout

variable {CI : ConformalInference E} {H : HessianGeometry E}

/--
Incompressibility kills the conformal anomaly scale when the anomaly readout is
the negative Cramer-Rao log-volume mode.
-/
@[rep_depth transport, capstone]
theorem chiralScale_eq_zero_of_incompressible
    (R : CramerRaoNegLogVolumeAnomalyReadout CI H)
    (hIncomp : IncompressibleMongeAmpere H) (x : E) :
    CI.chiralScale = 0 := by
  have bit : IncompressibleCramerRaoBit H :=
    incompressibleCramerRaoBit_of_incompressible hIncomp
  have hScalePotential :
      CI.chiralScale = cramerRaoVolumePotential H x := by
    simpa [souriauFisherMetricVolumePotential, souriauFisherMetricVolumeShadow,
      souriauFisherMetricOperator, cramerRaoVolumePotential, cramerRaoVolumeShadow,
      IncompressibleBitBridge.cramerRaoMetricOperatorOwner] using
        CramerRaoNegLogVolumeAnomalyReadout.chiralScale_eq_metricVolumePotential R x
  have hPotentialZero : cramerRaoVolumePotential H x = 0 :=
    cramerRaoVolumePotential_eq_zero_of_incompressibleBit (H := H) bit x
  calc
    CI.chiralScale = cramerRaoVolumePotential H x := hScalePotential
    _ = 0 := hPotentialZero

/--
The same readout constructively yields the normal conformal phase.
-/
@[rep_depth thermo, capstone]
theorem normalInference_of_incompressible
    (R : CramerRaoNegLogVolumeAnomalyReadout CI H)
    (hIncomp : IncompressibleMongeAmpere H) (x : E) :
    CI.IsNormalInference := by
  have bit : IncompressibleCramerRaoBit H :=
    incompressibleCramerRaoBit_of_incompressible hIncomp
  have hScalePotential :
      CI.chiralScale = cramerRaoVolumePotential H x := by
    simpa [souriauFisherMetricVolumePotential, souriauFisherMetricVolumeShadow,
      souriauFisherMetricOperator, cramerRaoVolumePotential, cramerRaoVolumeShadow,
      IncompressibleBitBridge.cramerRaoMetricOperatorOwner] using
        CramerRaoNegLogVolumeAnomalyReadout.chiralScale_eq_metricVolumePotential R x
  exact isNormalInference_of_incompressibleBit_of_chiralScale_eq_cramerRaoVolumePotential
    (CI := CI) (H := H) bit x hScalePotential

/--
Compatibility projection to the operator-owner incompressible-bit theorem.

The bit theorem remains the owner lane; this readout simply transports the
negative-log-volume calibration through the Souriau-Fisher metric shadow.
-/
@[rep_depth thermo, capstone]
theorem isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume
    (R : CramerRaoNegLogVolumeAnomalyReadout CI H)
    (bit : IncompressibleCramerRaoBit H)
    (x : E) :
    CI.IsNormalInference := by
  have hScale :
      CI.chiralScale =
        -Real.log (|LinearMap.det (cramerRaoMetricOp H x).toLinearMap|) := by
    simpa [souriauFisherMetricVolumePotential, souriauFisherMetricVolumeShadow,
      souriauFisherMetricOperator, cramerRaoVolumePotential, cramerRaoVolumeShadow,
      IncompressibleBitBridge.cramerRaoMetricOperatorOwner] using
        CramerRaoNegLogVolumeAnomalyReadout.chiralScale_eq_metricVolumePotential R x
  exact
    IncompressibleBitBridge.isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume
        (CI := CI) (H := H) bit x hScale

/--
The same readout identifies the conformal unit of action with the negative
Cramer-Rao log-volume mode.

This is the manuscript-facing equality
`unit of action = anomaly scale = -log |det(g_CR)|`, with `g_CR` still carried
by the operatorial Souriau-Fisher metric owner.
-/
@[rep_depth transport]
theorem unitOfAction_eq_metricVolumePotential
    (R : CramerRaoNegLogVolumeAnomalyReadout CI H) (x : E) :
    CI.unitOfAction = souriauFisherMetricVolumePotential H x := by
  calc
    CI.unitOfAction = CI.chiralScale := CI.unitOfAction_eq_chiralScale
    _ = souriauFisherMetricVolumePotential H x :=
      CramerRaoNegLogVolumeAnomalyReadout.chiralScale_eq_metricVolumePotential R x

/--
The Weyl/KKT epsilon readout is the same negative Cramer-Rao log-volume mode
under the explicit anomaly readout.
-/
@[rep_depth transport]
theorem epsilon_eq_metricVolumePotential
    (R : CramerRaoNegLogVolumeAnomalyReadout CI H) (x : E) :
    CI.epsilon = souriauFisherMetricVolumePotential H x := by
  calc
    CI.epsilon = CI.chiralScale := by
      exact (ConformalInference.chiralScale_eq_epsilon (CI := CI)).symm
    _ = souriauFisherMetricVolumePotential H x :=
      CramerRaoNegLogVolumeAnomalyReadout.chiralScale_eq_metricVolumePotential R x

/--
Readout packet: chiral scale, unit of action, and Weyl/KKT epsilon are the
same negative log-volume mode of the operatorial Souriau-Fisher metric shadow.
-/
@[rep_depth transport]
theorem anomalyReadoutPacket_eq_metricVolumePotential
    (R : CramerRaoNegLogVolumeAnomalyReadout CI H) (x : E) :
    CI.chiralScale = souriauFisherMetricVolumePotential H x
      ∧ CI.unitOfAction = souriauFisherMetricVolumePotential H x
      ∧ CI.epsilon = souriauFisherMetricVolumePotential H x := by
  exact ⟨
    CramerRaoNegLogVolumeAnomalyReadout.chiralScale_eq_metricVolumePotential R x,
    CramerRaoNegLogVolumeAnomalyReadout.unitOfAction_eq_metricVolumePotential R x,
    CramerRaoNegLogVolumeAnomalyReadout.epsilon_eq_metricVolumePotential R x⟩

/--
The incompressible negative-log Cramer-Rao readout forces zero unit of action.
-/
@[rep_depth thermo]
theorem unitOfAction_eq_zero_of_incompressible
    (R : CramerRaoNegLogVolumeAnomalyReadout CI H)
    (hIncomp : IncompressibleMongeAmpere H) (x : E) :
    CI.unitOfAction = 0 :=
  CI.unitOfAction_eq_zero_of_normalInference
    (CramerRaoNegLogVolumeAnomalyReadout.normalInference_of_incompressible
      R hIncomp x)

/--
The same operatorial metric-volume zero mode feeds the conformal/Weyl owner
theorems: under the structured projector hypotheses, the projector obstruction
and the dilation commutator both collapse.
-/
@[rep_depth transport]
theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_incompressible
    (R : CramerRaoNegLogVolumeAnomalyReadout CI H)
    (hIncomp : IncompressibleMongeAmpere H) (x : E)
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  have hScaleZero : CI.chiralScale = 0 :=
    CramerRaoNegLogVolumeAnomalyReadout.chiralScale_eq_zero_of_incompressible
      R hIncomp x
  have hComm : Commute CI.spectralChiralProjector CI.metricChiralProjector := by
    simpa [Commute] using CI.projectors_commute_of_chiralScale_eq_zero hScaleZero
  have hObsZero : CI.projectorObstruction = 0 :=
    CI.projectorObstruction_eq_zero_of_commute hComm
  have hRight : CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D := by
    rw [hProj]
    exact hLeft
  have hDilZero : CI.P_D * CI.D - CI.D * CI.P_D = 0 :=
    CI.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero
      hRight hScaleZero
  exact ⟨hObsZero, hDilZero⟩

/--
Full Weyl/KKT semantic-collapse packet from the operatorial Souriau-Fisher
metric-volume zero mode.

The first three conjuncts are the existing Weyl/KKT semantic packet. The final
three conjuncts are the zero-mode consequences used by downstream closure code.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_incompressible
    (R : CramerRaoNegLogVolumeAnomalyReadout CI H)
    (hIncomp : IncompressibleMongeAmpere H) (x : E)
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    (CI.chiralScale = CI.epsilon
      ∧ CI.epsilon = ‖CI.projectorObstruction‖₊
      ∧ CI.P_D * CI.D - CI.D * CI.P_D
          = -((2 : ℝ)⁻¹) • CI.projectorObstruction)
      ∧ CI.chiralScale = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  have hPacket :=
    ConformalInference.semanticCollapsePacket
      (CI := CI) hProj hLeft
  have hScaleZero : CI.chiralScale = 0 :=
    CramerRaoNegLogVolumeAnomalyReadout.chiralScale_eq_zero_of_incompressible
      R hIncomp x
  have hObsDil :=
    CramerRaoNegLogVolumeAnomalyReadout.projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_incompressible
      R hIncomp x hProj hLeft
  exact ⟨hPacket, hScaleZero, hObsDil.1, hObsDil.2⟩

end CramerRaoNegLogVolumeAnomalyReadout

end Core

end InfoGeometry.Canonical.IncompressibleCramerRaoActionBridge
