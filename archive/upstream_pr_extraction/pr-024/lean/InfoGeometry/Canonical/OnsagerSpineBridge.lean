import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Canonical.GeneratedFlow
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OnsagerSpineBridge

Narrow owner bridge connecting the existing operatorial Onsager Hessian lane to
`LogGenerator -> GeneratedFlow -> GeometricResponse` spine primitives.
-/

namespace InfoGeometry.Canonical.OnsagerSpineBridge

open InfoGeometry.Canonical.OnsagerReciprocity

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Chan" => InfoGeometry.Canonical.RelationalInformationCore.PerturbationChannel E

/--
Generated-flow view of the symmetric Onsager operator Hessian lane.
-/
@[rep_depth transport]
noncomputable def onsagerMetricGeneratedFlow
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)) :
    InfoGeometry.Canonical.GeneratedFlow EndH (LinearMap.BilinForm ℝ Chan) :=
  fun A => operatorMetricHessianForm (E := E) P A

/--
Generated-flow view of the skew Onsager curvature lane.
-/
@[rep_depth transport]
noncomputable def onsagerCurvatureGeneratedFlow
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)) :
    InfoGeometry.Canonical.GeneratedFlow EndH (LinearMap.BilinForm ℝ Chan) :=
  fun A => operatorCurvatureHessianForm (E := E) P A

/-- Point-readout response extractor for a fixed perturbation-channel pair. -/
@[rep_depth transport]
noncomputable def onsagerPairReadout
    (X Y : Chan) :
    InfoGeometry.Canonical.GeometricResponse (LinearMap.BilinForm ℝ Chan) ℝ :=
  fun B => B X Y

/--
Spine-factorization of the symmetric Onsager coefficient through
`LogGenerator.respond`.
-/
@[rep_depth transport, capstone]
theorem responseCoefficient_eq_spineRespond
    {W : Type*}
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (L : InfoGeometry.Canonical.LogGenerator W EndH)
    (X Y : Chan)
    (w : W) :
    InfoGeometry.Canonical.LogGenerator.respond L
      (onsagerMetricGeneratedFlow (E := E) P)
      (onsagerPairReadout X Y) w
      =
    responseCoefficient (E := E) P X Y (L.logGen w) := by
  rfl

/--
Spine-factorization of the skew Onsager coefficient through
`LogGenerator.respond`.
-/
@[rep_depth transport, capstone]
theorem curvatureCoefficient_eq_spineRespond
    {W : Type*}
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (L : InfoGeometry.Canonical.LogGenerator W EndH)
    (X Y : Chan)
    (w : W) :
    InfoGeometry.Canonical.LogGenerator.respond L
      (onsagerCurvatureGeneratedFlow (E := E) P)
      (onsagerPairReadout X Y) w
      =
    curvatureCoefficient (E := E) P X Y (L.logGen w) := by
  rfl

/--
Spine-level Onsager reciprocity:
swapping channel order leaves the symmetric response readout unchanged.
-/
@[rep_depth transport, capstone]
theorem spineRespond_metric_swap
    {W : Type*}
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (L : InfoGeometry.Canonical.LogGenerator W EndH)
    (X Y : Chan)
    (w : W) :
    InfoGeometry.Canonical.LogGenerator.respond L
      (onsagerMetricGeneratedFlow (E := E) P)
      (onsagerPairReadout X Y) w
      =
    InfoGeometry.Canonical.LogGenerator.respond L
      (onsagerMetricGeneratedFlow (E := E) P)
      (onsagerPairReadout Y X) w := by
  simpa [responseCoefficient_eq_spineRespond] using
    (responseCoefficient_swap (E := E) P X Y (L.logGen w))

/--
Spine-level Casimir skew law:
swapping channel order flips the sign of the skew response readout.
-/
@[rep_depth transport, capstone]
theorem spineRespond_curvature_swap_neg
    {W : Type*}
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (L : InfoGeometry.Canonical.LogGenerator W EndH)
    (X Y : Chan)
    (w : W) :
    InfoGeometry.Canonical.LogGenerator.respond L
      (onsagerCurvatureGeneratedFlow (E := E) P)
      (onsagerPairReadout Y X) w
      =
    -InfoGeometry.Canonical.LogGenerator.respond L
      (onsagerCurvatureGeneratedFlow (E := E) P)
      (onsagerPairReadout X Y) w := by
  simpa [curvatureCoefficient_eq_spineRespond] using
    (curvatureCoefficient_swap_neg (E := E) P X Y (L.logGen w))

end Core

end InfoGeometry.Canonical.OnsagerSpineBridge
