import InfoGeometry.Canonical.ConformalAnomalyReadout

namespace InfoGeometry.Canonical.ConformalUnification

open InfoGeometry.Canonical.MoE

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ConformalInference

variable (CI : ConformalInference E)

/--
Normal-phase (degenerate) package:
projector commutation collapses the operator source to zero and therefore all
readout scalars to zero.
-/
@[rep_depth thermo] structure NormalPhaseDegeneratePackage : Prop where
  projectors_commute :
    Commute CI.spectralChiralProjector CI.metricChiralProjector
  projectorObstruction_eq_zero :
    CI.projectorObstruction = 0
  chiralScale_eq_zero :
    CI.chiralScale = 0
  isNormalInference :
    CI.IsNormalInference

/-- Degenerate package from explicit projector commutation. -/
@[rep_depth thermo] theorem normalPhaseDegeneratePackage_of_projectors_commute
    (hComm : Commute CI.spectralChiralProjector CI.metricChiralProjector) :
    NormalPhaseDegeneratePackage (CI := CI) := by
  have hObsZero : CI.projectorObstruction = 0 :=
    CI.projectorObstruction_eq_zero_of_commute hComm
  have hScaleZero : CI.chiralScale = 0 :=
    CI.chiralScale_eq_zero_of_projectors_commute hComm.eq
  refine ⟨hComm, hObsZero, hScaleZero, ?_⟩
  simpa [ConformalInference.IsNormalInference] using hScaleZero

/--
Degenerate package from the RN/Kähler/log-det unit-relative-volume assumptions.
-/
@[rep_depth thermo] theorem normalPhaseDegeneratePackage_of_kahlerLogDet_unitRelativeVolume
    {n : Nat}
    (M : SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    NormalPhaseDegeneratePackage (CI := CI) := by
  have hComm :
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector :=
    CI.projectors_commute_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  have hComm' :
      Commute CI.spectralChiralProjector CI.metricChiralProjector := by
    simpa [Commute] using hComm
  exact CI.normalPhaseDegeneratePackage_of_projectors_commute hComm'

end ConformalInference

end InfoGeometry.Canonical.ConformalUnification
