import InfoGeometry.Canonical.ConformalAnomalyReadout

namespace InfoGeometry.Canonical.ConformalUnification

open InfoGeometry.Canonical.MoE

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ConformalInference

variable (CI : ConformalInference E)

/--
Proof-carrying unit-relative-volume input for the degenerate normal-phase lane.
-/
@[rep_depth operator] def UnitRelativeVolumeBit
    (n : Nat) (M : SinkhornMatrix n) : Prop :=
  relativeVolumeChangeRN n M = 1

/-- Constructor from the existing unit-relative-volume equality. -/
@[rep_depth operator] theorem unitRelativeVolumeBit_of_eq_one
    {n : Nat} {M : SinkhornMatrix n}
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    UnitRelativeVolumeBit n M :=
  hUnitVolume

/--
Normal-phase (degenerate) package:
projector commutation collapses the operator source to zero and therefore all
readout scalars to zero.
-/
@[rep_depth operator] def NormalPhaseDegeneratePackage : Prop :=
  Commute CI.spectralChiralProjector CI.metricChiralProjector ∧
  CI.projectorObstruction = 0 ∧
  CI.chiralScale = 0 ∧
  CI.IsNormalInference

/-- Degenerate package from explicit projector commutation. -/
@[rep_depth operator] theorem normalPhaseDegeneratePackage_of_projectors_commute
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
@[rep_depth operator] theorem normalPhaseDegeneratePackage_of_kahlerLogDet_unitRelativeVolume
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

/--
Degenerate package from the proof-carrying unit-relative-volume bit.
-/
@[rep_depth operator] theorem normalPhaseDegeneratePackage_of_unitRelativeVolumeBit
    {n : Nat}
    (M : SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeBit n M) :
    NormalPhaseDegeneratePackage (CI := CI) :=
  CI.normalPhaseDegeneratePackage_of_kahlerLogDet_unitRelativeVolume
    (M := M) hScaleFromKahler bit

/--
The local unit-relative-volume witness already forces the normal-phase equation.

This gives downstream users a direct theorem-backed readback from the local
constructive bit to `CI.IsNormalInference`, instead of forcing them to unpack
`relativeVolumeChangeRN n M = 1` and replay the RN/Kähler route.
-/
@[rep_depth operator] theorem isNormalInference_of_unitRelativeVolumeBit
    {n : Nat}
    (M : SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeBit n M) :
    CI.IsNormalInference :=
  (CI.normalPhaseDegeneratePackage_of_unitRelativeVolumeBit
    (M := M) hScaleFromKahler bit).2.2.2

/--
The local unit-relative-volume witness also forces the degenerate projector
obstruction to vanish, via the normal-phase package.  This gives downstream
callers a direct constructive readback and avoids carrying a separate raw
`CI.projectorObstruction = 0` hypothesis after the RN/Kähler bit is available.
-/
@[rep_depth operator] theorem projectorObstruction_eq_zero_of_unitRelativeVolumeBit
    {n : Nat}
    (M : SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeBit n M) :
    CI.projectorObstruction = 0 :=
  (CI.normalPhaseDegeneratePackage_of_unitRelativeVolumeBit
    (M := M) hScaleFromKahler bit).2.1

end ConformalInference

end InfoGeometry.Canonical.ConformalUnification
