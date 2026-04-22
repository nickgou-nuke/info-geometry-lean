import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.MongeAmpereCramerRao
import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.IncompressibleBitBridge

The repo-native "bit" used here is not a finite Hilbert-space toy. It is a
unit relative-volume witness:

- in the RN/Kähler lane, `relativeVolumeChangeRN = 1`;
- in the Cramer-Rao/Monge-Ampere lane, incompressibility forces zero log-volume
  mode for the Hessian metric determinant;
- through the existing conformal anomaly owner surface, unit relative volume
  forces normal inference and hence zero unit of action.

The redline sign convention is preserved: the Kähler/modular potential is the
negative log of the relative volume mode, not the raw positive log.

This bridge packages that corridor without asserting a new global equivalence
between all incompressible Hessian data and all conformal anomaly data.
-/

namespace InfoGeometry.Canonical.IncompressibleBitBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.MongeAmpereCramerRao
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Convex

section RelativeVolumeBit

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The incompressible information bit in the RN relative-volume lane.

It is the proof-carrying unit `relativeVolumeChangeRN = 1`, not a finite
cardinality bit and not a scalar replacement for the operatorial anomaly.
-/
@[rep_depth projective]
structure UnitRelativeVolumeBit (n : Nat) (M : SinkhornMatrix n) : Prop where
  unit_relative_volume : relativeVolumeChangeRN n M = 1

/-- Constructor from the existing RN unit-relative-volume equality. -/
@[rep_depth projective]
theorem unitRelativeVolumeBit_of_eq_one
    {n : Nat} {M : SinkhornMatrix n}
    (hUnit : relativeVolumeChangeRN n M = 1) :
    UnitRelativeVolumeBit n M :=
  ⟨hUnit⟩

/--
The unit relative-volume bit is exactly the input needed by the existing
conformal owner theorem to enter the normal phase.
-/
@[rep_depth thermo]
theorem isNormalInference_of_unitRelativeVolumeBit
    (CI : ConformalInference E)
    {n : Nat}
    (M : SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeBit n M) :
    CI.IsNormalInference := by
  exact CI.isNormalInference_of_kahlerLogDet_unitRelativeVolume
    (M := M) hScaleFromKahler bit.unit_relative_volume

/--
The incompressible unit of relative volume collapses the conformal unit of
action, provided the existing Kähler/log-det readout identifies the chiral scale
with the RN Kähler potential.
-/
@[rep_depth thermo]
theorem unitOfAction_eq_zero_of_unitRelativeVolumeBit
    (CI : ConformalInference E)
    {n : Nat}
    (M : SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeBit n M) :
    CI.unitOfAction = 0 := by
  have hNormal : CI.IsNormalInference :=
    isNormalInference_of_unitRelativeVolumeBit
      (CI := CI) (M := M) hScaleFromKahler bit
  exact CI.unitOfAction_eq_zero_of_normalInference hNormal

/--
Unit relative-volume bit packet: normal inference and zero unit of action are
derived together from the same bit witness.
-/
@[rep_depth thermo]
theorem normalInference_and_unitOfAction_eq_zero_of_unitRelativeVolumeBit
    (CI : ConformalInference E)
    {n : Nat}
    (M : SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeBit n M) :
    CI.IsNormalInference ∧ CI.unitOfAction = 0 := by
  refine ⟨?_, ?_⟩
  · exact isNormalInference_of_unitRelativeVolumeBit
      (CI := CI) (M := M) hScaleFromKahler bit
  · exact unitOfAction_eq_zero_of_unitRelativeVolumeBit
      (CI := CI) (M := M) hScaleFromKahler bit

end RelativeVolumeBit

section CramerRaoBit

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Cramer-Rao/Monge-Ampere form of the incompressible information bit.

This records the owner assumption `IncompressibleMongeAmpere H`; the determinant
and log-volume conclusions are derived by `MongeAmpereCramerRao`.
-/
@[rep_depth operator]
structure IncompressibleCramerRaoBit (H : HessianGeometry E) : Prop where
  incompressible : IncompressibleMongeAmpere H

/-- Constructor from the existing incompressible Monge-Ampere predicate. -/
@[rep_depth operator]
theorem incompressibleCramerRaoBit_of_incompressible
    {H : HessianGeometry E}
    (hIncomp : IncompressibleMongeAmpere H) :
    IncompressibleCramerRaoBit H :=
  ⟨hIncomp⟩

/--
The Cramer-Rao incompressible bit has determinant magnitude one at each point
where the metric determinant is nonzero.
-/
@[rep_depth operator]
theorem absDet_cramerRaoMetric_eq_one_of_incompressibleBit
    (H : HessianGeometry E)
    (bit : IncompressibleCramerRaoBit H)
    (x : E)
    (hdet : LinearMap.det (cramerRaoMetricOp H x).toLinearMap ≠ 0) :
    |LinearMap.det (cramerRaoMetricOp H x).toLinearMap| = 1 := by
  exact absDet_cramerRaoMetric_eq_one_of_incompressible
    (H := H) bit.incompressible x hdet

/--
The Cramer-Rao incompressible bit has zero logarithmic volume mode.
-/
@[rep_depth operator]
theorem logAbsDet_cramerRaoMetric_eq_zero_of_incompressibleBit
    (H : HessianGeometry E)
    (bit : IncompressibleCramerRaoBit H)
    (x : E) :
    Real.log (|LinearMap.det (cramerRaoMetricOp H x).toLinearMap|) = 0 := by
  exact logAbsDet_cramerRaoMetric_eq_zero_of_incompressible
    (H := H) bit.incompressible x

/--
If the conformal anomaly scale is identified with the Kähler/RN potential
coming from the Cramer-Rao logarithmic volume mode, then an incompressible
Cramer-Rao bit forces normal inference.

This keeps the repository redline sign:
`Kähler potential = - log(relative volume mode)`.
-/
@[rep_depth thermo]
theorem isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume
    (CI : ConformalInference E)
    (H : HessianGeometry E)
    (bit : IncompressibleCramerRaoBit H)
    (x : E)
    (hScaleFromNegLogVolume :
      CI.chiralScale =
        -Real.log (|LinearMap.det (cramerRaoMetricOp H x).toLinearMap|)) :
    CI.IsNormalInference := by
  have hLogZero :
      Real.log (|LinearMap.det (cramerRaoMetricOp H x).toLinearMap|) = 0 :=
    logAbsDet_cramerRaoMetric_eq_zero_of_incompressibleBit
      (H := H) bit x
  have hNegLogZero :
      -Real.log (|LinearMap.det (cramerRaoMetricOp H x).toLinearMap|) = 0 := by
    rw [hLogZero, neg_zero]
  simpa [ConformalInference.IsNormalInference, hScaleFromNegLogVolume] using hNegLogZero

/--
If the anomaly scale is the negative Cramer-Rao log-volume mode, the
incompressible bit collapses the conformal unit of action.
-/
@[rep_depth thermo]
theorem unitOfAction_eq_zero_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume
    (CI : ConformalInference E)
    (H : HessianGeometry E)
    (bit : IncompressibleCramerRaoBit H)
    (x : E)
    (hScaleFromNegLogVolume :
      CI.chiralScale =
        -Real.log (|LinearMap.det (cramerRaoMetricOp H x).toLinearMap|)) :
    CI.unitOfAction = 0 := by
  have hNormal : CI.IsNormalInference :=
    isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume
      (CI := CI) (H := H) bit x hScaleFromNegLogVolume
  exact CI.unitOfAction_eq_zero_of_normalInference hNormal

end CramerRaoBit

end InfoGeometry.Canonical.IncompressibleBitBridge
