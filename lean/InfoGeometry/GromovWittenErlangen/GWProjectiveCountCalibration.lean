import InfoGeometry.Arithmetic.PrimitiveProjectiveRays
import InfoGeometry.GromovWittenErlangen.LieOrbitCurve
import InfoGeometry.Meta.Architecture

/-!
# GW Projective Count Calibration

This module installs the lowest GW/count layer:

```text
GW localization graph
  -> vertex/edge fixed-sector contributions
  -> unnormalized arithmetic count profile
  -> positive projective count ray
  -> optional finite partition / normalized gauge shape
```

The point is deliberately conservative:

* probability is not primary;
* normalization is a later gauge choice;
* before gauge fixing, the meaningful object is an unnormalized count profile
  modulo positive scale.

No virtual localization theorem or probability normalization theorem is proved
here.  The fields below are finite count/readout data only; they do not package
a separate count-shadow proof.
-/

noncomputable section

namespace InfoGeometry
namespace GromovWittenErlangen

open PrimitiveProjectiveRays

/--
Projective count calibration for a GW localization packet.

The `counts` field is the L0 unnormalized arithmetic count profile.  The
projective object is its positive ray, represented by `SamePositiveRay`.
-/
@[rep_depth count]
structure GWProjectiveCountCalibration
    (G T Target Coeff : Type*) where
  /-- Finite GW/Erlangen localization packet. -/
  localization :
    VirtualLocalizationOrbitPacket G T Target Coeff

  /-- Atomic labels for count sectors. -/
  CountAtom : Type*

  /-- Encode count atoms into arithmetic labels. -/
  atomCode : CountAtom → ℕ

  /-- Raw unnormalized count profile. -/
  counts : CountProfile

  /-- Finite active support of the count profile. -/
  support : Finset ℕ

  /-- Vertex-to-count-sector assignment. -/
  vertexAtom :
    localization.graph.Vertex → CountAtom

  /-- Edge-to-count-sector assignment. -/
  edgeAtom :
    localization.graph.Edge → CountAtom

  /-- Scalar readout of a localization contribution. -/
  coeffReadout : Coeff → ℝ

namespace GWProjectiveCountCalibration

variable {G T Target Coeff : Type*}
variable (C : GWProjectiveCountCalibration G T Target Coeff)

/-- Finite arithmetic partition attached to the GW projective count state. -/
@[rep_depth projective]
def finitePartition (β : ℝ) : ℝ :=
  finiteArithmeticPartition C.counts C.support β

/-- Normalized projective shape after choosing the finite arithmetic gauge. -/
@[rep_depth projective]
def normalizedShape (β : ℝ) : CountProfile :=
  finiteArithmeticNormalizedRay C.counts C.support β

/--
The normalized GW count shape is invariant under nonzero rescaling of the raw
count profile.
-/
@[rep_depth projective]
theorem normalizedShape_scale_counts
    (β c : ℝ) (hc : c ≠ 0) :
    finiteArithmeticNormalizedRay (fun n => c * C.counts n) C.support β =
      C.normalizedShape β :=
  finiteArithmeticNormalizedRay_scale_counts C.counts C.support β c hc

/--
The normalized GW count shape depends only on the positive projective ray of
the raw count profile.
-/
@[rep_depth projective]
theorem normalizedShape_eq_of_samePositiveRay
    {counts' : CountProfile} {β : ℝ}
    (hray : SamePositiveRay C.counts counts')
    (hZ : finiteArithmeticPartition C.counts C.support β ≠ 0)
    (n : ℕ) :
    finiteArithmeticNormalizedRay counts' C.support β n =
      C.normalizedShape β n :=
  finiteArithmeticNormalizedRay_eq_of_samePositiveRay hray hZ n

/-- The selected finite gauge normalizes active weights to sum to one. -/
@[rep_depth projective]
theorem normalizedShape_sum_eq_one
    (β : ℝ)
    (hZ : C.finitePartition β ≠ 0) :
    Finset.sum C.support (fun n => C.normalizedShape β n) = 1 :=
  finiteArithmeticNormalizedRay_sum_eq_one C.counts C.support β hZ

/--
Finite unnormalized weights decompose into partition scale times normalized
projective shape after choosing a nonzero gauge.
-/
@[rep_depth projective]
theorem finiteArithmeticWeight_eq_partition_mul_normalizedShape
    (β : ℝ)
    (hZ : C.finitePartition β ≠ 0)
    (n : ℕ) :
    finiteArithmeticWeight C.counts β n =
      C.finitePartition β * C.normalizedShape β n :=
  finiteArithmeticWeight_eq_partition_mul_normalizedRay
    C.counts C.support β hZ n

end GWProjectiveCountCalibration

end GromovWittenErlangen
end InfoGeometry
