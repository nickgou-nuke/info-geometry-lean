import Mathlib
import InfoGeometry.Canonical.CuntzGaugeRotationNative

namespace InfoGeometry.Canonical

open ToeplitzCuntzVacuumBridge

variable {R : Type*} [CommRing R] [StarRing R]
variable [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R] [ContinuousNeg R]

/-- The normalized self-adjoint coefficient locus for the native rotation. -/
def rotationParameterSet : Set (R × R) :=
  {p | star p.1 = p.1 ∧ star p.2 = p.2 ∧ p.1 * p.1 + p.2 * p.2 = 1}

/-- The coefficient space carries the induced topology from `R × R`. -/
abbrev RotationParameter := {p : R × R // p ∈ rotationParameterSet (R := R)}

def rotationParameterToNative (p : RotationParameter (R := R)) :
    SelfAdjointNormalizedPairNative R where
  a := p.1.1
  b := p.1.2
  star_a := p.2.1
  star_b := p.2.2.1
  normalized := p.2.2.2

def continuousRotationV1 (g : ToeplitzCuntzGenerators R)
    (p : RotationParameter (R := R)) : R :=
  nativeRotationV1 (rotationParameterToNative p) g

def continuousRotationV2 (g : ToeplitzCuntzGenerators R)
    (p : RotationParameter (R := R)) : R :=
  nativeRotationV2 (rotationParameterToNative p) g

theorem continuous_continuousRotationV1 (g : ToeplitzCuntzGenerators R) :
    Continuous (continuousRotationV1 (R := R) g) := by
  change Continuous (fun p : RotationParameter (R := R) =>
    p.1.1 * g.V1 + p.1.2 * g.V2)
  have ha : Continuous (fun p : RotationParameter (R := R) => p.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hb : Continuous (fun p : RotationParameter (R := R) => p.1.2) :=
    continuous_snd.comp continuous_subtype_val
  exact (ha.mul continuous_const).add (hb.mul continuous_const)

theorem continuous_continuousRotationV2 (g : ToeplitzCuntzGenerators R) :
    Continuous (continuousRotationV2 (R := R) g) := by
  unfold continuousRotationV2 nativeRotationV2 rotationParameterToNative
  fun_prop

theorem continuousRotationV1_preserves_isometry
    (g : ToeplitzCuntzGenerators R) (p : RotationParameter (R := R)) :
    star (continuousRotationV1 g p) * continuousRotationV1 g p = 1 :=
  nativeRotationV1_isometry (rotationParameterToNative p) g

theorem continuousRotationV2_preserves_isometry
    (g : ToeplitzCuntzGenerators R) (p : RotationParameter (R := R)) :
    star (continuousRotationV2 g p) * continuousRotationV2 g p = 1 :=
  nativeRotationV2_isometry (rotationParameterToNative p) g

end InfoGeometry.Canonical
