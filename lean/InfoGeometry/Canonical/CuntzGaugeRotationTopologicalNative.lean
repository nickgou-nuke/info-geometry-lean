import Mathlib
import InfoGeometry.Canonical.CuntzGaugeRotationNative

namespace InfoGeometry.Canonical

open ToeplitzCuntzVacuumBridge

variable {R : Type*} [CommRing R] [StarRing R]
variable [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R] [ContinuousNeg R]

def nativeRotationParameterSet : Set (R × R) :=
  {p | star p.1 = p.1 ∧ star p.2 = p.2 ∧ p.1 * p.1 + p.2 * p.2 = 1}

abbrev NativeRotationParameter :=
  {p : R × R // p ∈ nativeRotationParameterSet (R := R)}

def nativeRotationParameterCoefficients
    (p : NativeRotationParameter (R := R)) :
    SelfAdjointNormalizedPairNative R where
  a := p.1.1
  b := p.1.2
  star_a := p.2.1
  star_b := p.2.2.1
  normalized := p.2.2.2

def nativeRotationV1Readout (g : ToeplitzCuntzGenerators R)
    (p : NativeRotationParameter (R := R)) : R :=
  p.1.1 * g.V1 + p.1.2 * g.V2

def nativeRotationV2Readout (g : ToeplitzCuntzGenerators R)
    (p : NativeRotationParameter (R := R)) : R :=
  -(p.1.2 * g.V1) + p.1.1 * g.V2

def nativeRotationReadout (g : ToeplitzCuntzGenerators R)
    (p : NativeRotationParameter (R := R)) : R × R :=
  (nativeRotationV1Readout g p, nativeRotationV2Readout g p)

theorem continuous_nativeRotationV1Readout
    (g : ToeplitzCuntzGenerators R) :
    Continuous (nativeRotationV1Readout (R := R) g) := by
  have ha : Continuous (fun p : NativeRotationParameter (R := R) => p.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hb : Continuous (fun p : NativeRotationParameter (R := R) => p.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have hc1 : Continuous (fun _ : NativeRotationParameter (R := R) => g.V1) :=
    continuous_const
  have hc2 : Continuous (fun _ : NativeRotationParameter (R := R) => g.V2) :=
    continuous_const
  exact (ha.mul hc1).add (hb.mul hc2)

theorem continuous_nativeRotationV2Readout
    (g : ToeplitzCuntzGenerators R) :
    Continuous (nativeRotationV2Readout (R := R) g) := by
  have ha : Continuous (fun p : NativeRotationParameter (R := R) => p.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hb : Continuous (fun p : NativeRotationParameter (R := R) => p.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have hc1 : Continuous (fun _ : NativeRotationParameter (R := R) => g.V1) :=
    continuous_const
  have hc2 : Continuous (fun _ : NativeRotationParameter (R := R) => g.V2) :=
    continuous_const
  exact (hb.mul hc1).neg.add (ha.mul hc2)

theorem continuous_nativeRotationReadout
    (g : ToeplitzCuntzGenerators R) :
    Continuous (nativeRotationReadout (R := R) g) := by
  exact (continuous_nativeRotationV1Readout (R := R) g).prodMk
    (continuous_nativeRotationV2Readout (R := R) g)

theorem nativeRotationV1Readout_isometry
    (g : ToeplitzCuntzGenerators R) (p : NativeRotationParameter (R := R)) :
    star (nativeRotationV1Readout g p) * nativeRotationV1Readout g p = 1 := by
  simpa [nativeRotationV1Readout, nativeRotationV1,
    nativeRotationParameterCoefficients] using
    nativeRotationV1_isometry (nativeRotationParameterCoefficients p) g

theorem nativeRotationV2Readout_isometry
    (g : ToeplitzCuntzGenerators R) (p : NativeRotationParameter (R := R)) :
    star (nativeRotationV2Readout g p) * nativeRotationV2Readout g p = 1 := by
  simpa [nativeRotationV2Readout, nativeRotationV2,
    nativeRotationParameterCoefficients] using
    nativeRotationV2_isometry (nativeRotationParameterCoefficients p) g

end InfoGeometry.Canonical
