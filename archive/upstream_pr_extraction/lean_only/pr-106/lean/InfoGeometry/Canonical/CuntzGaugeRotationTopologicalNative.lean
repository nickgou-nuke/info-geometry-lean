import Mathlib
import InfoGeometry.Canonical.CuntzGaugeRotationNative

namespace InfoGeometry.Canonical

open ToeplitzCuntzVacuumBridge

variable {R : Type*} [CommRing R] [StarRing R]
variable [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R] [ContinuousNeg R]

def nativeRotationParameterSet : Set (R × R) :=
  {p | star p.1 = p.1 ∧ star p.2 = p.2 ∧ p.1 * p.1 + p.2 * p.2 = 1}

theorem nativeRotationParameterSet_isClosed
    [ContinuousStar R] [T2Space R] :
    IsClosed (nativeRotationParameterSet (R := R)) := by
  have h₁ : IsClosed {p : R × R | star p.1 = p.1} := by
    exact isClosed_eq (continuous_star.comp continuous_fst) continuous_fst
  have h₂ : IsClosed {p : R × R | star p.2 = p.2} := by
    exact isClosed_eq (continuous_star.comp continuous_snd) continuous_snd
  have h₃ : IsClosed {p : R × R | p.1 * p.1 + p.2 * p.2 = 1} := by
    exact isClosed_eq
      ((continuous_fst.mul continuous_fst).add
        (continuous_snd.mul continuous_snd)) continuous_const
  simpa [nativeRotationParameterSet] using h₁.inter (h₂.inter h₃)

theorem realNativeRotationParameterSet_isCompact :
    IsCompact (nativeRotationParameterSet (R := ℝ)) := by
  have hrect :
      IsCompact ((Set.Icc (-1 : ℝ) 1) ×ˢ (Set.Icc (-1 : ℝ) 1)) :=
    isCompact_Icc.prod isCompact_Icc
  apply hrect.of_isClosed_subset
    (nativeRotationParameterSet_isClosed (R := ℝ))
  intro p hp
  have hnorm : p.1 * p.1 + p.2 * p.2 = 1 := hp.2.2
  have h₁ : p.1 * p.1 ≤ 1 := by
    nlinarith [sq_nonneg p.2]
  have h₂ : p.2 * p.2 ≤ 1 := by
    nlinarith [sq_nonneg p.1]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [sq_nonneg (p.1 + 1)]
  · nlinarith [sq_nonneg (p.1 - 1)]
  · nlinarith [sq_nonneg (p.2 + 1)]
  · nlinarith [sq_nonneg (p.2 - 1)]

abbrev NativeRotationParameter :=
  {p : R × R // p ∈ nativeRotationParameterSet (R := R)}

theorem isCompact_nativeRotationParameterSpace :
    CompactSpace (NativeRotationParameter (R := ℝ)) := by
  exact isCompact_iff_compactSpace.mp realNativeRotationParameterSet_isCompact

theorem realNativeRotationParameterSpace_nonempty :
    Nonempty (NativeRotationParameter (R := ℝ)) := by
  refine ⟨⟨(1, 0), ?_⟩⟩
  norm_num [nativeRotationParameterSet]

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

theorem exists_max_realNativeRotationV1Readout
    (g : ToeplitzCuntzGenerators ℝ) :
    ∃ p : NativeRotationParameter (R := ℝ),
      IsMaxOn (nativeRotationV1Readout (R := ℝ) g) Set.univ p := by
  letI : CompactSpace (NativeRotationParameter (R := ℝ)) :=
    isCompact_nativeRotationParameterSpace
  have hnonempty : (Set.univ : Set (NativeRotationParameter (R := ℝ))).Nonempty := by
    refine ⟨⟨(1, 0), ?_⟩, Set.mem_univ _⟩
    norm_num [nativeRotationParameterSet]
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn
    hnonempty
    (continuous_nativeRotationV1Readout (R := ℝ) g).continuousOn
  exact ⟨p, hp⟩

theorem exists_min_realNativeRotationV1Readout
    (g : ToeplitzCuntzGenerators ℝ) :
    ∃ p : NativeRotationParameter (R := ℝ),
      IsMinOn (nativeRotationV1Readout (R := ℝ) g) Set.univ p := by
  letI : CompactSpace (NativeRotationParameter (R := ℝ)) :=
    isCompact_nativeRotationParameterSpace
  have hnonempty : (Set.univ : Set (NativeRotationParameter (R := ℝ))).Nonempty := by
    refine ⟨⟨(1, 0), ?_⟩, Set.mem_univ _⟩
    norm_num [nativeRotationParameterSet]
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn
    hnonempty
    (continuous_nativeRotationV1Readout (R := ℝ) g).continuousOn
  exact ⟨p, hp⟩

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

theorem exists_max_realNativeRotationV2Readout
    (g : ToeplitzCuntzGenerators ℝ) :
    ∃ p : NativeRotationParameter (R := ℝ),
      IsMaxOn (nativeRotationV2Readout (R := ℝ) g) Set.univ p := by
  letI : CompactSpace (NativeRotationParameter (R := ℝ)) :=
    isCompact_nativeRotationParameterSpace
  have hnonempty : (Set.univ : Set (NativeRotationParameter (R := ℝ))).Nonempty := by
    refine ⟨⟨(1, 0), ?_⟩, Set.mem_univ _⟩
    norm_num [nativeRotationParameterSet]
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn
    hnonempty
    (continuous_nativeRotationV2Readout (R := ℝ) g).continuousOn
  exact ⟨p, hp⟩

theorem exists_min_realNativeRotationV2Readout
    (g : ToeplitzCuntzGenerators ℝ) :
    ∃ p : NativeRotationParameter (R := ℝ),
      IsMinOn (nativeRotationV2Readout (R := ℝ) g) Set.univ p := by
  letI : CompactSpace (NativeRotationParameter (R := ℝ)) :=
    isCompact_nativeRotationParameterSpace
  have hnonempty : (Set.univ : Set (NativeRotationParameter (R := ℝ))).Nonempty := by
    refine ⟨⟨(1, 0), ?_⟩, Set.mem_univ _⟩
    norm_num [nativeRotationParameterSet]
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn
    hnonempty
    (continuous_nativeRotationV2Readout (R := ℝ) g).continuousOn
  exact ⟨p, hp⟩

theorem continuous_nativeRotationReadout
    (g : ToeplitzCuntzGenerators R) :
    Continuous (nativeRotationReadout (R := R) g) := by
  exact (continuous_nativeRotationV1Readout (R := R) g).prodMk
    (continuous_nativeRotationV2Readout (R := R) g)

theorem isCompact_realNativeRotationReadout_range
    (g : ToeplitzCuntzGenerators ℝ) :
    IsCompact (Set.range (nativeRotationReadout (R := ℝ) g)) := by
  letI : CompactSpace (NativeRotationParameter (R := ℝ)) :=
    isCompact_nativeRotationParameterSpace
  exact isCompact_range (continuous_nativeRotationReadout (R := ℝ) g)

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
