import InfoGeometry.Canonical.SouriauRelativeEntropyLevelTopology

namespace SouriauRelativeEntropyBandTopology

open SouriauRelativeEntropy
open SouriauRelativeEntropySimplex
open SouriauRelativeEntropySublevel
open SouriauRelativeEntropyLevelTopology

variable {n : ℕ}

/-- Relative entropy restricted to the compact positive simplex core. -/
noncomputable def relativeEntropyCoreValue (ε : ℝ)
    (p : positiveSimplexCorePair (n := n) ε) : ℝ :=
  relativeEntropy p.1.1 p.1.2

theorem continuous_relativeEntropyCoreValue
    {ε : ℝ} (hεpos : 0 < ε) :
    Continuous (relativeEntropyCoreValue (n := n) ε) := by
  exact continuous_relativeEntropy_on_subtype _
    (positiveSimplexCorePair_subset_positiveOrthantPair hεpos)

/-- A compact-core KL band with lower and upper information bounds. -/
def relativeEntropyCoreBand (ε a b : ℝ) :
    Set (positiveSimplexCorePair (n := n) ε) :=
  {p | a ≤ relativeEntropyCoreValue ε p ∧
    relativeEntropyCoreValue ε p ≤ b}

theorem isClosed_relativeEntropyCoreBand
    {ε : ℝ} (hεpos : 0 < ε) (a b : ℝ) :
    IsClosed (relativeEntropyCoreBand (n := n) ε a b) := by
  exact isClosed_Icc.preimage
    (continuous_relativeEntropyCoreValue (n := n) hεpos)

theorem isCompact_relativeEntropyCoreBand
    {ε : ℝ} (hεpos : 0 < ε) (a b : ℝ) :
    IsCompact (relativeEntropyCoreBand (n := n) ε a b) := by
  letI : CompactSpace (positiveSimplexCorePair (n := n) ε) :=
    isCompact_iff_compactSpace.mp
      (isCompact_positiveSimplexCorePair ε)
  exact (isClosed_relativeEntropyCoreBand hεpos a b).isCompact

theorem relativeEntropyCoreBand_inter
    (ε a b c d : ℝ) :
    relativeEntropyCoreBand (n := n) ε a b ∩
        relativeEntropyCoreBand (n := n) ε c d =
      relativeEntropyCoreBand (n := n) ε (max a c) (min b d) := by
  ext p
  simp only [relativeEntropyCoreBand, Set.mem_inter_iff,
    Set.mem_setOf_eq, max_le_iff, le_min_iff]
  aesop

theorem relativeEntropyCoreLevel_eq_band
    (ε c : ℝ) :
    relativeEntropyCoreLevel (n := n) ε c =
      relativeEntropyCoreBand (n := n) ε c c := by
  ext p
  change relativeEntropyCoreValue ε p = c ↔
    c ≤ relativeEntropyCoreValue ε p ∧
      relativeEntropyCoreValue ε p ≤ c
  constructor
  · intro hp
    exact ⟨hp.ge, hp.le⟩
  · intro hp
    exact le_antisymm hp.2 hp.1

theorem relativeEntropyCoreBand_zero_eq_sublevel
    {ε : ℝ} (hεpos : 0 < ε) (c : ℝ) :
    relativeEntropyCoreBand (n := n) ε 0 c =
      relativeEntropyCoreSublevel (n := n) ε c := by
  ext p
  constructor
  · exact fun hp => hp.2
  · intro hp
    exact
      ⟨relativeEntropy_nonneg_on_positiveSimplexCorePair hεpos p,
        hp⟩

theorem relativeEntropyCoreBand_nonempty_iff
    (ε a b : ℝ) :
    (relativeEntropyCoreBand (n := n) ε a b).Nonempty ↔
      ∃ c ∈ Set.Icc a b,
        c ∈ relativeEntropyCoreRange (n := n) ε := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨relativeEntropyCoreValue ε p, hp, p, rfl⟩
  · rintro ⟨c, hc, p, hp⟩
    refine ⟨p, ?_⟩
    change a ≤ relativeEntropyCoreValue ε p ∧
      relativeEntropyCoreValue ε p ≤ b
    simpa [relativeEntropyCoreValue, hp] using hc

theorem relativeEntropyCoreBand_nonempty_iff_max_le_min
    (hn : 0 < n) {ε a b : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    (relativeEntropyCoreBand (n := n) ε a b).Nonempty ↔
      max a 0 ≤
        min b (sSup (relativeEntropyCoreRange (n := n) ε)) := by
  rw [relativeEntropyCoreBand_nonempty_iff]
  have hrange :=
    relativeEntropyCoreRange_eq_Icc_zero_sSup
      hn hεpos hεupper
  constructor
  · rintro ⟨c, hc, hcrange⟩
    have hcglobal : c ∈
        Set.Icc 0
          (sSup (relativeEntropyCoreRange (n := n) ε)) :=
      (Set.ext_iff.mp hrange c).mp hcrange
    exact
      (max_le hc.1 hcglobal.1).trans
        (le_min hc.2 hcglobal.2)
  · intro hab
    refine ⟨max a 0, ?_, ?_⟩
    · exact
        ⟨le_max_left a 0,
          hab.trans (min_le_left _ _)⟩
    · apply (Set.ext_iff.mp hrange (max a 0)).mpr
      exact
        ⟨le_max_right a 0,
          hab.trans (min_le_right _ _)⟩

theorem relativeEntropyCoreBand_mono
    (ε : ℝ) {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    relativeEntropyCoreBand (n := n) ε a b ⊆
      relativeEntropyCoreBand (n := n) ε c d := by
  intro p hp
  exact ⟨hca.trans hp.1, hp.2.trans hbd⟩

/-- Canonical inclusion of a KL band into a wider KL band. -/
def relativeEntropyCoreBandInclusion
    (ε : ℝ) {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    relativeEntropyCoreBand (n := n) ε a b →
      relativeEntropyCoreBand (n := n) ε c d :=
  fun p => ⟨p.1, relativeEntropyCoreBand_mono ε hca hbd p.2⟩

@[simp] theorem relativeEntropyCoreBandInclusion_coe
    (ε : ℝ) {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d)
    (p : relativeEntropyCoreBand (n := n) ε a b) :
    (relativeEntropyCoreBandInclusion ε hca hbd p :
      positiveSimplexCorePair (n := n) ε) = p.1 := rfl

theorem continuous_relativeEntropyCoreBandInclusion
    (ε : ℝ) {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    Continuous
      (relativeEntropyCoreBandInclusion (n := n) ε hca hbd) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem injective_relativeEntropyCoreBandInclusion
    (ε : ℝ) {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    Function.Injective
      (relativeEntropyCoreBandInclusion (n := n) ε hca hbd) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg
    (fun r : relativeEntropyCoreBand (n := n) ε c d => r.1) hpq

theorem isClosedEmbedding_relativeEntropyCoreBandInclusion
    {ε : ℝ} (hεpos : 0 < ε) {a b c d : ℝ}
    (hca : c ≤ a) (hbd : b ≤ d) :
    Topology.IsClosedEmbedding
      (relativeEntropyCoreBandInclusion (n := n) ε hca hbd) := by
  letI : CompactSpace (relativeEntropyCoreBand (n := n) ε a b) :=
    isCompact_iff_compactSpace.mp
      (isCompact_relativeEntropyCoreBand (n := n) hεpos a b)
  exact
    (continuous_relativeEntropyCoreBandInclusion
      (n := n) ε hca hbd).isClosedEmbedding
        (injective_relativeEntropyCoreBandInclusion
          (n := n) ε hca hbd)

theorem isProperMap_relativeEntropyCoreBandInclusion
    {ε : ℝ} (hεpos : 0 < ε) {a b c d : ℝ}
    (hca : c ≤ a) (hbd : b ≤ d) :
    IsProperMap
      (relativeEntropyCoreBandInclusion (n := n) ε hca hbd) := by
  exact
    (isClosedEmbedding_relativeEntropyCoreBandInclusion
      hεpos hca hbd).isProperMap

@[simp] theorem relativeEntropyCoreBandInclusion_refl
    (ε a b : ℝ)
    (p : relativeEntropyCoreBand (n := n) ε a b) :
    relativeEntropyCoreBandInclusion ε (le_refl a) (le_refl b) p = p := by
  rfl

theorem relativeEntropyCoreBandInclusion_trans
    (ε : ℝ) {a b c d e f : ℝ}
    (hca : c ≤ a) (hbd : b ≤ d) (hec : e ≤ c) (hdf : d ≤ f)
    (p : relativeEntropyCoreBand (n := n) ε a b) :
    relativeEntropyCoreBandInclusion ε hec hdf
        (relativeEntropyCoreBandInclusion ε hca hbd p) =
      relativeEntropyCoreBandInclusion ε
        (hec.trans hca) (hbd.trans hdf) p := by
  rfl

end SouriauRelativeEntropyBandTopology
