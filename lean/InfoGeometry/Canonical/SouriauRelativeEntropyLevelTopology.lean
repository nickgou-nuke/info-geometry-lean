import InfoGeometry.Canonical.SouriauRelativeEntropySublevelDiagram
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace SouriauRelativeEntropyLevelTopology

open SouriauRelativeEntropy
open SouriauRelativeEntropySimplex
open SouriauRelativeEntropySublevel

variable {n : ℕ}

/-- The exact KL level inside the compact positive simplex core. -/
def relativeEntropyCoreLevel (ε c : ℝ) :
    Set (positiveSimplexCorePair (n := n) ε) :=
  {p | relativeEntropy p.1.1 p.1.2 = c}

theorem isClosed_relativeEntropyCoreLevel
    {ε : ℝ} (hεpos : 0 < ε) (c : ℝ) :
    IsClosed (relativeEntropyCoreLevel (n := n) ε c) := by
  exact
    isClosed_relativeEntropy_level_set_on_positiveSimplexCorePair
      hεpos c

theorem isCompact_relativeEntropyCoreLevel
    {ε : ℝ} (hεpos : 0 < ε) (c : ℝ) :
    IsCompact (relativeEntropyCoreLevel (n := n) ε c) := by
  letI : CompactSpace (positiveSimplexCorePair (n := n) ε) :=
    isCompact_iff_compactSpace.mp
      (isCompact_positiveSimplexCorePair ε)
  exact (isClosed_relativeEntropyCoreLevel hεpos c).isCompact

theorem relativeEntropyCoreLevel_subset_sublevel
    (ε c : ℝ) :
    relativeEntropyCoreLevel (n := n) ε c ⊆
      relativeEntropyCoreSublevel (n := n) ε c := by
  intro p hp
  exact hp.le

theorem relativeEntropyCoreLevel_eq_empty_of_neg
    {ε c : ℝ} (hεpos : 0 < ε) (hc : c < 0) :
    relativeEntropyCoreLevel (n := n) ε c = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  have hnonneg :=
    relativeEntropy_nonneg_on_positiveSimplexCorePair hεpos p
  change relativeEntropy p.1.1 p.1.2 = c at hp
  linarith

theorem relativeEntropyCoreLevel_zero_eq_diagonal
    {ε : ℝ} (hεpos : 0 < ε) :
    relativeEntropyCoreLevel (n := n) ε 0 =
      {p | p.1.1 = p.1.2} := by
  ext p
  exact
    relativeEntropy_eq_zero_iff_on_positiveSimplexCorePair
      hεpos p

theorem relativeEntropyCoreLevel_nonempty_iff_mem_range
    (ε c : ℝ) :
    (relativeEntropyCoreLevel (n := n) ε c).Nonempty ↔
      c ∈ relativeEntropyCoreRange (n := n) ε := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, hp⟩

theorem relativeEntropyCoreLevel_nonempty_iff_mem_Icc
    (hn : 0 < n) {ε c : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    (relativeEntropyCoreLevel (n := n) ε c).Nonempty ↔
      c ∈ Set.Icc 0
        (sSup (relativeEntropyCoreRange (n := n) ε)) := by
  rw [relativeEntropyCoreLevel_nonempty_iff_mem_range]
  exact Set.ext_iff.mp
    (relativeEntropyCoreRange_eq_Icc_zero_sSup
      hn hεpos hεupper) c

/-- The canonical inclusion of an exact level into a containing KL sublevel. -/
def relativeEntropyCoreLevelInclusion
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d) :
    relativeEntropyCoreLevel (n := n) ε c →
      relativeEntropyCoreSublevel (n := n) ε d :=
  fun p => ⟨p.1, p.2.le.trans hcd⟩

@[simp] theorem relativeEntropyCoreLevelInclusion_coe
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d)
    (p : relativeEntropyCoreLevel (n := n) ε c) :
    (relativeEntropyCoreLevelInclusion ε hcd p :
      positiveSimplexCorePair (n := n) ε) = p.1 := rfl

theorem continuous_relativeEntropyCoreLevelInclusion
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d) :
    Continuous (relativeEntropyCoreLevelInclusion (n := n) ε hcd) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem injective_relativeEntropyCoreLevelInclusion
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d) :
    Function.Injective
      (relativeEntropyCoreLevelInclusion (n := n) ε hcd) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg
    (fun r : relativeEntropyCoreSublevel (n := n) ε d => r.1) hpq

theorem isClosedEmbedding_relativeEntropyCoreLevelInclusion
    {ε : ℝ} (hεpos : 0 < ε) {c d : ℝ} (hcd : c ≤ d) :
    Topology.IsClosedEmbedding
      (relativeEntropyCoreLevelInclusion (n := n) ε hcd) := by
  letI : CompactSpace (relativeEntropyCoreLevel (n := n) ε c) :=
    isCompact_iff_compactSpace.mp
      (isCompact_relativeEntropyCoreLevel (n := n) hεpos c)
  exact
    (continuous_relativeEntropyCoreLevelInclusion
      (n := n) ε hcd).isClosedEmbedding
        (injective_relativeEntropyCoreLevelInclusion
          (n := n) ε hcd)

theorem isProperMap_relativeEntropyCoreLevelInclusion
    {ε : ℝ} (hεpos : 0 < ε) {c d : ℝ} (hcd : c ≤ d) :
    IsProperMap
      (relativeEntropyCoreLevelInclusion (n := n) ε hcd) := by
  exact
    (isClosedEmbedding_relativeEntropyCoreLevelInclusion
      hεpos hcd).isProperMap

end SouriauRelativeEntropyLevelTopology
