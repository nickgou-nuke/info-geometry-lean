import InfoGeometry.Canonical.SouriauRelativeEntropySimplexTopology

namespace SouriauRelativeEntropySublevel

open SouriauRelativeEntropy
open SouriauRelativeEntropySimplex

variable {n : ℕ}

/-- Compact-core KL sublevel filtration. -/
def relativeEntropyCoreSublevel (ε c : ℝ) :
    Set (positiveSimplexCorePair (n := n) ε) :=
  {p | relativeEntropy p.1.1 p.1.2 ≤ c}

theorem isClosed_relativeEntropyCoreSublevel
    {ε : ℝ} (hεpos : 0 < ε) (c : ℝ) :
    IsClosed (relativeEntropyCoreSublevel (n := n) ε c) := by
  exact isClosed_Iic.preimage
    (continuous_relativeEntropy_on_subtype _
      (positiveSimplexCorePair_subset_positiveOrthantPair hεpos))

theorem isCompact_relativeEntropyCoreSublevel
    {ε : ℝ} (hεpos : 0 < ε) (c : ℝ) :
    IsCompact (relativeEntropyCoreSublevel (n := n) ε c) := by
  letI : CompactSpace (positiveSimplexCorePair (n := n) ε) :=
    isCompact_iff_compactSpace.mp (isCompact_positiveSimplexCorePair ε)
  exact (isClosed_relativeEntropyCoreSublevel hεpos c).isCompact

theorem relativeEntropyCoreSublevel_mono
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d) :
    relativeEntropyCoreSublevel (n := n) ε c ⊆
      relativeEntropyCoreSublevel (n := n) ε d := by
  intro p hp
  exact hp.trans hcd

theorem relativeEntropyCoreSublevel_inter
    (ε c d : ℝ) :
    relativeEntropyCoreSublevel (n := n) ε c ∩
        relativeEntropyCoreSublevel (n := n) ε d =
      relativeEntropyCoreSublevel (n := n) ε (min c d) := by
  ext p
  simp [relativeEntropyCoreSublevel]

theorem relativeEntropyCoreSublevel_nonempty
    (hn : 0 < n) {ε c : ℝ} (hεupper : ε ≤ (n : ℝ)⁻¹)
    (hc : 0 ≤ c) :
    (relativeEntropyCoreSublevel (n := n) ε c).Nonempty := by
  rcases positiveSimplexCore_nonempty hn hεupper with ⟨P, hP⟩
  refine ⟨⟨(P, P), hP, hP⟩, ?_⟩
  change relativeEntropy P P ≤ c
  rw [relativeEntropy_self_zero]
  exact hc

theorem relativeEntropyCoreSublevel_eq_empty_of_neg
    {ε c : ℝ} (hεpos : 0 < ε) (hc : c < 0) :
    relativeEntropyCoreSublevel (n := n) ε c = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  change relativeEntropy p.1.1 p.1.2 ≤ c at hp
  have hnonneg :=
    relativeEntropy_nonneg_on_positiveSimplexCorePair hεpos p
  linarith

theorem relativeEntropyCoreSublevel_zero_eq_diagonal
    {ε : ℝ} (hεpos : 0 < ε) :
    relativeEntropyCoreSublevel (n := n) ε 0 =
      {p | p.1.1 = p.1.2} := by
  ext p
  constructor
  · intro hp
    have hzero : relativeEntropy p.1.1 p.1.2 = 0 :=
      le_antisymm hp
        (relativeEntropy_nonneg_on_positiveSimplexCorePair hεpos p)
    exact
      (relativeEntropy_eq_zero_iff_on_positiveSimplexCorePair
        hεpos p).1 hzero
  · intro hp
    exact le_of_eq
      ((relativeEntropy_eq_zero_iff_on_positiveSimplexCorePair
        hεpos p).2 hp)

theorem relativeEntropyCoreSublevel_log_inv_epsilon_eq_univ
    {ε : ℝ} (hεpos : 0 < ε) :
    relativeEntropyCoreSublevel (n := n) ε (Real.log (1 / ε)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact
    relativeEntropy_le_log_inv_epsilon_on_positiveSimplexCorePair
      hεpos p

end SouriauRelativeEntropySublevel
