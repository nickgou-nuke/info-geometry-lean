import InfoGeometry.Canonical.SouriauRelativeEntropyBandTopology

namespace SouriauRelativeEntropyPersistenceQuotient

open SouriauRelativeEntropySublevel
open SouriauRelativeEntropySublevelDiagram

variable {n : ℕ}

/-- The lower KL sublevel viewed as a subset of an upper sublevel carrier. -/
def relativeEntropyLowerInUpper (ε c d : ℝ) :
    Set (relativeEntropyCoreSublevel (n := n) ε d) :=
  {p | p.1 ∈ relativeEntropyCoreSublevel (n := n) ε c}

theorem isClosed_relativeEntropyLowerInUpper
    {ε : ℝ} (hεpos : 0 < ε) (c d : ℝ) :
    IsClosed (relativeEntropyLowerInUpper (n := n) ε c d) := by
  exact (isClosed_relativeEntropyCoreSublevel hεpos c).preimage
    continuous_subtype_val

/-- Collapse the lower KL sublevel to one persistence basepoint. -/
def relativeEntropySublevelCollapseSetoid (ε c d : ℝ) :
    Setoid (relativeEntropyCoreSublevel (n := n) ε d) where
  r p q :=
    p = q ∨
      (p ∈ relativeEntropyLowerInUpper ε c d ∧
        q ∈ relativeEntropyLowerInUpper ε c d)
  iseqv := by
    constructor
    · intro p
      exact Or.inl rfl
    · intro p q hpq
      rcases hpq with hpq | hpq
      · exact Or.inl hpq.symm
      · exact Or.inr ⟨hpq.2, hpq.1⟩
    · intro p q r hpq hqr
      rcases hpq with rfl | hpq
      · exact hqr
      · rcases hqr with rfl | hqr
        · exact Or.inr hpq
        · exact Or.inr ⟨hpq.1, hqr.2⟩

/-- The persistence quotient `L_d / L_c` of compact KL sublevels. -/
abbrev RelativeEntropySublevelQuotient
    (ε c d : ℝ) : Type :=
  Quotient (relativeEntropySublevelCollapseSetoid (n := n) ε c d)

/-- Canonical projection from the upper KL sublevel to the persistence quotient. -/
def relativeEntropySublevelQuotientProjection
    (ε c d : ℝ) :
    relativeEntropyCoreSublevel (n := n) ε d →
      RelativeEntropySublevelQuotient (n := n) ε c d :=
  Quotient.mk (relativeEntropySublevelCollapseSetoid ε c d)

@[simp] theorem relativeEntropySublevelQuotientProjection_eq_iff
    (ε c d : ℝ)
    (p q : relativeEntropyCoreSublevel (n := n) ε d) :
    relativeEntropySublevelQuotientProjection ε c d p =
        relativeEntropySublevelQuotientProjection ε c d q ↔
      p = q ∨
        (p ∈ relativeEntropyLowerInUpper ε c d ∧
          q ∈ relativeEntropyLowerInUpper ε c d) := by
  exact Quotient.eq

theorem isQuotientMap_relativeEntropySublevelQuotientProjection
    (ε c d : ℝ) :
    Topology.IsQuotientMap
      (relativeEntropySublevelQuotientProjection
        (n := n) ε c d) := by
  letI : Setoid (relativeEntropyCoreSublevel (n := n) ε d) :=
    relativeEntropySublevelCollapseSetoid ε c d
  exact isQuotientMap_quotient_mk'

theorem continuous_relativeEntropySublevelQuotientProjection
    (ε c d : ℝ) :
    Continuous
      (relativeEntropySublevelQuotientProjection
        (n := n) ε c d) :=
  (isQuotientMap_relativeEntropySublevelQuotientProjection
    ε c d).continuous

theorem surjective_relativeEntropySublevelQuotientProjection
    (ε c d : ℝ) :
    Function.Surjective
      (relativeEntropySublevelQuotientProjection
        (n := n) ε c d) :=
  (isQuotientMap_relativeEntropySublevelQuotientProjection
    ε c d).surjective

theorem lower_sublevel_collapses
    (ε : ℝ) {c d : ℝ} (hcd : c ≤ d)
    (p q : relativeEntropyCoreSublevel (n := n) ε c) :
    relativeEntropySublevelQuotientProjection ε c d
        (relativeEntropyCoreSublevelInclusion ε hcd p) =
      relativeEntropySublevelQuotientProjection ε c d
        (relativeEntropyCoreSublevelInclusion ε hcd q) := by
  apply
    (relativeEntropySublevelQuotientProjection_eq_iff
      ε c d _ _).2
  exact Or.inr ⟨p.2, q.2⟩

theorem projection_eq_iff_of_not_mem_lower
    (ε c d : ℝ)
    (p q : relativeEntropyCoreSublevel (n := n) ε d)
    (hp : p ∉ relativeEntropyLowerInUpper ε c d) :
    relativeEntropySublevelQuotientProjection ε c d p =
        relativeEntropySublevelQuotientProjection ε c d q ↔
      p = q := by
  rw [relativeEntropySublevelQuotientProjection_eq_iff]
  constructor
  · intro hpq
    rcases hpq with hpq | hpq
    · exact hpq
    · exact False.elim (hp hpq.1)
  · exact Or.inl

theorem isClosed_collapse_relation
    {ε : ℝ} (hεpos : 0 < ε) (c d : ℝ) :
    IsClosed
      {pq :
          relativeEntropyCoreSublevel (n := n) ε d ×
            relativeEntropyCoreSublevel (n := n) ε d |
        (relativeEntropySublevelCollapseSetoid ε c d).r pq.1 pq.2} := by
  have hlower :=
    isClosed_relativeEntropyLowerInUpper
      (n := n) hεpos c d
  rw [show
    {pq :
        relativeEntropyCoreSublevel (n := n) ε d ×
          relativeEntropyCoreSublevel (n := n) ε d |
      (relativeEntropySublevelCollapseSetoid ε c d).r pq.1 pq.2} =
        {pq | pq.1 = pq.2} ∪
          relativeEntropyLowerInUpper ε c d ×ˢ
            relativeEntropyLowerInUpper ε c d by
      ext pq
      rfl]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (hlower.prod hlower)

theorem isCompact_univ_relativeEntropySublevelQuotient
    {ε : ℝ} (hεpos : 0 < ε) (c d : ℝ) :
    IsCompact
      (Set.univ :
        Set (RelativeEntropySublevelQuotient (n := n) ε c d)) := by
  letI : CompactSpace (relativeEntropyCoreSublevel (n := n) ε d) :=
    isCompact_iff_compactSpace.mp
      (isCompact_relativeEntropyCoreSublevel (n := n) hεpos d)
  rw [← Set.range_eq_univ.mpr
    (surjective_relativeEntropySublevelQuotientProjection
      (n := n) ε c d)]
  simpa only [Set.image_univ] using
    (isCompact_univ :
      IsCompact
        (Set.univ :
          Set (relativeEntropyCoreSublevel (n := n) ε d))).image
      (continuous_relativeEntropySublevelQuotientProjection
        (n := n) ε c d)

end SouriauRelativeEntropyPersistenceQuotient
