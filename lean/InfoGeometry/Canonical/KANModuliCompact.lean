import InfoGeometry.Canonical.KANModuliTopology

namespace InfoGeometry.Canonical.KANModuli

variable {K : ℕ} {V : Type*} [TopologicalSpace V]

/--
The finite expert-coordinate quotient is compact whenever the expert space is
compact.

The proof uses compactness of the finite product `Fin K → V` and the fact that
the quotient projection is a continuous surjection.  No separation or
optimization algorithm or convergence theorem is included here; the final
lemma records only the ordinary compact-space minimum principle.
-/
instance kanModuliSpace_compact [CompactSpace V] :
    CompactSpace (KANModuliSpace V K) where
  isCompact_univ := by
    have hrange :
        IsCompact (Set.range (quotientMap (V := V) (K := K))) :=
      isCompact_range (continuous_quotientMap (V := V) (K := K))
    rw [Set.range_eq_univ.2 (quotientMap_surjective (V := V) (K := K))] at hrange
    exact hrange

theorem exists_global_minimum_on_kanModuli
    [CompactSpace V] [Nonempty V]
    (f : KANModuliSpace V K → ℝ) (hf : Continuous f) :
    ∃ q, ∀ q', f q ≤ f q' := by
  classical
  have hq : (Set.univ : Set (KANModuliSpace V K)).Nonempty := by
    let v : ExpertVector V K :=
      fun _ => Classical.choice (inferInstance : Nonempty V)
    exact ⟨quotientMap (V := V) (K := K) v, Set.mem_univ _⟩
  letI : Nonempty (KANModuliSpace V K) := ⟨hq.choose⟩
  rcases (isCompact_univ :
      IsCompact (Set.univ : Set (KANModuliSpace V K))).exists_isMinOn
      hq hf.continuousOn with ⟨q, hq', hmin⟩
  refine ⟨q, ?_⟩
  intro q'
  exact hmin (Set.mem_univ q')

theorem exists_global_maximum_on_kanModuli
    [CompactSpace V] [Nonempty V]
    (f : KANModuliSpace V K → ℝ) (hf : Continuous f) :
    ∃ q, ∀ q', f q' ≤ f q := by
  rcases exists_global_minimum_on_kanModuli (fun q => -f q) hf.neg with
    ⟨q, hq⟩
  refine ⟨q, ?_⟩
  intro q'
  have h := hq q'
  linarith

end InfoGeometry.Canonical.KANModuli
