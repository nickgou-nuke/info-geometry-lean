import InfoGeometry.Canonical.AttentionExpertSimplexModuliTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KANModuliCompact

open scoped BigOperators

namespace InfoGeometry.Canonical.KANModuli

open InfoGeometry.Convex.LogSumExp

variable {B : ℝ} {K : ℕ} {V : Type*}
variable [TopologicalSpace V] [Fact (0 < K)]

/-- Expert parameters whose logits live in a compact interval.  The subtype
keeps the boundedness invariant in the type rather than as an external claim. -/
abbrev BoundedExpertAttentionVector (B : ℝ) (V : Type*) (K : ℕ) :=
  Fin K → (Set.Icc (-B) B × V)

noncomputable def boundedExpertSoftmaxVector
    (p : BoundedExpertAttentionVector B V K) : Fin K → ℝ :=
  fun i => softmax (fun j => ((p j).1 : ℝ)) i

theorem boundedExpertSoftmaxVector_smul
    (σ : Equiv.Perm (Fin K))
    (p : BoundedExpertAttentionVector B V K) :
    boundedExpertSoftmaxVector (σ • p) =
      σ • boundedExpertSoftmaxVector p := by
  ext i
  change softmax (fun j => ((p (σ.symm j)).1 : ℝ)) i =
    softmax (fun j => ((p j).1 : ℝ)) (σ.symm i)
  exact softmax_reindex σ (fun j => ((p j).1 : ℝ)) i

noncomputable def boundedExpertSoftmaxOrbitReadout
    (p : BoundedExpertAttentionVector B V K) : KANModuliSpace ℝ K :=
  quotientMap (V := ℝ) (K := K) (boundedExpertSoftmaxVector p)

theorem boundedExpertSoftmaxOrbitReadout_smul
    (σ : Equiv.Perm (Fin K))
    (p : BoundedExpertAttentionVector B V K) :
    boundedExpertSoftmaxOrbitReadout (σ • p) =
      boundedExpertSoftmaxOrbitReadout p := by
  unfold boundedExpertSoftmaxOrbitReadout
  rw [show boundedExpertSoftmaxVector (σ • p) =
      σ • boundedExpertSoftmaxVector p by
        ext i
        change softmax (fun j => ((p (σ.symm j)).1 : ℝ)) i =
          softmax (fun j => ((p j).1 : ℝ)) (σ.symm i)
        exact softmax_reindex σ (fun j => ((p j).1 : ℝ)) i]
  exact Quotient.sound ⟨σ, rfl⟩

theorem continuous_boundedExpertSoftmaxVector :
    Continuous (boundedExpertSoftmaxVector (B := B) (V := V) (K := K)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  apply continuous_pi
  intro i
  have hlogits : ∀ j : Fin K,
      Continuous (fun p : BoundedExpertAttentionVector B V K =>
        ((p j).1 : ℝ)) := by
    intro j
    exact continuous_subtype_val.comp (continuous_fst.comp (continuous_apply j))
  exact InfoGeometry.Topology.continuous_latentSoftmax_coordinate
    (fun p : BoundedExpertAttentionVector B V K => fun j => ((p j).1 : ℝ))
    hlogits i

theorem continuous_boundedExpertSoftmaxOrbitReadout :
    Continuous
      (boundedExpertSoftmaxOrbitReadout (B := B) (V := V) (K := K)) := by
  exact continuous_quotientMap.comp continuous_boundedExpertSoftmaxVector

noncomputable def boundedExpertSoftmaxOnModuli :
    KANModuliSpace (Set.Icc (-B) B × V) K → KANModuliSpace ℝ K :=
  invariantLift boundedExpertSoftmaxOrbitReadout
    boundedExpertSoftmaxOrbitReadout_smul

theorem continuous_boundedExpertSoftmaxOnModuli :
    Continuous
      (boundedExpertSoftmaxOnModuli (B := B) (V := V) (K := K)) := by
  exact continuous_invariantLift boundedExpertSoftmaxOrbitReadout
    continuous_boundedExpertSoftmaxOrbitReadout
    boundedExpertSoftmaxOrbitReadout_smul

noncomputable def boundedExpertSoftmaxConcentration
    (p : BoundedExpertAttentionVector B V K) : ℝ :=
  ∑ i : Fin K, (softmax (fun j => ((p j).1 : ℝ)) i) ^ 2

theorem boundedExpertSoftmaxConcentration_smul
    (σ : Equiv.Perm (Fin K))
    (p : BoundedExpertAttentionVector B V K) :
    boundedExpertSoftmaxConcentration (σ • p) =
      boundedExpertSoftmaxConcentration p := by
  change
    (∑ i : Fin K, (softmax (fun j => ((p (σ.symm j)).1 : ℝ)) i) ^ 2) =
      ∑ i : Fin K, (softmax (fun j => ((p j).1 : ℝ)) i) ^ 2
  calc
    (∑ i : Fin K, (softmax (fun j => ((p (σ.symm j)).1 : ℝ)) i) ^ 2) =
        ∑ i : Fin K, (softmax (fun j => ((p j).1 : ℝ)) (σ.symm i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [softmax_reindex σ (fun j => ((p j).1 : ℝ)) i]
    _ = ∑ i : Fin K, (softmax (fun j => ((p j).1 : ℝ)) i) ^ 2 := by
      simpa using
        (Fintype.sum_equiv σ.symm
          (fun i : Fin K => (softmax (fun j => ((p j).1 : ℝ)) (σ.symm i)) ^ 2)
          (fun i : Fin K => (softmax (fun j => ((p j).1 : ℝ)) i) ^ 2)
          (fun _ => rfl))

theorem continuous_boundedExpertSoftmaxConcentration :
    Continuous
      (boundedExpertSoftmaxConcentration (B := B) (V := V) (K := K)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  unfold boundedExpertSoftmaxConcentration
  apply continuous_finset_sum
  intro i hi
  have hlogits : ∀ j : Fin K,
      Continuous (fun p : BoundedExpertAttentionVector B V K =>
        ((p j).1 : ℝ)) := by
    intro j
    exact continuous_subtype_val.comp (continuous_fst.comp (continuous_apply j))
  have hweight : Continuous (fun p : BoundedExpertAttentionVector B V K =>
      softmax (fun j => ((p j).1 : ℝ)) i) :=
    InfoGeometry.Topology.continuous_latentSoftmax_coordinate
      (fun p : BoundedExpertAttentionVector B V K =>
        fun j => ((p j).1 : ℝ)) hlogits i
  exact hweight.pow 2

noncomputable def boundedExpertSoftmaxConcentrationOnModuli :
    KANModuliSpace (Set.Icc (-B) B × V) K → ℝ :=
  invariantLift boundedExpertSoftmaxConcentration
    boundedExpertSoftmaxConcentration_smul

theorem continuous_boundedExpertSoftmaxConcentrationOnModuli :
    Continuous (boundedExpertSoftmaxConcentrationOnModuli
      (B := B) (V := V) (K := K)) := by
  exact continuous_invariantLift boundedExpertSoftmaxConcentration
    continuous_boundedExpertSoftmaxConcentration
    boundedExpertSoftmaxConcentration_smul

theorem boundedExpertSoftmaxConcentration_global_minimum
    [CompactSpace V] [Nonempty V] (hB : 0 ≤ B) :
    ∃ q, ∀ q',
      boundedExpertSoftmaxConcentrationOnModuli (B := B) (V := V) (K := K) q ≤
        boundedExpertSoftmaxConcentrationOnModuli (B := B) (V := V) (K := K) q' := by
  letI : Nonempty (Set.Icc (-B) B) :=
    ⟨⟨0, by constructor <;> linarith⟩⟩
  exact exists_global_minimum_on_kanModuli
    (boundedExpertSoftmaxConcentrationOnModuli (B := B) (V := V) (K := K))
    (continuous_boundedExpertSoftmaxConcentrationOnModuli (B := B) (V := V) (K := K))

theorem boundedExpertSoftmaxConcentration_levelSet_isCompact
    [CompactSpace V] (c : ℝ) :
    IsCompact {q : KANModuliSpace (Set.Icc (-B) B × V) K |
      boundedExpertSoftmaxConcentrationOnModuli (B := B) (V := V) (K := K) q = c} := by
  exact isCompact_levelSet_on_kanModuli
    (boundedExpertSoftmaxConcentrationOnModuli (B := B) (V := V) (K := K))
    (continuous_boundedExpertSoftmaxConcentrationOnModuli (B := B) (V := V) (K := K)) c

noncomputable def boundedExpertForget
    (p : BoundedExpertAttentionVector B V K) : ExpertAttentionVector V K :=
  fun j => (((p j).1 : ℝ), (p j).2)

theorem boundedExpertForget_smul
    (σ : Equiv.Perm (Fin K))
    (p : BoundedExpertAttentionVector B V K) :
    boundedExpertForget (σ • p) = σ • boundedExpertForget p := by
  funext j
  rfl

theorem continuous_boundedExpertForget :
    Continuous (boundedExpertForget (B := B) (V := V) (K := K)) := by
  apply continuous_pi
  intro j
  exact (continuous_subtype_val.comp (continuous_fst.comp (continuous_apply j))).prodMk
    (continuous_snd.comp (continuous_apply j))

noncomputable def boundedExpertSoftmaxEntropy
    (p : BoundedExpertAttentionVector B V K) : ℝ :=
  expertSoftmaxEntropy (boundedExpertForget p)

theorem boundedExpertSoftmaxEntropy_smul
    (σ : Equiv.Perm (Fin K))
    (p : BoundedExpertAttentionVector B V K) :
    boundedExpertSoftmaxEntropy (σ • p) = boundedExpertSoftmaxEntropy p := by
  unfold boundedExpertSoftmaxEntropy
  rw [boundedExpertForget_smul]
  exact expertSoftmaxEntropy_smul σ (boundedExpertForget p)

theorem continuous_boundedExpertSoftmaxEntropy :
    Continuous (boundedExpertSoftmaxEntropy (B := B) (V := V) (K := K)) := by
  exact continuous_expertSoftmaxEntropy.comp continuous_boundedExpertForget

noncomputable def boundedExpertSoftmaxEntropyOnModuli :
    KANModuliSpace (Set.Icc (-B) B × V) K → ℝ :=
  invariantLift boundedExpertSoftmaxEntropy boundedExpertSoftmaxEntropy_smul

theorem continuous_boundedExpertSoftmaxEntropyOnModuli :
    Continuous (boundedExpertSoftmaxEntropyOnModuli
      (B := B) (V := V) (K := K)) := by
  exact continuous_invariantLift boundedExpertSoftmaxEntropy
    continuous_boundedExpertSoftmaxEntropy boundedExpertSoftmaxEntropy_smul

theorem boundedExpertSoftmaxEntropy_global_maximum
    [CompactSpace V] [Nonempty V] (hB : 0 ≤ B) :
    ∃ q, ∀ q',
      boundedExpertSoftmaxEntropyOnModuli (B := B) (V := V) (K := K) q' ≤
        boundedExpertSoftmaxEntropyOnModuli (B := B) (V := V) (K := K) q := by
  letI : Nonempty (Set.Icc (-B) B) :=
    ⟨⟨0, by constructor <;> linarith⟩⟩
  exact exists_global_maximum_on_kanModuli
    (boundedExpertSoftmaxEntropyOnModuli (B := B) (V := V) (K := K))
    (continuous_boundedExpertSoftmaxEntropyOnModuli (B := B) (V := V) (K := K))

theorem boundedExpertSoftmaxEntropy_levelSet_isCompact
    [CompactSpace V] (c : ℝ) :
    IsCompact {q : KANModuliSpace (Set.Icc (-B) B × V) K |
      boundedExpertSoftmaxEntropyOnModuli (B := B) (V := V) (K := K) q = c} := by
  exact isCompact_levelSet_on_kanModuli
    (boundedExpertSoftmaxEntropyOnModuli (B := B) (V := V) (K := K))
    (continuous_boundedExpertSoftmaxEntropyOnModuli (B := B) (V := V) (K := K)) c

end InfoGeometry.Canonical.KANModuli
