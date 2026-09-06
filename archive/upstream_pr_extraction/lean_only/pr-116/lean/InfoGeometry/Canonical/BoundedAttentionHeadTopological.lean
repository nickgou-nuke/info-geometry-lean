import InfoGeometry.Canonical.BoundedAttentionLatentModuliTopological

namespace InfoGeometry.Canonical.KANModuli

variable {B : ℝ} {K : ℕ} {V : Type*}
variable [TopologicalSpace V] [AddCommMonoid V] [ContinuousAdd V]
variable [SMul ℝ V] [ContinuousSMul ℝ V]
variable [Fact (0 < K)]

/-- The value readout of a bounded symbolic attention field. -/
noncomputable def boundedExpertAttentionHead
    (p : BoundedExpertAttentionVector B V K) : V :=
  expertAttentionHead (boundedExpertForget p)

theorem boundedExpertAttentionHead_smul
    (σ : Equiv.Perm (Fin K))
    (p : BoundedExpertAttentionVector B V K) :
    boundedExpertAttentionHead (σ • p) = boundedExpertAttentionHead p := by
  unfold boundedExpertAttentionHead
  rw [boundedExpertForget_smul]
  exact expertAttentionHead_smul σ (boundedExpertForget p)

theorem continuous_boundedExpertAttentionHead :
    Continuous (boundedExpertAttentionHead (B := B) (V := V) (K := K)) := by
  exact continuous_expertAttentionHead.comp continuous_boundedExpertForget

noncomputable def boundedExpertAttentionHeadOnModuli :
    KANModuliSpace (Set.Icc (-B) B × V) K → V :=
  invariantLift boundedExpertAttentionHead boundedExpertAttentionHead_smul

theorem continuous_boundedExpertAttentionHeadOnModuli :
    Continuous (boundedExpertAttentionHeadOnModuli (B := B) (V := V) (K := K)) := by
  exact continuous_invariantLift boundedExpertAttentionHead
    continuous_boundedExpertAttentionHead boundedExpertAttentionHead_smul

@[simp] theorem boundedExpertAttentionHeadOnModuli_quotientMap
    (p : BoundedExpertAttentionVector B V K) :
    boundedExpertAttentionHeadOnModuli (B := B) (V := V) (K := K)
      (quotientMap (V := Set.Icc (-B) B × V) (K := K) p) =
        boundedExpertAttentionHead p := by
  exact invariantLift_quotientMap boundedExpertAttentionHead
    boundedExpertAttentionHead_smul p

theorem boundedExpertAttentionHeadOnModuli_fiber_isClosed
    [T1Space V] (v : V) :
    IsClosed {q : KANModuliSpace (Set.Icc (-B) B × V) K |
      boundedExpertAttentionHeadOnModuli (B := B) (V := V) (K := K) q = v} := by
  change IsClosed
    ((boundedExpertAttentionHeadOnModuli (B := B) (V := V) (K := K)) ⁻¹'
      ({v} : Set V))
  exact isClosed_singleton.preimage
    (continuous_boundedExpertAttentionHeadOnModuli (B := B) (V := V) (K := K))

theorem isCompact_range_boundedExpertAttentionHeadOnModuli
    [CompactSpace V] :
    IsCompact (Set.range
      (boundedExpertAttentionHeadOnModuli (B := B) (V := V) (K := K))) :=
  isCompact_range
    (continuous_boundedExpertAttentionHeadOnModuli (B := B) (V := V) (K := K))

theorem boundedExpertAttentionHeadOnModuli_fiber_isCompact
    [CompactSpace V] [T1Space V] (v : V) :
    IsCompact {q : KANModuliSpace (Set.Icc (-B) B × V) K |
      boundedExpertAttentionHeadOnModuli (B := B) (V := V) (K := K) q = v} :=
  IsClosed.isCompact
    (boundedExpertAttentionHeadOnModuli_fiber_isClosed
      (B := B) (V := V) (K := K) v)

end InfoGeometry.Canonical.KANModuli
