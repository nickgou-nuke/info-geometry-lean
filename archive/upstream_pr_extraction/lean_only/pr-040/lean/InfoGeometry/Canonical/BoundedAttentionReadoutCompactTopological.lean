import InfoGeometry.Canonical.BoundedAttentionHeadTopological

namespace InfoGeometry.Canonical.KANModuli

variable {B : ℝ} {K : ℕ} {V : Type*}
variable [TopologicalSpace V] [Fact (0 < K)]

theorem isCompact_range_boundedExpertSoftmaxOnModuli
    [CompactSpace V] :
    IsCompact (Set.range
      (boundedExpertSoftmaxOnModuli (B := B) (V := V) (K := K))) :=
  isCompact_range
    (continuous_boundedExpertSoftmaxOnModuli (B := B) (V := V) (K := K))

theorem isCompact_range_boundedExpertSoftmaxConcentrationOnModuli
    [CompactSpace V] :
    IsCompact (Set.range
      (boundedExpertSoftmaxConcentrationOnModuli
        (B := B) (V := V) (K := K))) :=
  isCompact_range
    (continuous_boundedExpertSoftmaxConcentrationOnModuli
      (B := B) (V := V) (K := K))

theorem isClosed_range_boundedExpertSoftmaxConcentrationOnModuli
    [CompactSpace V] :
    IsClosed (Set.range
      (boundedExpertSoftmaxConcentrationOnModuli
        (B := B) (V := V) (K := K))) :=
  (isCompact_range_boundedExpertSoftmaxConcentrationOnModuli
    (B := B) (V := V) (K := K)).isClosed

theorem isCompact_range_boundedExpertSoftmaxEntropyOnModuli
    [CompactSpace V] :
    IsCompact (Set.range
      (boundedExpertSoftmaxEntropyOnModuli (B := B) (V := V) (K := K))) :=
  isCompact_range
    (continuous_boundedExpertSoftmaxEntropyOnModuli
      (B := B) (V := V) (K := K))

theorem isClosed_range_boundedExpertSoftmaxEntropyOnModuli
    [CompactSpace V] :
    IsClosed (Set.range
      (boundedExpertSoftmaxEntropyOnModuli (B := B) (V := V) (K := K))) :=
  (isCompact_range_boundedExpertSoftmaxEntropyOnModuli
    (B := B) (V := V) (K := K)).isClosed

end InfoGeometry.Canonical.KANModuli
