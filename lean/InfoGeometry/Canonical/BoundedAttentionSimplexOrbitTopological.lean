import InfoGeometry.Canonical.BoundedAttentionReadoutCompactTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Convex.StdSimplex

namespace InfoGeometry.Canonical.KANModuli

variable {B : ℝ} {K : ℕ} {V : Type*}
variable [TopologicalSpace V] [Fact (0 < K)]

/-- A quotient point has a simplex representative among its expert
coordinates.  This predicate does not replace the ambient KAN quotient by a
separate simplex quotient. -/
def IsSimplexOrbit (q : KANModuliSpace ℝ K) : Prop :=
  ∃ p : stdSimplex ℝ (Fin K),
    quotientMap (V := ℝ) (K := K) (p : Fin K → ℝ) = q

theorem boundedExpertSoftmaxOnModuli_quotientMap_mem_simplexOrbit
    (p : BoundedExpertAttentionVector B V K) :
    IsSimplexOrbit
      (boundedExpertSoftmaxOnModuli (B := B) (V := V) (K := K)
        (quotientMap (V := Set.Icc (-B) B × V) (K := K) p)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  refine ⟨⟨boundedExpertSoftmaxVector p,
    by
      simpa [boundedExpertSoftmaxVector] using
        InfoGeometry.Topology.latentSoftmax_mem_stdSimplex
          (fun p : BoundedExpertAttentionVector B V K =>
            fun j => ((p j).1 : ℝ)) p⟩, ?_⟩
  calc
    quotientMap (V := ℝ) (K := K) (boundedExpertSoftmaxVector p)
        = boundedExpertSoftmaxOrbitReadout p := rfl
    _ = boundedExpertSoftmaxOnModuli (B := B) (V := V) (K := K)
          (quotientMap (V := Set.Icc (-B) B × V) (K := K) p) := by
      rw [boundedExpertSoftmaxOnModuli]
      exact (invariantLift_quotientMap boundedExpertSoftmaxOrbitReadout
        boundedExpertSoftmaxOrbitReadout_smul p).symm

theorem boundedExpertSoftmaxOnModuli_range_subset_simplexOrbit :
    Set.range
        (boundedExpertSoftmaxOnModuli (B := B) (V := V) (K := K)) ⊆
      {q : KANModuliSpace ℝ K | IsSimplexOrbit q} := by
  rintro q ⟨p, rfl⟩
  refine Quotient.inductionOn p ?_
  intro p
  exact boundedExpertSoftmaxOnModuli_quotientMap_mem_simplexOrbit
    (B := B) (V := V) (K := K) p

end InfoGeometry.Canonical.KANModuli
