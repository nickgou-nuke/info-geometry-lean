import InfoGeometry.External.Auto.NonIsoConf3DeRhamCohomologyFormula
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.QuadricConf3BraidingCooperadBridge

/-!
# Product-candidate cardinality and arity-three cooperad counts

This module combines the maintained finite product-basis cardinality, the
internal/outer edge counts for an arity-three block decomposition, and the two
exact triangle-cycle identities.
-/

namespace CooperadEnvironmentalRank32

open QuadraticConfiguration3
open NonIsoConf3DeRhamCooperad
open NonIsoConf3DeRhamCohomologyFormula
open QuadricConf3BraidingCooperadBridge
open VertexAlgebraBraidingCocycle
open VertexAlgebraBraidingCocycle.EdgeSystem

/-- Finite product-candidate cardinality, cooperad edge counts, and exact
triangle-cycle identities. -/
theorem product_candidate_cooperad_cycle_summary
    (b : BlockDecomp3)
    (S : EdgeSystem Vertex3) (potential : Vertex3 → ℝ)
    (hExact : IsExact S potential) :
    Fintype.card ProductBasis = 32 ∧
    (arityThreeInternalEdges b).card = 1 ∧
    (arityThreeOuterEdges b).card = 2 ∧
    cycleEntropyProduction S triangle012 = 0 ∧
    cycleEntropyProduction S triangle021 = 0 := by
  exact ⟨productBasis_card,
    (arityThree_cooperad_partition_counts b).1,
    (arityThree_cooperad_partition_counts b).2,
    (exact_three_vertex_cycle_summary S potential hExact).1,
    (exact_three_vertex_cycle_summary S potential hExact).2⟩

end CooperadEnvironmentalRank32
