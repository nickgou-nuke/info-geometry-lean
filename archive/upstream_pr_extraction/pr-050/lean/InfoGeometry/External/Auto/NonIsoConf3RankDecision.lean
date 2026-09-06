import InfoGeometry.External.Auto.NonIsoConf3DeRhamCooperad
import InfoGeometry.External.Auto.NonIsoConf3DupontGysinModel

/-!
# Finite rank-fork bookkeeping for three quadric divisors

This module compares two finite candidate bases under an explicitly configured
codimension table.  It computes the exterior and flux factors, the product rank,
the OS rank, and the resulting finite rank gap.
-/

namespace NonIsoConf3RankDecision

open NonIsoConf3DeRhamCooperad

/-- Plain numerical codimension data for three named divisors and their
intersections. -/
structure ThreeQuadricCodimData where
  codimQA : ℕ
  codimQB : ℕ
  codimQAB : ℕ
  codimQA_QB : ℕ
  codimQA_QAB : ℕ
  codimQB_QAB : ℕ
  codimTriple : ℕ

/-- The independent-hypersurface codimension configuration used for the finite
branch comparison.  This is data, not a proved geometric computation. -/
def expectedCodimData : ThreeQuadricCodimData where
  codimQA := 1
  codimQB := 1
  codimQAB := 1
  codimQA_QB := 2
  codimQA_QAB := 2
  codimQB_QAB := 2
  codimTriple := 3

/-- Numerical dependence predicate used by the finite comparison. -/
def tripleDependent (C : ThreeQuadricCodimData) : Prop :=
  C.codimTriple < 3

/-- The configured table is not dependent according to the numerical
predicate. -/
theorem configured_triple_not_dependent :
    ¬ tripleDependent expectedCodimData := by
  norm_num [tripleDependent, expectedCodimData]

/-- Cardinality of an exterior basis on three independent formal generators. -/
theorem exterior_three_rank : 2 ^ 3 = 8 := by
  norm_num

/-- Cardinality of two independent formal flux bits. -/
theorem two_flux_rank : 2 ^ 2 = 4 := by
  norm_num

/-- Product cardinality of the configured exterior and flux bits. -/
theorem configured_exterior_flux_rank : 2 ^ 3 * 2 ^ 2 = 32 := by
  norm_num

/-- The two already-defined finite candidate bases differ in cardinality by
`8`.  This is a finite combinatorial comparison only. -/
theorem finite_candidate_rank_gap :
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 :=
  product_vs_os_rank_gap

end NonIsoConf3RankDecision
