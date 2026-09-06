import proofs.NonIsoConf3DeRhamCooperad
import proofs.NonIsoConf3DupontGysinModel

/-!
# Rank fork decision for the three-quadric Dupont/Gysin model

The key human-math correction is that the three quadric hypersurfaces

* `q(a)=0`,
* `q(b)=0`,
* `q(a-b)=0`

are not the `A₂` diagonal hyperplane arrangement.  In the Dupont/Orlik--Solomon
criterion, the Arnold relation appears for a dependent triple, i.e. when the
triple intersection has codimension `< 3`.  For the nondegenerate quadric
arrangement the expected geometric lemma is instead

`codim(Q_a ∩ Q_b ∩ Q_{a-b}) = 3`,

so the three divisor classes are OS-independent.  Therefore the alpha sector is
exterior on three degree-one classes, of rank `8`, not the `A₂` OS rank `6`.
Together with two independent flux/beta bits this selects the rank-`32`
product/Leray candidate, conditional on the geometric codimension and beta/Gysin
lemmas.
-/

namespace NonIsoConf3RankDecision

open NonIsoConf3DeRhamCooperad
open NonIsoConf3DupontGysinModel

/-- Codimension data for the resolved three-quadric arrangement.  These are the
geometric facts to discharge via the quadric dimension calculation / resolution.
-/
structure ThreeQuadricCodimData where
  codimQA : ℕ
  codimQB : ℕ
  codimQAB : ℕ
  codimQA_QB : ℕ
  codimQA_QAB : ℕ
  codimQB_QAB : ℕ
  codimTriple : ℕ

/-- The expected codimension data for three independent hypersurfaces. -/
def expectedCodimData : ThreeQuadricCodimData where
  codimQA := 1
  codimQB := 1
  codimQAB := 1
  codimQA_QB := 2
  codimQA_QAB := 2
  codimQB_QAB := 2
  codimTriple := 3

/-- In the Orlik--Solomon criterion, a triple of hypersurfaces is dependent only
when the triple intersection has codimension `< 3`. -/
def tripleDependent (C : ThreeQuadricCodimData) : Prop :=
  C.codimTriple < 3

/-- The expected three-quadric codimension data is independent, hence no
`A₂` Arnold relation is forced in the alpha sector. -/
theorem expected_triple_not_dependent : ¬ tripleDependent expectedCodimData := by
  unfold tripleDependent expectedCodimData
  norm_num

/-- Three independent alpha divisors give the exterior alpha rank `2^3=8`. -/
theorem independent_alpha_rank : 2 ^ 3 = 8 := by
  norm_num

/-- Two beta/flux bits give rank `2^2=4`. -/
theorem two_flux_rank : 2 ^ 2 = 4 := by
  norm_num

/-- The independent-alpha plus two-flux product rank is `32`. -/
theorem independent_alpha_flux_rank : 2 ^ 3 * 2 ^ 2 = 32 := by
  norm_num

/-- The OS-alpha alternative has rank `24`; it is smaller by `8`. -/
theorem os_alpha_rank_smaller :
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 :=
  product_vs_os_rank_gap

/-- Rank decision: the correct finite branch is the rank-`32`
product/Leray branch, not the rank-`24` OS-alpha branch. -/
theorem rank32_decision_from_dupont_independence :
    ¬ tripleDependent expectedCodimData ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  exact ⟨expected_triple_not_dependent, productBasis_card, osFluxBasis_card,
    product_vs_os_rank_gap⟩

end NonIsoConf3RankDecision
