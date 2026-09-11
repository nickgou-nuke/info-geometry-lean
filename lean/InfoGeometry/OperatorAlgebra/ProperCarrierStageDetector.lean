import InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.OperatorAlgebra.ProperCarrierStageDetector

Concrete finite-stage detection for proper self-dual cone carriers.

This file specializes the abstract detector interface from
`ProperCarrierSelfDualConeExtension` to the common owner-side situation where a
proper carrier family comes with an explicit stage index assigning each element
of the ambient algebra to a finite carrier stage.

#### BUCKET 1: CLOSED FINITE/COLIMIT THEOREMS
[dualPositive_implies_finiteStage_membership,
 properCarrier_selfDualCone_extends_of_stageIndex,
 iUnion_eq_univ_of_finiteCarrierStage,
 properCarrier_stageIndex_mem_iff_dual_positive,
 properCarrier_selfDualCone_extends_to_univ_of_stageIndex]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The extension theorem is conditional on:
* monotone finite-stage carrier inclusions;
* self-duality at each stage;
* an explicit stage-index witness placing every ambient element in a finite
  carrier stage.

#### BUCKET 3: OPEN CLOSURE DEBT
No analytic modular-theory claim is made here.  This file only converts a
concrete finite-stage indexing witness into the detector premise needed for the
proper-carrier self-dual cone colimit theorem.
-/

namespace InfoGeometry.OperatorAlgebra.ProperCarrierStageDetector

open InfoGeometry.OperatorAlgebra.SelfDualConeColimit
open InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension

/--
A concrete proper-carrier witness: every ambient element is assigned to a finite
carrier stage containing it.
-/
structure HasFiniteCarrierStage {E : Type*} (K : ℕ → Set E) where
  stage : E → ℕ
  mem_stage : ∀ x : E, x ∈ K (stage x)

/--
A concrete stage index yields the detector premise: if an element pairs
nonnegatively with every element of the directed union, then it already belongs
to some finite carrier stage.
-/
theorem dualPositive_implies_finiteStage_membership
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hstage : HasFiniteCarrierStage K) :
    ∀ x, (∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y) → ∃ n : ℕ, x ∈ K n := by
  intro x _
  exact ⟨hstage.stage x, hstage.mem_stage x⟩

/--
Proper-carrier extension theorem from an explicit stage-index witness.
-/
theorem properCarrier_selfDualCone_extends_of_stageIndex
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    (hstage : HasFiniteCarrierStage K) :
    IsSelfDualCone pairing (Set.iUnion K) := by
  apply properCarrier_selfDualCone_extends_to_algebra pairing K hmono hself
  exact dualPositive_implies_finiteStage_membership pairing K hstage

/--
An explicit stage-index witness says exactly that the directed union covers the
whole ambient carrier.
-/
theorem iUnion_eq_univ_of_finiteCarrierStage
    {E : Type*}
    (K : ℕ → Set E)
    (hstage : HasFiniteCarrierStage K) :
    Set.iUnion K = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact Set.mem_iUnion.mpr ⟨hstage.stage x, hstage.mem_stage x⟩

/--
Membership in the algebraic colimit carrier is equivalent to dual positivity
against the same carrier, under the explicit stage-index witness.
-/
theorem properCarrier_stageIndex_mem_iff_dual_positive
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    (hstage : HasFiniteCarrierStage K)
    (x : E) :
    x ∈ Set.iUnion K ↔ ∀ y, y ∈ Set.iUnion K → 0 ≤ pairing x y := by
  exact properCarrier_selfDualCone_extends_of_stageIndex
    pairing K hmono hself hstage x

/--
If the proper carrier stages cover the ambient algebraic carrier, the self-dual
cone extends from the finite stages to the whole ambient carrier.
-/
theorem properCarrier_selfDualCone_extends_to_univ_of_stageIndex
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : ℕ → Set E)
    (hmono : Monotone K)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (K n))
    (hstage : HasFiniteCarrierStage K) :
    IsSelfDualCone pairing (Set.univ : Set E) := by
  have hUnion : Set.iUnion K = (Set.univ : Set E) :=
    iUnion_eq_univ_of_finiteCarrierStage K hstage
  simpa [hUnion] using
    properCarrier_selfDualCone_extends_of_stageIndex pairing K hmono hself hstage

end InfoGeometry.OperatorAlgebra.ProperCarrierStageDetector
