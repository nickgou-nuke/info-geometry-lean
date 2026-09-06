import DAG.LambdaReductionCondensation
import InfoGeometry.Causal.Alexandrov

/-!
# Alexandrov topology of beta reduction

The generic Alexandrov topology already owned by InfoGeometry.Causal is
instantiated on the beta-reduction preorder. Open sets are precisely sets
closed under computational futures.
-/

open Set

namespace InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

namespace LambdaTerm

/-- The upper-set Alexandrov topology of beta reachability. -/
def betaAlexandrovTopology : TopologicalSpace LambdaTerm :=
  InfoGeometry.Causal.AlexandrovTopology

/-- A beta-open set is open in the reachability Alexandrov topology. -/
def IsBetaOpen (U : Set LambdaTerm) : Prop :=
  @IsOpen LambdaTerm betaAlexandrovTopology U

/-- Beta-open sets are exactly the sets closed under forward beta reduction. -/
theorem isBetaOpen_iff (U : Set LambdaTerm) :
    IsBetaOpen U ↔
      ∀ ⦃t u : LambdaTerm⦄, t ∈ U → BetaStar t u → u ∈ U :=
  Iff.rfl

/-- The complete computational future of a term. -/
def betaFuture (t : LambdaTerm) : Set LambdaTerm :=
  {u | BetaStar t u}

/-- Every computational future is an Alexandrov-open set. -/
theorem betaFuture_isOpen (t : LambdaTerm) :
    IsBetaOpen (betaFuture t) := by
  rw [isBetaOpen_iff]
  intro u v htu huv
  exact betaStar_trans htu huv

/-- Open-neighbourhood specialization in the chosen future-open convention. -/
def FutureSpecializes (t u : LambdaTerm) : Prop :=
  ∀ U : Set LambdaTerm, IsBetaOpen U → t ∈ U → u ∈ U

/-- The open-neighbourhood specialization relation is exactly beta reachability. -/
theorem futureSpecializes_iff_betaStar (t u : LambdaTerm) :
    FutureSpecializes t u ↔ BetaStar t u := by
  constructor
  · intro h
    exact h (betaFuture t) (betaFuture_isOpen t) (betaStar_refl t)
  · intro htu U hU ht
    exact (isBetaOpen_iff U).mp hU ht htu

/-- Mutual specialization is exactly membership in one reduction component. -/
theorem mutual_futureSpecializes_iff_mutualBeta (t u : LambdaTerm) :
    (FutureSpecializes t u ∧ FutureSpecializes u t) ↔ MutualBeta t u := by
  simp only [futureSpecializes_iff_betaStar, MutualBeta, le_iff_betaStar]

end LambdaTerm

end InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

