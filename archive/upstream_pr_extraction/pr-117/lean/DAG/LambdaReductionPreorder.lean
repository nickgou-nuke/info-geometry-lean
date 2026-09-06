import DAG.LambdaReduction

/-!
# The beta-reduction reachability preorder

This module equips the repository-owned de Bruijn lambda terms with the preorder
whose comparison relation is reflexive-transitive beta reduction. It adds no
new term syntax and no new reduction relation.
-/

namespace InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

namespace LambdaTerm

/-- Beta reachability is the preorder relation on de Bruijn lambda terms. -/
instance betaReductionPreorder : Preorder LambdaTerm where
  le := BetaStar
  lt := fun t u => BetaStar t u ∧ ¬ BetaStar u t
  le_refl := betaStar_refl
  le_trans := fun _ _ _ => betaStar_trans
  lt_iff_le_not_ge := by
    intro t u
    rfl

/-- The order relation is definitionally reflexive-transitive beta reduction. -/
@[simp] theorem le_iff_betaStar (t u : LambdaTerm) :
    t ≤ u ↔ BetaStar t u :=
  Iff.rfl

/-- Every one-step beta reduction is an edge of the reachability preorder. -/
theorem betaStep_le {t u : LambdaTerm} (h : BetaStep t u) : t ≤ u :=
  betaStep_to_betaStar h

end LambdaTerm

end InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
