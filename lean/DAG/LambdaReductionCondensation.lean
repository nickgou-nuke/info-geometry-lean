import DAG.LambdaReductionPreorder

/-!
# Strongly connected beta-reduction classes

Mutual beta reachability is an equivalence relation. Its quotient carries the
induced reachability partial order: recurrent computation remains inside one
class, while the quotient records the acyclic condensation order.
-/

namespace InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

namespace LambdaTerm

/-- Two terms lie in the same reduction component when each reaches the other. -/
def MutualBeta (t u : LambdaTerm) : Prop :=
  t ≤ u ∧ u ≤ t

theorem mutualBeta_refl (t : LambdaTerm) : MutualBeta t t :=
  ⟨le_rfl, le_rfl⟩

theorem mutualBeta_symm {t u : LambdaTerm} (h : MutualBeta t u) :
    MutualBeta u t :=
  ⟨h.2, h.1⟩

theorem mutualBeta_trans {t u v : LambdaTerm}
    (htu : MutualBeta t u) (huv : MutualBeta u v) :
    MutualBeta t v :=
  ⟨le_trans htu.1 huv.1, le_trans huv.2 htu.2⟩

/-- Setoid of strongly connected components of the beta-reduction graph. -/
def betaSCCSetoid : Setoid LambdaTerm where
  r := MutualBeta
  iseqv := ⟨mutualBeta_refl, mutualBeta_symm, mutualBeta_trans⟩

/-- Condensation of lambda terms by mutual beta reachability. -/
def BetaSCC : Type :=
  Quotient betaSCCSetoid

/-- Canonical projection to the beta-reduction condensation. -/
def betaSCCClass (t : LambdaTerm) : BetaSCC :=
  Quotient.mk betaSCCSetoid t

/-- Reachability descends to strongly connected components. -/
def betaSCCLe : BetaSCC → BetaSCC → Prop :=
  fun q r =>
    Quotient.liftOn₂ q r (fun t u => t ≤ u) (by
      intro t u t' u' htt' huu'
      apply propext
      constructor
      · intro htu
        exact le_trans htt'.2 (le_trans htu huu'.1)
      · intro ht'u'
        exact le_trans htt'.1 (le_trans ht'u' huu'.2))

/-- The condensation order is a partial order. -/
instance betaSCCPartialOrder : PartialOrder BetaSCC where
  le := betaSCCLe
  lt := fun q r => betaSCCLe q r ∧ ¬ betaSCCLe r q
  le_refl := by
    intro q
    refine Quotient.inductionOn q ?_
    intro t
    exact le_rfl
  le_trans := by
    intro q r s
    refine Quotient.inductionOn q ?_
    intro t
    refine Quotient.inductionOn r ?_
    intro u
    refine Quotient.inductionOn s ?_
    intro v htu huv
    exact le_trans htu huv
  le_antisymm := by
    intro q r
    refine Quotient.inductionOn q ?_
    intro t
    refine Quotient.inductionOn r ?_
    intro u htu hut
    exact Quotient.sound ⟨htu, hut⟩
  lt_iff_le_not_ge := by
    intro q r
    rfl

@[simp] theorem betaSCCClass_le_betaSCCClass (t u : LambdaTerm) :
    betaSCCClass t ≤ betaSCCClass u ↔ t ≤ u :=
  Iff.rfl

/-- Mutual reachability collapses to equality in the condensation. -/
theorem betaSCCClass_eq_of_mutualBeta {t u : LambdaTerm}
    (h : MutualBeta t u) :
    betaSCCClass t = betaSCCClass u :=
  Quotient.sound h

/-- A one-step reduction induces an ordered edge between condensation classes. -/
theorem betaSCCClass_le_of_betaStep {t u : LambdaTerm}
    (h : BetaStep t u) :
    betaSCCClass t ≤ betaSCCClass u :=
  betaStep_le h

end LambdaTerm

end InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

