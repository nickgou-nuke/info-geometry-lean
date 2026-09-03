import DAG.LambdaReduction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Thermodynamic one-cochains on beta-reduction traces

A positive forward/reverse rate field assigns a logarithmic affinity to every
proof-relevant beta step. The generic repository-owned ReductionTrace provides
finite paths; affinity is additive along the stored trace and its exponential
is the positive multiplicative holonomy.
-/

namespace InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

namespace LambdaTerm

/-- Strictly positive forward and reverse rates on every beta-reduction edge. -/
structure BetaRateField where
  forward : ∀ {t u : LambdaTerm}, BetaStep t u → ℝ
  reverse : ∀ {t u : LambdaTerm}, BetaStep t u → ℝ
  forward_pos : ∀ {t u : LambdaTerm} (h : BetaStep t u), 0 < forward h
  reverse_pos : ∀ {t u : LambdaTerm} (h : BetaStep t u), 0 < reverse h

namespace BetaRateField

/-- Logarithmic affinity of one beta-reduction edge. -/
noncomputable def affinity (R : BetaRateField)
    {t u : LambdaTerm} (h : BetaStep t u) : ℝ :=
  Real.log (R.forward h / R.reverse h)

/-- Integrated affinity along a proof-relevant reduction trace. -/
noncomputable def traceAffinity (R : BetaRateField) :
    {t u : LambdaTerm} → {xs : List LambdaTerm} →
      DAG.ReductionTrace BetaStep t xs u → ℝ
  | _, _, _, .refl _ => 0
  | _, _, _, .cons h rest => R.affinity h + R.traceAffinity rest

/-- Multiplicative holonomy of a finite beta-reduction trace. -/
noncomputable def traceHolonomy (R : BetaRateField)
    {t u : LambdaTerm} {xs : List LambdaTerm}
    (trace : DAG.ReductionTrace BetaStep t xs u) : ℝ :=
  Real.exp (R.traceAffinity trace)

theorem traceHolonomy_pos (R : BetaRateField)
    {t u : LambdaTerm} {xs : List LambdaTerm}
    (trace : DAG.ReductionTrace BetaStep t xs u) :
    0 < R.traceHolonomy trace :=
  Real.exp_pos _

/-- Detailed balance on a closed trace means zero integrated affinity. -/
def DetailedBalance (R : BetaRateField)
    {t : LambdaTerm} {xs : List LambdaTerm}
    (loop : DAG.ReductionTrace BetaStep t xs t) : Prop :=
  R.traceAffinity loop = 0

/-- A closed trace has detailed balance exactly when its holonomy is the unit. -/
theorem detailedBalance_iff_traceHolonomy_eq_one (R : BetaRateField)
    {t : LambdaTerm} {xs : List LambdaTerm}
    (loop : DAG.ReductionTrace BetaStep t xs t) :
    R.DetailedBalance loop ↔ R.traceHolonomy loop = 1 := by
  unfold DetailedBalance traceHolonomy
  constructor
  · intro h
    rw [h, Real.exp_zero]
  · intro h
    apply Real.exp_injective
    simpa using h

end BetaRateField

end LambdaTerm

end InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
