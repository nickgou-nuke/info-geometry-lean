import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Concrete carrier data for the period-average and crossed-product trace readouts. -/
structure HSPPeriodTraceData where
  Phase : Type
  Morphism : Type
  observable : Phase → ℝ
  birkhoffAverage : ℝ
  invariantIntegral : ℝ
  crossedProductTrace : ℝ
  sourceTrace : Morphism → ℝ
  targetTrace : Morphism → ℝ

/-- The Birkhoff, invariant-integral, and crossed-product trace identities imply trace invariance
under every morphism in the package. -/
theorem paper_hsp_period_trace
    (D : HSPPeriodTraceData)
    (birkhoffLimitWitness : D.birkhoffAverage = D.invariantIntegral)
    (crossedProductTraceFormula : D.invariantIntegral = D.crossedProductTrace)
    (traceCompatibility :
      ∀ f, D.sourceTrace f = D.crossedProductTrace ∧
        D.targetTrace f = D.crossedProductTrace) :
    D.birkhoffAverage = D.invariantIntegral ∧
      D.invariantIntegral = D.crossedProductTrace ∧
      (∀ f, D.sourceTrace f = D.targetTrace f) := by
  refine ⟨birkhoffLimitWitness, crossedProductTraceFormula, ?_⟩
  intro f
  rcases traceCompatibility f with ⟨hSource, hTarget⟩
  exact hSource.trans hTarget.symm

end Omega.OperatorAlgebra
