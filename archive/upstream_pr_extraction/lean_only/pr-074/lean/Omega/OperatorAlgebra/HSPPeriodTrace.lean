import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- The Birkhoff, invariant-integral, and crossed-product trace identities imply trace invariance
under every morphism in the package. -/
theorem paper_hsp_period_trace
    {Morphism : Type} (birkhoffAverage invariantIntegral crossedProductTrace : ℝ)
    (sourceTrace targetTrace : Morphism → ℝ)
    (birkhoffLimitWitness : birkhoffAverage = invariantIntegral)
    (crossedProductTraceFormula : invariantIntegral = crossedProductTrace)
    (traceCompatibility :
      ∀ f, sourceTrace f = crossedProductTrace ∧
        targetTrace f = crossedProductTrace) :
    birkhoffAverage = invariantIntegral ∧
      invariantIntegral = crossedProductTrace ∧
      (∀ f, sourceTrace f = targetTrace f) := by
  refine ⟨birkhoffLimitWitness, crossedProductTraceFormula, ?_⟩
  intro f
  rcases traceCompatibility f with ⟨hSource, hTarget⟩
  exact hSource.trans hTarget.symm

end Omega.OperatorAlgebra
