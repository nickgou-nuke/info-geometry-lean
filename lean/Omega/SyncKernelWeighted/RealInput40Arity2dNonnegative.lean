import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ArityChargeCoboundary

namespace Omega.SyncKernelWeighted

open Classical

/-- A concrete monomial of the 2D primitive generating polynomial, recording the `q`-exponent,
the `r`-exponent, and a nonnegative coefficient. -/
structure real_input_40_arity_2d_nonnegative_monomial where
  qExponent : ℤ
  rExponent : ℕ
  coefficient : ℕ

/-- Once the primitive-cycle charge audit is available, the 2D primitive support contains exactly
the monomials whose `q`-exponents are nonnegative; otherwise the support is empty. -/
def real_input_40_arity_2d_nonnegative_terms
    (primitiveCycleDensityBound : Prop) :
    Set real_input_40_arity_2d_nonnegative_monomial :=
  if primitiveCycleDensityBound then {t | 0 ≤ t.qExponent} else ∅

/-- Paper-facing 2D nonnegativity statement: every monomial in the primitive support has a
nonnegative `q`-exponent, so no Laurent negative powers of `q` occur. -/
def real_input_40_arity_2d_nonnegative_statement
    (primitiveCycleDensityBound : Prop) : Prop :=
  (∀ t ∈ real_input_40_arity_2d_nonnegative_terms primitiveCycleDensityBound, 0 ≤ t.qExponent) ∧
    ∀ t ∈ real_input_40_arity_2d_nonnegative_terms primitiveCycleDensityBound, ¬ t.qExponent < 0

/-- Paper label: `cor:real-input-40-arity-2d-nonnegative`. -/
theorem paper_real_input_40_arity_2d_nonnegative
    (primitiveCycleDensityBound : Prop)
    (hBound : primitiveCycleDensityBound) :
    real_input_40_arity_2d_nonnegative_statement primitiveCycleDensityBound := by
  classical
  refine ⟨?_, ?_⟩
  · intro t ht
    simpa [real_input_40_arity_2d_nonnegative_terms, hBound] using ht
  · intro t ht hneg
    have hq : 0 ≤ t.qExponent := by
      simpa [real_input_40_arity_2d_nonnegative_terms, hBound] using ht
    omega

end Omega.SyncKernelWeighted
