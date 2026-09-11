import InfoGeometry.Exceptional.SplitOctonionZornReal
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Norm preservation for certified Zorn unit actions

This owner isolates the exact finite algebraic consequence of the existing
Zorn multiplicativity theorem.  It does not identify the action with a
derivation, a JKO step, or a quantum channel.
-/

namespace InfoGeometry.Exceptional.RealZorn

/-- A left multiplier is norm-preserving when its split norm is one. -/
theorem unit_action_preserves_norm
    (U X : ZornMatrixReal) (hU : U.norm = 1) :
    (U * X).norm = X.norm := by
  rw [norm_mul, hU, one_mul]

/-- Two successive certified left actions preserve the norm, without using
associativity of the non-associative Zorn product. -/
theorem unit_action_chain_preserves_norm
    (U V X : ZornMatrixReal)
    (hU : U.norm = 1) (hV : V.norm = 1) :
    (U * (V * X)).norm = X.norm := by
  calc
    (U * (V * X)).norm = (V * X).norm :=
      unit_action_preserves_norm U (V * X) hU
    _ = X.norm := unit_action_preserves_norm V X hV

/-- The identity multiplier is a certified norm-preserving action. -/
theorem one_action_preserves_norm (X : ZornMatrixReal) :
    (ZornMatrixReal.one * X).norm = X.norm := by
  apply unit_action_preserves_norm
  simp [ZornMatrixReal.one, ZornMatrixReal.norm, dot]

end InfoGeometry.Exceptional.RealZorn
