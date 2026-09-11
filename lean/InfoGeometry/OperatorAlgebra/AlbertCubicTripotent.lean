import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace InfoGeometry.OperatorAlgebra.Albert

/--
A witness-gated cubic characteristic interface over an associative `K`-algebra.

This is an algebraic shadow of a Freudenthal/Albert characteristic polynomial,
not a construction of the Albert algebra, OP², or an exceptional Lie group.
Concrete exceptional carriers must supply this characteristic law explicitly.
-/
structure CubicNorm (M K : Type*) [CommRing K] [Ring M] [Algebra K M] where
  trace1 : M → K
  trace2 : M → K
  norm   : M → K

  -- The stored cubic characteristic property.
  cubic_characteristic : ∀ (x : M),
    x^3 - (trace1 x) • x^2 + (trace2 x) • x - (norm x) • 1 = 0

variable {M K : Type*} [CommRing K] [Ring M] [Algebra K M] (sys : CubicNorm M K)

/-- The cubic characteristic residual stored by `CubicNorm`. -/
def cubicResidual (x : M) : M :=
  x ^ 3 - (sys.trace1 x) • x ^ 2 + (sys.trace2 x) • x - (sys.norm x) • 1

/-- The stored characteristic law says the cubic residual vanishes. -/
theorem cubicResidual_eq_zero (x : M) :
    cubicResidual sys x = 0 :=
  sys.cubic_characteristic x

/--
Exact coefficient specialization of the cubic residual.

Under `trace1 P = 0`, `trace2 P = -1`, and `norm P = 0`, the residual is
literally the tripotent residual `P³ - P` in the supplied associative algebra.
This is the Lean counterpart of the SymPy/Sage/GAP abstract polynomial check.
-/
theorem cubicResidual_specializes_to_tripotent_residual (P : M)
    (h_tr1 : sys.trace1 P = 0)
    (h_tr2 : sys.trace2 P = -1)
    (h_nrm : sys.norm P = 0) :
    cubicResidual sys P = P ^ 3 - P := by
  simp [cubicResidual, h_tr1, h_tr2, h_nrm, sub_eq_add_neg]

/--
Algebraic tripotency reduction.

If the stored cubic characteristic law has coefficients `trace1 P = 0`,
`trace2 P = -1`, and `norm P = 0`, then the element satisfies `P³ = P`.
-/
theorem tripotency_is_cubic_rank2_special (P : M)
    (h_tr1 : sys.trace1 P = 0)
    (h_tr2 : sys.trace2 P = -1)
    (h_nrm : sys.norm P = 0) :
    P^3 = P := by
  have h_res : P ^ 3 - P = 0 := by
    rw [← cubicResidual_specializes_to_tripotent_residual sys P h_tr1 h_tr2 h_nrm]
    exact cubicResidual_eq_zero sys P
  exact sub_eq_zero.mp h_res

end InfoGeometry.OperatorAlgebra.Albert
