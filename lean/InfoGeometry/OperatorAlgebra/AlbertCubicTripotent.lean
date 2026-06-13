import Mathlib.Algebra.Algebra.Basic
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

/--
Algebraic tripotency reduction.

If the stored cubic characteristic law has coefficients `trace1 P = 0`,
`trace2 P = -1`, and `norm P = 0`, then the element satisfies `P³ = P`.
This proves only the polynomial reduction in the supplied associative algebra.
-/
theorem tripotency_is_cubic_rank2_special (P : M) 
    (h_tr1 : sys.trace1 P = 0)
    (h_tr2 : sys.trace2 P = -1)
    (h_nrm : sys.norm P = 0) : 
    P^3 = P := by
  have h_cubic := sys.cubic_characteristic P
  rw [h_tr1, h_tr2, h_nrm] at h_cubic
  have h_sub : P ^ 3 - P = 0 := by
    calc P ^ 3 - P = P ^ 3 - (0 : K) • P ^ 2 + (-1 : K) • P - (0 : K) • 1 := by simp [sub_eq_add_neg]
         _         = 0 := h_cubic
  exact sub_eq_zero.mp h_sub

end InfoGeometry.OperatorAlgebra.Albert
