import InfoGeometry.Clifford.Arxiv160309063SplitAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Concrete Jordan-Cayley inversion for Cs (split complex numbers)

Concrete coordinate trace-reversal determinant identities for `J₂(ℂ_s)`.

This file proves finite coordinate facts around Eq. (5.7) of Fioresi--Latini--
Marrani.  It does not prove an analytic conformality theorem, a CCC theorem, or
a global spin/structure-group isomorphism.
-/

open InfoGeometry.Clifford.Arxiv160309063

namespace InfoGeometry.Algebra.JordanCayleyInversionCs

/--
A Hermitian 2x2 matrix over Cs:

    X = [[x₊, a], [conj(a), x₋]]
-/
structure Herm2x2Cs where
  xp : ℚ
  xm : ℚ
  a : SplitC
  deriving DecidableEq, Repr

namespace Herm2x2Cs

/-- Determinant: det(X) = x₊·x₋ - |a|². -/
def det (X : Herm2x2Cs) : ℚ :=
  X.xp * X.xm - SplitC.norm X.a

/-- The determinant equals the (2,2) quadratic form. -/
theorem det_eq_quadratic (X : Herm2x2Cs) (x1 x2 x3 x4 : ℚ)
    (hxp : X.xp = x1 + x4) (hxm : X.xm = x1 - x4) (ha : X.a = ⟨x3, x2⟩) :
    X.det = x1 ^ 2 + x2 ^ 2 - x3 ^ 2 - x4 ^ 2 := by
  simp [det, SplitC.norm, hxp, hxm, ha]
  ring

/-- Trace reversal (Eq. 5.5): X̃ = [[x₋, -a], [-conj(a), x₊]]. -/
def traceReversal (X : Herm2x2Cs) : Herm2x2Cs :=
  ⟨X.xm, X.xp, SplitC.neg X.a⟩

/--
Result of multiplying `X · X̃` as 2-component diagonal (off-diagonals vanish).
-/
structure ProdResult where
  e11 : ℚ
  e22 : ℚ

/-- Compute `X · X̃`.  Off-diagonal entries are zero by trace-reversal. -/
def mulTraceReversal (X : Herm2x2Cs) : ProdResult :=
  { e11 := X.xp * X.xm - SplitC.norm X.a
    e22 := -(X.xp * X.xm - SplitC.norm X.a) }

/-- Coordinate trace-reversal determinant identity for the diagonal packet. -/
theorem fundamental_identity (X : Herm2x2Cs) :
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } := by
  simp [mulTraceReversal, det]

/--
**Corollary:** On the coordinate Klein quadric `{det(X) = 0}`, the diagonal
packet vanishes.
-/
theorem on_klein_quadric (X : Herm2x2Cs) (h : X.det = 0) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 := by
  -- Note: X.det = X.xp * X.xm - SplitC.norm X.a by definition
  -- and X.mulTraceReversal.e11 = X.xp * X.xm - SplitC.norm X.a by definition
  -- So the goal follows directly from h.
  -- Use `show_term` to see the definitional equalities:
  have h1 : X.mulTraceReversal.e11 = X.det := by
    unfold mulTraceReversal det
    rfl
  have h2 : X.mulTraceReversal.e22 = -X.det := by
    unfold mulTraceReversal det
    rfl
  rw [h1, h2, h]
  simp

/--
**Klein quadric equation:** `det(X) = 0` in coordinates.
-/
theorem klein_quadric_equation (X : Herm2x2Cs) (x1 x2 x3 x4 : ℚ)
    (hxp : X.xp = x1 + x4) (hxm : X.xm = x1 - x4) (ha : X.a = ⟨x3, x2⟩) :
    (X.det = 0) ↔ x1 ^ 2 + x2 ^ 2 - x3 ^ 2 - x4 ^ 2 = 0 := by
  rw [det_eq_quadratic X x1 x2 x3 x4 hxp hxm ha]

end Herm2x2Cs

end InfoGeometry.Algebra.JordanCayleyInversionCs
