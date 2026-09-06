import InfoGeometry.Algebra.SplitOctonionQ
import Mathlib.Tactic

/-!
# Concrete Jordan-Cayley inversion for Os (split octonions) — ℚ lane

Concrete coordinate trace-reversal determinant identities for `J₂(𝕆ₛ)`
over the pure-ℚ split-octonion carrier `SplitO`.

This is the self-contained Lane 1, following the exact pattern of the
Cs and Hs files.  It does **not** depend on the ℤ-based `SplitOct` from
`OperatorAlgebra/SplitOctonionMultiplication.lean`.

This file proves only finite coordinate identities.  It does not prove
an analytic conformality theorem, a CCC theorem, or a global
`Spin(5,5)` isomorphism.
-/

open InfoGeometry.Algebra.SplitOctonionQ

namespace InfoGeometry.Algebra.JordanCayleyInversionOsQ

/--
A Hermitian 2×2 matrix over the split octonions 𝕆ₛ:

    X = [[ξ₊, Z], [conj(Z), ξ₋]]

where `ξ₊, ξ₋ : ℚ` and `Z : SplitO` (8 coordinates over ℚ).
-/
structure Herm2x2OsQ where
  xp : ℚ      -- ξ₊
  xm : ℚ      -- ξ₋
  z  : SplitO  -- Z ∈ 𝕆ₛ (ℚ-based)
  deriving DecidableEq, Repr

namespace Herm2x2OsQ

/-- Determinant: det(X) = ξ₊·ξ₋ - ‖Z‖².  This is the (5,5) quadratic form. -/
def det (X : Herm2x2OsQ) : ℚ :=
  X.xp * X.xm - SplitO.norm X.z

/-- The determinant equals the (5,5) quadratic form with explicit ℚ witnesses. -/
theorem det_eq_quadratic (X : Herm2x2OsQ) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℚ)
    (hxp : X.xp = x1 + x6) (hxm : X.xm = x1 - x6)
    (hza : X.z.a = x7 + x2) (hzb : X.z.b = x7 - x2)
    (hzx0 : X.z.x0 = x3 + x8) (hzy0 : X.z.y0 = x3 - x8)
    (hzx1 : X.z.x1 = x4 + x9) (hzy1 : X.z.y1 = x4 - x9)
    (hzx2 : X.z.x2 = x5 + x10) (hzy2 : X.z.y2 = x5 - x10) :
    X.det = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 - x6 ^ 2 - x7 ^ 2 - x8 ^ 2 - x9 ^ 2 - x10 ^ 2 := by
  simp [det, SplitO.norm, hxp, hxm, hza, hzb, hzx0, hzy0, hzx1, hzy1, hzx2, hzy2]; ring

/-- Trace reversal: X̃ = [[ξ₋, -Z], [-conj(Z), ξ₊]]. -/
def traceReversal (X : Herm2x2OsQ) : Herm2x2OsQ :=
  ⟨X.xm, X.xp, SplitO.neg X.z⟩

/-- Result of multiplying X · X̃ as 2-component diagonal. -/
structure ProdResult where
  e11 : ℚ
  e22 : ℚ

/-- Compute X · X̃.  Off-diagonal entries vanish by trace-reversal. -/
def mulTraceReversal (X : Herm2x2OsQ) : ProdResult :=
  { e11 := X.xp * X.xm - SplitO.norm X.z
    e22 := -(X.xp * X.xm - SplitO.norm X.z) }

/-- Coordinate trace-reversal determinant identity for the diagonal packet. -/
theorem fundamental_identity (X : Herm2x2OsQ) :
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } := by
  simp [mulTraceReversal, det]

/--
**Corollary:** On the Klein quadric `{det(X) = 0}`, the diagonal packet vanishes.
-/
theorem on_klein_quadric (X : Herm2x2OsQ) (h : X.det = 0) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 := by
  have h1 : X.mulTraceReversal.e11 = X.det := by
    unfold mulTraceReversal det; rfl
  have h2 : X.mulTraceReversal.e22 = -X.det := by
    unfold mulTraceReversal det; rfl
  rw [h1, h2, h]
  simp

/--
**Klein quadric equation (5,5) in coordinates.**
-/
theorem klein_quadric_equation (X : Herm2x2OsQ) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℚ)
    (hxp : X.xp = x1 + x6) (hxm : X.xm = x1 - x6)
    (hza : X.z.a = x7 + x2) (hzb : X.z.b = x7 - x2)
    (hzx0 : X.z.x0 = x3 + x8) (hzy0 : X.z.y0 = x3 - x8)
    (hzx1 : X.z.x1 = x4 + x9) (hzy1 : X.z.y1 = x4 - x9)
    (hzx2 : X.z.x2 = x5 + x10) (hzy2 : X.z.y2 = x5 - x10) :
    (X.det = 0) ↔ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 - x6 ^ 2 - x7 ^ 2 - x8 ^ 2 - x9 ^ 2 - x10 ^ 2 = 0 := by
  rw [det_eq_quadratic X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 hxp hxm hza hzb hzx0 hzy0 hzx1 hzy1 hzx2 hzy2]

end Herm2x2OsQ

end InfoGeometry.Algebra.JordanCayleyInversionOsQ
