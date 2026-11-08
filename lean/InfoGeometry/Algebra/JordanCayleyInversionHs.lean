import InfoGeometry.Clifford.Arxiv160309063SplitAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Concrete Jordan-Cayley inversion for Hs (split quaternions)

Concrete coordinate analogue of the split-complex trace-reversal determinant
identity for `J₂(ℍ_s)`.

This file proves only finite coordinate identities for the determinant packet and
its trace-reversal witness.  It does not prove a global conformal-group theorem,
a `Spin(3,3)` isomorphism, or an octonionic/`Spin(5,5)` statement.
-/

open InfoGeometry.Clifford.Arxiv160309063

namespace InfoGeometry.Algebra.JordanCayleyInversionHs

/--
A Hermitian 2x2 matrix over Hs:

    X = [[x̂₊, z], [conj(z), x̂₋]]

where `x̂₊ = x³ + x⁶`, `x̂₋ = x³ - x⁶`, and `z = x⁵ + jx¹ + kx⁴ + (kj)x² ∈ ℍ_s`.
-/
structure Herm2x2Hs where
  xp : ℚ    -- x̂₊ = x³ + x⁶
  xm : ℚ    -- x̂₋ = x³ - x⁶
  z : SplitH  -- z = x⁵ + j·x¹ + k·x⁴ + (kj)·x²
  deriving DecidableEq, Repr

namespace Herm2x2Hs

/-- Determinant: det(X) = x̂₊·x̂₋ - |z|².  This is the (3,3) quadratic form. -/
def det (X : Herm2x2Hs) : ℚ :=
  X.xp * X.xm - SplitH.norm X.z

/-- The determinant equals the (3,3) quadratic form (Eq. 6.2). -/
theorem det_eq_quadratic (X : Herm2x2Hs) (x1 x2 x3 x4 x5 x6 : ℚ)
    (hxp : X.xp = x3 + x6) (hxm : X.xm = x3 - x6) (hz : X.z = ⟨x5, x1, x4, x2⟩) :
    X.det = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 := by
  simp [det, SplitH.norm, hxp, hxm, hz]
  ring

/-- Trace reversal for Hs: X̃ = [[x̂₋, -z], [-conj(z), x̂₊]]. -/
def traceReversal (X : Herm2x2Hs) : Herm2x2Hs :=
  ⟨X.xm, X.xp, SplitH.neg X.z⟩

/-- Compute `X · X̃`.  Off-diagonal entries vanish by construction. -/
def mulTraceReversal (X : Herm2x2Hs) : ℚ × ℚ :=
  (X.xp * X.xm - SplitH.norm X.z, -(X.xp * X.xm - SplitH.norm X.z))

/-- Coordinate trace-reversal determinant identity for the diagonal packet. -/
theorem fundamental_identity (X : Herm2x2Hs) :
    X.mulTraceReversal = (X.det, -X.det) := by
  simp [mulTraceReversal, det]

/--
**Corollary:** On the Klein quadric `{det(X) = 0}`, `X · X̃ = 0`.
-/
theorem on_klein_quadric (X : Herm2x2Hs) (h : X.det = 0) :
    X.mulTraceReversal.1 = 0 ∧ X.mulTraceReversal.2 = 0 := by
  have h1 : X.mulTraceReversal.1 = X.det := by
    unfold mulTraceReversal det; rfl
  have h2 : X.mulTraceReversal.2 = -X.det := by
    unfold mulTraceReversal det; rfl
  rw [h1, h2, h]
  simp

/--
**Klein quadric equation (3,3):** `det(X) = 0` in coordinates.
-/
theorem klein_quadric_equation (X : Herm2x2Hs) (x1 x2 x3 x4 x5 x6 : ℚ)
    (hxp : X.xp = x3 + x6) (hxm : X.xm = x3 - x6) (hz : X.z = ⟨x5, x1, x4, x2⟩) :
    (X.det = 0) ↔ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 = 0 := by
  rw [det_eq_quadratic X x1 x2 x3 x4 x5 x6 hxp hxm hz]

end Herm2x2Hs

end InfoGeometry.Algebra.JordanCayleyInversionHs
