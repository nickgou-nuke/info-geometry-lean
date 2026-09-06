import Mathlib.Tactic

/-!
# ℚ-based split-octonion carrier (Zorn coordinates)

Lightweight 8-coordinate carrier over ℚ for the Lane 1 Jordan-Cayley
inversion of `J₂(𝕆ₛ)`.  Provides only `norm` (the Zorn split-determinant),
`neg`, and `conj`; full nonassociative multiplication is intentionally
excluded so that the Lane 1 file follows the same minimal pattern as the
Cs and Hs files.

The norm `a·b - (x₀·y₀ + x₁·y₁ + x₂·y₂)` is the split (4,4) quadratic
form.  Combined with the Hermitian 2×2 determinant `ξ₊·ξ₋ - ‖Z‖²`, this
yields a coordinate model for a (5,5) quadratic form.

This file does **not** prove an analytic conformality theorem, a CCC
theorem, a global `Spin(5,5)` isomorphism, or an octonionic matrix
inverse theorem.
-/

namespace InfoGeometry.Algebra.SplitOctonionQ

/-- Eight-coordinate Zorn split-octonion cell over ℚ. -/
structure SplitO where
  a  : ℚ
  b  : ℚ
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  y0 : ℚ
  y1 : ℚ
  y2 : ℚ
  deriving DecidableEq, Repr

namespace SplitO

/-- Coordinatewise negation. -/
def neg (z : SplitO) : SplitO :=
  ⟨-z.a, -z.b, -z.x0, -z.x1, -z.x2, -z.y0, -z.y1, -z.y2⟩

/--
Correct split-octonion conjugation `conj(a, x; y, b) = (b, -x; -y, a)`.

This satisfies the alternative property `Z·conj(Z) = ‖Z‖²·1`.
-/
def conj (z : SplitO) : SplitO :=
  ⟨z.b, z.a, -z.x0, -z.x1, -z.x2, -z.y0, -z.y1, -z.y2⟩

/-- Zorn split-norm: the (4,4) quadratic form. -/
def norm (z : SplitO) : ℚ :=
  z.a * z.b - (z.x0 * z.y0 + z.x1 * z.y1 + z.x2 * z.y2)

/-- Conjugation is an involution. -/
theorem conj_conj (z : SplitO) : conj (conj z) = z := by
  cases z; simp [conj]

/-- The norm is invariant under conjugation. -/
theorem norm_conj (z : SplitO) : norm (conj z) = norm z := by
  cases z; simp [conj, norm]; ring

/-- The norm equals the (4,4) quadratic form in diagonal coordinates. -/
theorem norm_eq_quadratic (z : SplitO) (p q u0 u1 u2 v0 v1 v2 : ℚ)
    (ha : z.a = q + v0) (hb : z.b = q - v0)
    (hx0 : z.x0 = u0 + v1) (hy0 : z.y0 = u0 - v1)
    (hx1 : z.x1 = u1 + v2) (hy1 : z.y1 = u1 - v2)
    (hx2 : z.x2 = u2 + p) (hy2 : z.y2 = u2 - p) :
    z.norm = q ^ 2 + p ^ 2 + v1 ^ 2 + v2 ^ 2 - v0 ^ 2 - u0 ^ 2 - u1 ^ 2 - u2 ^ 2 := by
  simp [norm, ha, hb, hx0, hy0, hx1, hy1, hx2, hy2]; ring_nf

end SplitO

end InfoGeometry.Algebra.SplitOctonionQ
