import InfoGeometry.Clifford.Arxiv160309063SplitAlgebra
import Mathlib.Tactic

/-!
# Theorem-safe Jordan--Cayley inversion identities

Finite coordinate identities for planar inversion and the split-complex
`J₂(C_s)` determinant/trace-reversal packet from Fioresi--Latini--Marrani,
arXiv:1603.09063v2.

No analytic conformality theorem, CCC theorem, global Spin theorem, or
octonionic inverse theorem is claimed here.
-/

namespace JordanCayleyInversion

/-- Numerator of the image of the line `A x + B y + C = 0` under planar inversion
`x = u/(u²+v²)`, `y = -v/(u²+v²)`. -/
def invertedLineCircleNumerator (A B C u v : ℚ) : ℚ :=
  C * (u ^ 2 + v ^ 2) + A * u - B * v

/-- Finite algebraic form of the line-to-circle transform under `w = 1/z`, away
from the inversion pole `u²+v²=0`. -/
theorem planar_inversion_line_to_circle_numerator
    (A B C u v : ℚ) (h : u ^ 2 + v ^ 2 ≠ 0) :
    (u ^ 2 + v ^ 2) * (A * (u / (u ^ 2 + v ^ 2)) +
      B * ((-v) / (u ^ 2 + v ^ 2)) + C) =
    invertedLineCircleNumerator A B C u v := by
  field_simp [h]
  unfold invertedLineCircleNumerator
  ring_nf

namespace CsJordan

abbrev Herm2 := InfoGeometry.Clifford.Arxiv160309063.SplitC.Herm2x2Cs

/-- Scalar multiplication of the coordinate packet for `J₂(C_s)`. -/
def scale (r : ℚ) (X : Herm2) : Herm2 where
  xp := r * X.xp
  xm := r * X.xm
  a := InfoGeometry.Clifford.Arxiv160309063.SplitC.mul
    (InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar r) X.a

/-- The Jordan determinant, re-exported locally. -/
def det (X : Herm2) : ℚ :=
  InfoGeometry.Clifford.Arxiv160309063.SplitC.hermitianDet X

/-- Trace reversal, re-exported locally. -/
def trRev (X : Herm2) : Herm2 :=
  InfoGeometry.Clifford.Arxiv160309063.SplitC.traceReversal X

/-- Coordinate extensionality for Hermitian `2×2` split-complex packets. -/
theorem ext {X Y : Herm2} (hxp : X.xp = Y.xp) (hxm : X.xm = Y.xm) (ha : X.a = Y.a) :
    X = Y := by
  cases X
  cases Y
  simp_all

/-- Trace reversal is an involution on the coordinate packet. -/
theorem trRev_involutive (X : Herm2) : trRev (trRev X) = X := by
  cases X with
  | mk xp xm a =>
    apply ext <;> simp [trRev,
      InfoGeometry.Clifford.Arxiv160309063.SplitC.traceReversal,
      InfoGeometry.Clifford.Arxiv160309063.SplitC.neg]

/-- The determinant is invariant under trace reversal. -/
theorem det_trRev (X : Herm2) : det (trRev X) = det X := by
  cases X with
  | mk xp xm a =>
    cases a with
    | mk ar ai =>
      simp [det, trRev,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.hermitianDet,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.traceReversal,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.norm,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.neg]
      ring

/-- Scaling a `J₂(C_s)` coordinate packet scales the determinant quadratically. -/
theorem det_scale (r : ℚ) (X : Herm2) : det (scale r X) = r ^ 2 * det X := by
  cases X with
  | mk xp xm a =>
    cases a with
    | mk ar ai =>
      simp [det, scale,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.hermitianDet,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.norm]
      ring

/-- Coordinate Jordan--Cayley inversion `W(X)=trRev(X)/det(X)`, totalized by
Lean's field division at determinant zero. Use nonzero determinant lemmas for the
genuine inverse region. -/
def cayleyInversion (X : Herm2) : Herm2 :=
  scale (1 / det X) (trRev X)

/-- Applying determinant to the coordinate Cayley inversion gives `1/det(X)` on
the non-null locus. -/
theorem det_cayleyInversion (X : Herm2) (hX : det X ≠ 0) :
    det (cayleyInversion X) = 1 / det X := by
  rw [cayleyInversion, det_scale, det_trRev]
  field_simp [hX]

/-- Trace reversal commutes with scalar multiplication. -/
theorem trRev_scale (r : ℚ) (X : Herm2) : trRev (scale r X) = scale r (trRev X) := by
  cases X with
  | mk xp xm a =>
    cases a with
    | mk ar ai =>
      apply ext <;> simp [trRev, scale,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.traceReversal,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.neg]

/-- Coordinate involutivity of Cayley inversion on the non-null locus. -/
theorem cayleyInversion_involutive (X : Herm2) (hX : det X ≠ 0) :
    cayleyInversion (cayleyInversion X) = X := by
  have hdet : det (cayleyInversion X) = 1 / det X := det_cayleyInversion X hX
  unfold cayleyInversion
  change scale (1 / det (cayleyInversion X)) (trRev (scale (1 / det X) (trRev X))) = X
  rw [hdet, trRev_scale, trRev_involutive]
  cases X with
  | mk xp xm a =>
    cases a with
    | mk ar ai =>
      apply ext
      · simp [scale,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.mul]
        field_simp [hX]
      · simp [scale,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.mul]
        field_simp [hX]
      · apply InfoGeometry.Clifford.Arxiv160309063.SplitC.ext
        · simp [scale,
            InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
            InfoGeometry.Clifford.Arxiv160309063.SplitC.mul]
          field_simp [hX]
        · simp [scale,
            InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
            InfoGeometry.Clifford.Arxiv160309063.SplitC.mul]
          field_simp [hX]

end CsJordan

end JordanCayleyInversion
