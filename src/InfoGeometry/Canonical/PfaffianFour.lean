import Mathlib.Tactic

/-!
# The four-dimensional Pfaffian identity

This owner closes the first genuinely higher-dimensional Pfaffian case left open
by `Canonical.Pfaffian`.  The carrier is the canonical 4×4 skew matrix with
upper-triangular entries `a,b,c,d,e,f`; the Pfaffian is the usual alternating
quadratic `a f - b e + c d`.  The determinant identity is proved over every
commutative ring, by Mathlib's determinant expansion and ring normalization.
This is an algebraic finite identity; it does not assert a general Pfaffian
implementation for arbitrary even dimensions.
-/

namespace InfoGeometry.Canonical.Pfaffian

/-- The standard 4×4 skew-symmetric matrix with upper-triangular entries. -/
def skew4 {R : Type*} [CommRing R] (a b c d e f : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![0, a, b, c; -a, 0, d, e; -b, -d, 0, f; -c, -e, -f, 0]

/-- The Pfaffian polynomial of a 4×4 skew-symmetric matrix. -/
def pfaffian4 {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  a * f - b * e + c * d

private lemma det_fin_three_explicit {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) :
    M.det = M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1)
      - M 1 0 * (M 0 1 * M 2 2 - M 0 2 * M 2 1)
      + M 2 0 * (M 0 1 * M 1 2 - M 0 2 * M 1 1) := by
  rw [Matrix.det_succ_column_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_two]
  ring

/-- The 4×4 Pfaffian squared is the determinant of the skew matrix. -/
theorem pfaffian4_sq_eq_det {R : Type*} [CommRing R]
    (a b c d e f : R) :
    (pfaffian4 a b c d e f) ^ 2 = (skew4 a b c d e f).det := by
  classical
  rw [Matrix.det_succ_column_zero]
  simp only [Fin.sum_univ_succ, Fin.succAbove_zero]
  have h1 := det_fin_three_explicit
    (skew4 a b c d e f |>.submatrix (Fin.succAbove 1) Fin.succ)
  have h2 := det_fin_three_explicit
    (skew4 a b c d e f |>.submatrix (Fin.succAbove 2) Fin.succ)
  have h3 := det_fin_three_explicit
    (skew4 a b c d e f |>.submatrix (Fin.succAbove 3) Fin.succ)
  simp [skew4, pfaffian4, Fin.succAbove, Fin.succ,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2 h3 ⊢
  rw [h1, h2, h3]
  ring

@[simp] theorem pfaffian4_zero :
    pfaffian4 (0 : ℝ) 0 0 0 0 0 = 0 := by
  simp [pfaffian4]

end InfoGeometry.Canonical.Pfaffian
