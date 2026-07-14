import Mathlib
import Mathlib.Tactic.FinCases

namespace SL2CZhukovsky

open Matrix
open Complex

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

def det2x2 (M : Mat2C) : ℂ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

/-- The characteristic polynomial of a `2 × 2` complex matrix, evaluated at `x`. -/
def charPoly2x2 (M : Mat2C) (x : ℂ) : ℂ :=
  det2x2 (x • (1 : Mat2C) - M)

/-- Explicit characteristic-polynomial formula for a `2 × 2` complex matrix. -/
theorem charPoly2x2_eq (M : Mat2C) (x : ℂ) :
    charPoly2x2 M x = x ^ 2 - Matrix.trace M * x + det2x2 M := by
  unfold charPoly2x2 det2x2
  have hMatrix :
      x • (1 : Mat2C) - M = !![x - M 0 0, -M 0 1; -M 1 0, x - M 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [hMatrix]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

/-- Determinant-one specialization of the `2 × 2` characteristic polynomial. -/
theorem char_poly_eq_zhukovsky (M : Mat2C) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : det2x2 M = 1) :
    charPoly2x2 M x = x ^ 2 - Tr * x + 1 := by
  rw [charPoly2x2_eq, h_tr, h_det]

/-- Nonzero roots of the determinant-one characteristic polynomial satisfy the Zhukovsky relation. -/
theorem eigenvalue_zhukovsky_relation (M : Mat2C) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : det2x2 M = 1)
    (h_eigen : charPoly2x2 M x = 0) (hx : x ≠ 0) :
    x + x⁻¹ = Tr := by
  have hchar := char_poly_eq_zhukovsky M x Tr h_tr h_det
  rw [h_eigen] at hchar
  have hquad : x ^ 2 - Tr * x + 1 = 0 := hchar.symm
  have hmul : x * (x + x⁻¹ - Tr) = 0 := by
    field_simp [hx]
    ring_nf at hquad ⊢
    exact hquad
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hx)

/-- For nonzero `x`, the determinant-one root condition is equivalent to the Zhukovsky relation. -/
theorem charPoly2x2_root_iff_zhukovsky_relation (M : Mat2C) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : det2x2 M = 1) (hx : x ≠ 0) :
    charPoly2x2 M x = 0 ↔ x + x⁻¹ = Tr := by
  constructor
  · intro h_eigen
    exact eigenvalue_zhukovsky_relation M x Tr h_tr h_det h_eigen hx
  · intro hrel
    rw [char_poly_eq_zhukovsky M x Tr h_tr h_det]
    have hmul : x * (x + x⁻¹ - Tr) = 0 := by
      rw [hrel]
      ring
    field_simp [hx] at hmul
    ring_nf at hmul ⊢
    exact hmul

/-- Nonzero determinant-one roots are closed under spectral inversion. -/
theorem inverse_root_of_root (M : Mat2C) (x Tr : ℂ)
    (h_tr : Matrix.trace M = Tr) (h_det : det2x2 M = 1)
    (h_eigen : charPoly2x2 M x = 0) (hx : x ≠ 0) :
    charPoly2x2 M x⁻¹ = 0 := by
  have hrel : x + x⁻¹ = Tr :=
    eigenvalue_zhukovsky_relation M x Tr h_tr h_det h_eigen hx
  exact (charPoly2x2_root_iff_zhukovsky_relation M x⁻¹ Tr h_tr h_det (inv_ne_zero hx)).mpr
    (by simpa [inv_inv, add_comm] using hrel)

/--
Trace-free determinant-one specialization: any root of the characteristic polynomial
satisfies `x^2 = -1`.
-/
theorem trace_free_eigenvalue_square_eq_neg_one (M : Mat2C) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : det2x2 M = 1) (h_eigen : charPoly2x2 M x = 0) :
    x ^ 2 = -1 := by
  have h_char : charPoly2x2 M x = x ^ 2 + 1 := by
    calc
      charPoly2x2 M x = x ^ 2 - Matrix.trace M * x + det2x2 M := charPoly2x2_eq M x
      _ = x ^ 2 + 1 := by rw [h_tr, h_det]; ring
  rw [h_eigen] at h_char
  exact eq_neg_of_add_eq_zero_left h_char.symm

/-- A complex number whose square is `-1` lies on the squared-norm unit circle. -/
theorem normSq_eq_one_of_sq_eq_neg_one (x : ℂ) (h : x ^ 2 = -1) :
    Complex.normSq x = 1 := by
  have hnorm : Complex.normSq (x ^ 2) = Complex.normSq (-1 : ℂ) := by
    rw [h]
  have hs : Complex.normSq x * Complex.normSq x = 1 := by
    simpa [pow_two] using hnorm
  have hn : 0 ≤ Complex.normSq x := Complex.normSq_nonneg x
  nlinarith

/-- Backward-compatible alias matching the earlier external name. -/
theorem trace_free_eigenvalue_compact_C (M : Mat2C) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : det2x2 M = 1) (h_eigen : charPoly2x2 M x = 0) :
    x ^ 2 = -1 :=
  trace_free_eigenvalue_square_eq_neg_one M x h_tr h_det h_eigen

/-- The only complex roots of `x^2 = -1` are `I` and `-I`. -/
theorem sq_eq_neg_one_iff_eq_I_or_neg_I (x : ℂ) :
    x ^ 2 = -1 ↔ x = Complex.I ∨ x = -Complex.I := by
  constructor
  · intro h
    have hf : (x - Complex.I) * (x + Complex.I) = 0 := by
      calc
        (x - Complex.I) * (x + Complex.I) = x ^ 2 - Complex.I ^ 2 := by ring
        _ = x ^ 2 + 1 := by simp [Complex.I_mul_I, pow_two]
        _ = 0 := by rw [h]; norm_num
    rcases mul_eq_zero.mp hf with hx | hx
    · left
      exact sub_eq_zero.mp hx
    · right
      exact eq_neg_of_add_eq_zero_left hx
  · intro h
    rcases h with rfl | rfl <;> norm_num

/-- Trace-free determinant-one roots lie on the squared-norm unit circle. -/
theorem trace_free_eigenvalue_normSq_eq_one (M : Mat2C) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : det2x2 M = 1) (h_eigen : charPoly2x2 M x = 0) :
    Complex.normSq x = 1 :=
  normSq_eq_one_of_sq_eq_neg_one x
    (trace_free_eigenvalue_square_eq_neg_one M x h_tr h_det h_eigen)

/-- Trace-free determinant-one roots are exactly the two complex points `±I`. -/
theorem trace_free_eigenvalue_eq_I_or_neg_I (M : Mat2C) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : det2x2 M = 1) (h_eigen : charPoly2x2 M x = 0) :
    x = Complex.I ∨ x = -Complex.I :=
  (sq_eq_neg_one_iff_eq_I_or_neg_I x).mp
    (trace_free_eigenvalue_square_eq_neg_one M x h_tr h_det h_eigen)

/-- Trace-free determinant-one roots have inverse equal to their negative. -/
theorem trace_free_eigenvalue_inv_eq_neg (M : Mat2C) (x : ℂ)
    (h_tr : Matrix.trace M = 0) (h_det : det2x2 M = 1) (h_eigen : charPoly2x2 M x = 0) :
    x⁻¹ = -x := by
  have hsq : x ^ 2 = -1 := trace_free_eigenvalue_square_eq_neg_one M x h_tr h_det h_eigen
  apply inv_eq_of_mul_eq_one_right
  calc
    x * (-x) = -(x ^ 2) := by ring
    _ = 1 := by rw [hsq]; norm_num

end SL2CZhukovsky
