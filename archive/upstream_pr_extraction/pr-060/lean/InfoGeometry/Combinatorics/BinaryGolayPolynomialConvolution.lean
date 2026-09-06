import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace InfoGeometry.Combinatorics.BinaryGolayPolynomialConvolution

open Polynomial

/-!
Coefficient-level convolution for a finite coefficient vector.  This is the
ordinary polynomial multiplication law used before the separate modulo-23
cyclic reduction is proved.
-/

theorem coeff_sum_monomial_mul
    {R : Type*} [Semiring R] {n : ℕ}
    (m : Fin n → R) (q : Polynomial R) (N : ℕ) :
    ((∑ i : Fin n, Polynomial.C (m i) * Polynomial.X ^ (i : ℕ)) * q).coeff N =
      ∑ i : Fin n, if (i : ℕ) ≤ N then m i * q.coeff (N - i) else 0 := by
  rw [Polynomial.coeff_mul]
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner (i : Fin n) :
      ∑ x ∈ Finset.antidiagonal N,
          (if x.1 = (i : ℕ) then m i else 0) * q.coeff x.2 =
        if (i : ℕ) ≤ N then m i * q.coeff (N - i) else 0 := by
    by_cases hi : (i : ℕ) ≤ N
    · have hmem : ((i : ℕ), N - (i : ℕ)) ∈ Finset.antidiagonal N := by
        rw [Finset.mem_antidiagonal]
        omega
      rw [Finset.sum_eq_single ((i : ℕ), N - (i : ℕ))]
      · simp [hi]
      · intro b hb hne
        by_cases hbi : b.1 = (i : ℕ)
        · have hb2 : b.2 = N - (i : ℕ) := by
            have hsum := Finset.mem_antidiagonal.mp hb
            omega
          exact False.elim (hne (Prod.ext hbi hb2))
        · simp [hbi]
      · simp [hmem]
    · simp only [if_neg hi]
      apply Finset.sum_eq_zero
      intro b hb
      have hbi : b.1 ≠ (i : ℕ) := by
        intro hbi
        have hsum := Finset.mem_antidiagonal.mp hb
        omega
      simp [hbi]
  simp_rw [hinner]

abbrev F₂ := ZMod 2
abbrev Message := Fin 12 → F₂

noncomputable def messagePolynomial (m : Message) : Polynomial F₂ :=
  ∑ i : Fin 12, Polynomial.C (m i) * Polynomial.X ^ (i : ℕ)

theorem messagePolynomial_mul_coeff (m : Message) (q : Polynomial F₂) (N : ℕ) :
    (messagePolynomial m * q).coeff N =
      ∑ i : Fin 12, if (i : ℕ) ≤ N then m i * q.coeff (N - i) else 0 := by
  exact coeff_sum_monomial_mul m q N

theorem messagePolynomial_coeff_zero_of_ge (m : Message) {N : ℕ}
    (hN : 12 ≤ N) :
    (messagePolynomial m).coeff N = 0 := by
  unfold messagePolynomial
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : N ≠ (i : ℕ) := by omega
  simp [hne]

end InfoGeometry.Combinatorics.BinaryGolayPolynomialConvolution
