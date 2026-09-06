import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzPrimonHamiltonian

/-!
# Cuntz Spectral Calculus: p(H) = Σ p(ε_i) P_i (PROVED)

For H = Σ ε_i P_i, any polynomial p satisfies p(H) = Σ p(ε_i) P_i.
-/
open InfoGeometry.Algebra.CuntzPrimonHamiltonian
open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzSpectralCalculus

theorem polynomial_spectral (n : ℕ) (ε : Fin n → ℂ) (p : Polynomial ℂ) :
    Polynomial.aeval (hamiltonian n ε) p =
    ∑ i : Fin n, (Polynomial.aeval (ε i) p) • P n i := by
  rw [Polynomial.aeval_eq_sum_range (x := hamiltonian n ε) (p := p)]
  -- LHS = Σ_k coeff_k • H^k
  simp_rw [H_pow_eq n ε, Finset.smul_sum, smul_smul, mul_comm]
  -- LHS = Σ_k Σ_i (coeff_k * ε_i ^ k) • P n i
  -- Exchange sums: = Σ_i Σ_k ...
  rw [Finset.sum_comm]
  -- RHS = Σ_i (Σ_k coeff_k • (ε i : CuntzAlg n)^k) • P_i
  -- For each i, need: Σ_k (coeff_k * ε_i ^ k) • P_i = (aeval ε_i p) • P_i
  refine Finset.sum_congr rfl (λ i _ => ?_)
  rw [Polynomial.aeval_eq_sum_range (x := ε i) (p := p)]
  simp [Finset.sum_smul, mul_comm, smul_eq_mul]

theorem polynomial_spectral_mul_P
    (n : ℕ) (ε : Fin n → ℂ) (p : Polynomial ℂ) (i : Fin n) :
    Polynomial.aeval (hamiltonian n ε) p * P n i =
      (Polynomial.aeval (ε i) p) • P n i := by
  rw [polynomial_spectral, Finset.sum_mul]
  have h : ∀ j, (Polynomial.aeval (ε j) p • P n j) * P n i =
      (if j = i then (Polynomial.aeval (ε i) p) • P n i else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [P_idem n i]
    · simp [P_ortho n hji, hji]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  simp [Finset.mem_univ]

theorem P_mul_polynomial_spectral
    (n : ℕ) (ε : Fin n → ℂ) (p : Polynomial ℂ) (i : Fin n) :
    P n i * Polynomial.aeval (hamiltonian n ε) p =
      (Polynomial.aeval (ε i) p) • P n i := by
  rw [polynomial_spectral, Finset.mul_sum]
  have h : ∀ j, P n i * (Polynomial.aeval (ε j) p • P n j) =
      (if j = i then (Polynomial.aeval (ε i) p) • P n i else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [P_idem n i]
    · simp [P_ortho n (Ne.symm hji), hji]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  simp [Finset.mem_univ]

end InfoGeometry.Algebra.CuntzSpectralCalculus
