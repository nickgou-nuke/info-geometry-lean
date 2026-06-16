import Mathlib
import InfoGeometry.Algebra.CuntzPrimonHamiltonian

/-!
# Cuntz Spectral Calculus: p(H) = Σ p(ε_i) P_i (PROVED)

For H = Σ ε_i P_i, any polynomial p satisfies p(H) = Σ p(ε_i) P_i.
-/
open InfoGeometry.Algebra.CuntzPrimonHamiltonian

noncomputable section

namespace InfoGeometry.Algebra.CuntzSpectralCalculus

theorem polynomial_spectral (n : ℕ) (ε : Fin n → ℂ) (p : Polynomial ℂ) :
    Polynomial.aeval (hamiltonian n ε) p =
    ∑ i : Fin n, (Polynomial.aeval (ε i) p) • P n i := by
  rw [Polynomial.aeval_eq_sum_range (x := hamiltonian n ε) (p := p)]
  -- LHS = Σ_k coeff_k · H^k
  -- RHS = Σ_i (Σ_k coeff_k · ε_i^k) · P_i = Σ_k coeff_k · Σ_i ε_i^k · P_i = Σ_k coeff_k · H^k
  have h_rhs : (∑ i : Fin n, (Polynomial.aeval (ε i) p) • P n i) =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        (Polynomial.coeff p k) • (hamiltonian n ε) ^ k := by
    calc
      (∑ i : Fin n, (Polynomial.aeval (ε i) p) • P n i)
          = (∑ i : Fin n, (∑ k ∈ Finset.range (p.natDegree + 1),
              (Polynomial.coeff p k) • (ε i ^ k)) • P n i) := by
        refine Finset.sum_congr rfl (λ i _ => ?_)
        rw [Polynomial.aeval_eq_sum_range (x := ε i) (p := p)]
        simp [smul_eq_mul]
      _ = (∑ i : Fin n, ∑ k ∈ Finset.range (p.natDegree + 1),
            ((Polynomial.coeff p k) * (ε i ^ k)) • P n i) := by
        simp_rw [Finset.sum_smul]
      _ = (∑ k ∈ Finset.range (p.natDegree + 1), ∑ i : Fin n,
            ((Polynomial.coeff p k) * (ε i ^ k)) • P n i) := by
        rw [Finset.sum_comm]
      _ = (∑ k ∈ Finset.range (p.natDegree + 1),
            (Polynomial.coeff p k) • (∑ i : Fin n, (ε i ^ k) • P n i)) := by
        simp [Finset.smul_sum, smul_smul, mul_comm, smul_eq_mul]
      _ = (∑ k ∈ Finset.range (p.natDegree + 1),
            (Polynomial.coeff p k) • (hamiltonian n ε) ^ k) := by
        simp [H_pow_eq n ε]
  rw [h_rhs]

end InfoGeometry.Algebra.CuntzSpectralCalculus
