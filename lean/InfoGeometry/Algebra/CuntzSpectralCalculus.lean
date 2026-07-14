import Mathlib
import InfoGeometry.Algebra.CuntzPrimonHamiltonian

/-!
# Cuntz Spectral Calculus: p(H) = Σ p(ε_i) P_i (PROVED)

For H = Σ ε_i P_i, any polynomial p satisfies p(H) = Σ p(ε_i) P_i.
-/
open InfoGeometry.Algebra.CuntzPrimonHamiltonian
open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace CuntzSpectralCalculus

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

end CuntzSpectralCalculus
