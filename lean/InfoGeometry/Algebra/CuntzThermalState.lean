import Mathlib
import InfoGeometry.Algebra.CuntzSpectralCalculus
import InfoGeometry.Algebra.CuntzPrimonHamiltonian

/-!
# Cuntz Thermal State: exp_N(-β H) = Σ exp_N(-β ε_i) P_i

For H = Σ ε_i P_i with orthogonal projectors P_i summing to 1,
the truncated exponential series diagonalizes:

  Σ_{k=0}^N (-β)^k/k! · H^k = Σ_i (Σ_{k=0}^N (-β ε_i)^k/k!) · P_i

Proof: `H^k = Σ ε_i^k P_i` (H_pow_eq) and linearity.

For the primon gas with ε_i = log(p_i), this gives the truncated
partition function and thermal Gibbs state. In the limit N→∞ and
n→∞ (over all primes), this converges to the Riemann zeta function.

Reference: Bost–Connes (1995), Section 2.
-/
open InfoGeometry.Algebra.CuntzPrimonHamiltonian
open InfoGeometry.Algebra.CuntzSpectralCalculus
open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzThermalState

/-- The truncated exponential polynomial: exp_N(x) = Σ_{k=0}^N x^k / k!. -/
noncomputable def truncExp (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (N+1), Polynomial.monomial k (1 / (Nat.factorial k : ℂ))

/-- exp_N(H) = Σ_i exp_N(ε_i) · P_i. Direct corollary of polynomial_spectral. -/
theorem truncExp_spectral (n : ℕ) (ε : Fin n → ℂ) (N : ℕ) :
    Polynomial.aeval (hamiltonian n ε) (truncExp N) =
    ∑ i : Fin n, (Polynomial.aeval (ε i) (truncExp N)) • P n i :=
  polynomial_spectral n ε (truncExp N)

/-- exp_N(-β·H) = Σ_i exp_N(-β·ε_i) · P_i. -/
theorem truncExp_neg_beta_spectral (n : ℕ) (ε : Fin n → ℂ) (β : ℂ) (N : ℕ) :
    Polynomial.aeval (hamiltonian n ε)
      (truncExp N).comp (Polynomial.C (-β) * Polynomial.X) =
    ∑ i : Fin n,
      (Polynomial.aeval (ε i) ((truncExp N).comp (Polynomial.C (-β) * Polynomial.X))) • P n i :=
  polynomial_spectral n ε ((truncExp N).comp (Polynomial.C (-β) * Polynomial.X))

/-- Explicit formula: Σ_{k=0}^N (-β·ε_i)^k/k! · P_i. -/
theorem truncExp_neg_beta_explicit (n : ℕ) (ε : Fin n → ℂ) (β : ℂ) (N : ℕ) :
    Polynomial.aeval (hamiltonian n ε)
      ((truncExp N).comp (Polynomial.C (-β) * Polynomial.X)) =
    ∑ i : Fin n,
      (∑ k ∈ Finset.range (N+1), ((-β * ε i) ^ k / (Nat.factorial k : ℂ))) • P n i := by
  rw [truncExp_neg_beta_spectral n ε β N]
  refine Finset.sum_congr rfl (λ i _ => ?_)
  simp [truncExp, Polynomial.aeval_comp, Polynomial.aeval_mul,
    Polynomial.aeval_C, Polynomial.aeval_X, smul_eq_mul, mul_comm]

/-- The primon gas thermal state for primes up to index n:
    ρ_N(β) = Σ_{i<n} (Σ_{k≤N} (-β·log p_i)^k/k!) · P_i.

    In the limit N→∞, this converges to Σ_i p_i^{-β} · P_i.
    In the limit n→∞, Tr(ρ_∞(β)) → ζ(β) for Re(β) > 1. -/
theorem primon_thermal_state (primes : Fin 3 → ℕ) (hprimes : ∀ i, Nat.Prime (primes i)) (β : ℂ) (N : ℕ) :
    Polynomial.aeval (hamiltonian 3 (λ i => Real.log (primes i : ℂ)))
      ((truncExp N).comp (Polynomial.C (-β) * Polynomial.X)) =
    ∑ i : Fin 3,
      (∑ k ∈ Finset.range (N+1), ((-β * Real.log (primes i : ℂ)) ^ k / (Nat.factorial k : ℂ))) • P 3 i :=
  truncExp_neg_beta_explicit 3 (λ i => Real.log (primes i : ℂ)) β N

end InfoGeometry.Algebra.CuntzThermalState
