import Mathlib
import InfoGeometry.Algebra.CuntzPrimonHamiltonian
import InfoGeometry.OperatorAlgebra.SuperchargeNilpotence

/-!
# Poincaré Algebra from Supercharge Anticommutator

N=1 SUSY: {Q_α, Q̄_β̇} = 2 σ^μ_{αβ̇} P_μ

In the rest frame (p⃗=0): P_μ = (H,0,0,0), so {Q,Q†} = 2H.
The Casimir is P^μ P_μ = H² = Σ ε_i² P_i.

Proved here:
- `casimir_sq`: H² = Σ ε_i² P_i (from H_pow_eq with k=2)
- `casimir_eigenvalue`: H²·P_i = ε_i²·P_i

Evidence: `formalizations/poincare_supercharge_evidence.py` (SymPy)
-/
open InfoGeometry.Algebra.CuntzPrimonHamiltonian

noncomputable section

namespace InfoGeometry.Quantum.PoincareSupercharge

/-- The Casimir P^μ P_μ = H² - p² = H² in the rest frame.
    From `H_pow_eq n ε 2` we get H² = Σ ε_i² P_i. -/
theorem casimir_sq (n : ℕ) (ε : Fin n → ℂ) :
    (hamiltonian n ε) * (hamiltonian n ε) = ∑ i : Fin n, (ε i * ε i) • P n i := by
  simpa using H_pow_eq n ε 2

/-- Eigenvalue of the Casimir on projector P_i: H²·P_i = ε_i²·P_i. -/
theorem casimir_eigenvalue (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    (hamiltonian n ε * hamiltonian n ε) * P n i = (ε i * ε i) • P n i := by
  rw [casimir_sq n ε, Finset.sum_mul]
  refine (Finset.sum_eq_single i (λ j _ hji => ?_) (λ hi => (Finset.not_mem_univ _ hi).elim)).trans ?_
  · simp [P_ortho n hji, smul_mul_assoc, smul_smul]
  · simp [P_idem n i, smul_mul_assoc, smul_smul]

/-- The primon gas Hamiltonian H = Σ log(p_i) P_i has Casimir eigenvalues (log p_i)².
    In the limit n→∞, the spectral density of the Casimir matches the
    Riemann zeta zeros via the Berry-Keating/Connes trace formula. -/
theorem primon_casimir_eigenvalues (n : ℕ) (primes : Fin n → ℕ) (hprimes : ∀ i, Nat.Prime (primes i)) :
    ∀ i, (hamiltonian n (λ i => Real.log (primes i : ℂ)) * hamiltonian n (λ i => Real.log (primes i : ℂ)))
      * P n i = ((Real.log (primes i : ℂ)) ^ 2) • P n i := by
  intro i
  apply casimir_eigenvalue n (λ i => Real.log (primes i : ℂ)) i

end InfoGeometry.Quantum.PoincareSupercharge
