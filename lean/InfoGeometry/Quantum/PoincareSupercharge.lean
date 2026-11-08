import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzPrimonHamiltonian
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
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
open InfoGeometry.Canonical.PauliHestenesSpinMomentum

noncomputable section

namespace InfoGeometry.Quantum.PoincareSupercharge

/-- The Casimir P^μ P_μ = H² - p² = H² in the rest frame.
    From `H_pow_eq n ε 2` we get H² = Σ ε_i² P_i. -/
theorem casimir_sq (n : ℕ) (ε : Fin n → ℂ) :
    (hamiltonian n ε) * (hamiltonian n ε) = ∑ i : Fin n, (ε i * ε i) • P n i := by
  simpa [pow_two] using H_pow_eq n ε 2

/-- Eigenvalue of the Casimir on projector P_i: H²·P_i = ε_i²·P_i. -/
theorem casimir_eigenvalue (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    (hamiltonian n ε * hamiltonian n ε) * P n i = (ε i * ε i) • P n i := by
  calc
    (hamiltonian n ε * hamiltonian n ε) * P n i
        = hamiltonian n ε * (hamiltonian n ε * P n i) := by
          rw [mul_assoc]
    _ = hamiltonian n ε * (ε i • P n i) := by
          rw [H_mul_P]
    _ = ε i • (hamiltonian n ε * P n i) := by
          rw [mul_smul_comm]
    _ = ε i • (ε i • P n i) := by
          rw [H_mul_P]
    _ = (ε i * ε i) • P n i := by
          rw [smul_smul]

/-- The finite primon Hamiltonian `H = Σ log(p_i) P_i` has Casimir eigenvalues
`(log p_i)²` on the corresponding Cuntz range projectors. -/
theorem primon_casimir_eigenvalues
    (n : ℕ) (primes : Fin n → ℕ) (hprimes : ∀ i, Nat.Prime (primes i)) :
    ∀ i,
      Nat.Prime (primes i) ∧
        (hamiltonian n (fun i => (Real.log (primes i : ℝ) : ℂ)) *
            hamiltonian n (fun i => (Real.log (primes i : ℝ) : ℂ))) * P n i =
          (((Real.log (primes i : ℝ) : ℂ) ^ 2) • P n i) := by
  intro i
  refine ⟨hprimes i, ?_⟩
  simpa [pow_two] using
    casimir_eigenvalue n (fun i => (Real.log (primes i : ℝ) : ℂ)) i

/--
The Pauli trace formula recovers the four-momentum components from the
super-Poincare anticommutator matrix `2 σ^μ P_μ`.
-/
alias pauli_supercharge_trace_recovers_four_momentum :=
  PauliParavector.superchargeMomentumReadout_eq_components

/--
The lowered Pauli trace formula recovers the metric-lowered four-momentum
components from the same super-Poincare anticommutator matrix.
-/
alias pauli_supercharge_trace_recovers_lowered_four_momentum :=
  PauliParavector.loweredSuperchargeMomentumReadout_eq_components

/--
The determinant of `{Q,Qbar} = 2 σ·P` is four times the finite Pauli/Minkowski
Casimir.
-/
alias pauli_supercharge_anticommutator_det_eq_four_casimir :=
  PauliParavector.det_superPoincareAnticommutatorMatrix_eq_four_minkowskiNormSq

/--
The total trace of `{Q,Qbar} = 2 σ·P` is four times the energy component.
-/
alias pauli_supercharge_anticommutator_trace_eq_four_energy :=
  PauliParavector.trace_superPoincareAnticommutatorMatrix_eq_four_energy

/--
The supercharge anticommutator matrix is determinant-singular exactly on the
finite null cone.
-/
theorem pauli_supercharge_anticommutator_singular_iff_null
    (P : PauliParavector) :
    P.IsSingularSuperPoincareAnticommutator ↔ P.IsNull :=
  (PauliParavector.isNull_iff_isSingularSuperPoincareAnticommutator P).symm

/--
Timelike finite Pauli momenta have positive determinant for the supercharge
anticommutator matrix.
-/
alias pauli_supercharge_anticommutator_det_pos_of_timelike :=
  PauliParavector.det_superPoincareAnticommutatorMatrix_pos_of_timelike

/--
Spacelike finite Pauli momenta have negative determinant real part for the
supercharge anticommutator matrix.
-/
alias pauli_supercharge_anticommutator_det_neg_of_spacelike :=
  PauliParavector.det_superPoincareAnticommutatorMatrix_neg_of_spacelike

end InfoGeometry.Quantum.PoincareSupercharge
