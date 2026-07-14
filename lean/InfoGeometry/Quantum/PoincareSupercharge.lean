import Mathlib
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

namespace PoincareSupercharge

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
theorem pauli_supercharge_trace_recovers_four_momentum
    (P : PauliParavector) (a : Fin 4) :
    PauliParavector.superchargeMomentumReadout a P =
      match a with
      | 0 => (P.energy : ℂ)
      | 1 => (P.px : ℂ)
      | 2 => (P.py : ℂ)
      | 3 => (P.pz : ℂ) :=
  PauliParavector.superchargeMomentumReadout_eq_components P a

/--
The lowered Pauli trace formula recovers the metric-lowered four-momentum
components from the same super-Poincare anticommutator matrix.
-/
theorem pauli_supercharge_trace_recovers_lowered_four_momentum
    (P : PauliParavector) (a : Fin 4) :
    PauliParavector.loweredSuperchargeMomentumReadout a P =
      match a with
      | 0 => (P.energy : ℂ)
      | 1 => (-(P.px) : ℂ)
      | 2 => (-(P.py) : ℂ)
      | 3 => (-(P.pz) : ℂ) :=
  PauliParavector.loweredSuperchargeMomentumReadout_eq_components P a

/--
The determinant of `{Q,Qbar} = 2 σ·P` is four times the finite Pauli/Minkowski
Casimir.
-/
theorem pauli_supercharge_anticommutator_det_eq_four_casimir
    (P : PauliParavector) :
    Matrix.det P.superPoincareAnticommutatorMatrix =
      ((4 * P.minkowskiNormSq : ℝ) : ℂ) :=
  PauliParavector.det_superPoincareAnticommutatorMatrix_eq_four_minkowskiNormSq P

/--
The total trace of `{Q,Qbar} = 2 σ·P` is four times the energy component.
-/
theorem pauli_supercharge_anticommutator_trace_eq_four_energy
    (P : PauliParavector) :
    Matrix.trace P.superPoincareAnticommutatorMatrix = ((4 * P.energy : ℝ) : ℂ) :=
  PauliParavector.trace_superPoincareAnticommutatorMatrix_eq_four_energy P

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
theorem pauli_supercharge_anticommutator_det_pos_of_timelike
    {P : PauliParavector}
    (hP : P.IsTimelike) :
    0 < (Matrix.det P.superPoincareAnticommutatorMatrix).re :=
  PauliParavector.det_superPoincareAnticommutatorMatrix_pos_of_timelike hP

/--
Spacelike finite Pauli momenta have negative determinant real part for the
supercharge anticommutator matrix.
-/
theorem pauli_supercharge_anticommutator_det_neg_of_spacelike
    {P : PauliParavector}
    (hP : P.IsSpacelike) :
    (Matrix.det P.superPoincareAnticommutatorMatrix).re < 0 :=
  PauliParavector.det_superPoincareAnticommutatorMatrix_neg_of_spacelike hP

end PoincareSupercharge
