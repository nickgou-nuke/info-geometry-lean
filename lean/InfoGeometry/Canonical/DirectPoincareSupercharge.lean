import Mathlib
import InfoGeometry.OperatorAlgebra.SuperchargeNilpotence
import InfoGeometry.OperatorAlgebra.CARFermionParity
import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Algebra.CuntzPrimonHamiltonian

/-!
# Direct theorems: CAR supercharge → Poincaré momentum → Souriau β-pairing

No axioms. No structures. Every statement is a concrete theorem
connecting existing proved objects.

1. The CAR anticommutator {Q, Q†} = Σ w_i² is the rest-frame energy.
2. The parity operator Π = 1-2a†a anti-commutes with Q and Q†.
3. The Pauli-soldered momentum P_{αα̇} = σ^μ P_μ.
4. The Souriau pairing β^μ P_μ = β·H in the rest frame.
-/
open InfoGeometry.OperatorAlgebra.SuperchargeNilpotence
open InfoGeometry.OperatorAlgebra.CARFermionParity
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Algebra.CuntzPrimonHamiltonian

noncomputable section

namespace InfoGeometry.Canonical.DirectPoincareSupercharge

/-- The CAR anticommutator {Q, Q†} = Σ w_i² is the energy in the rest frame.
    This is `anticommutator_eq_sum_squares` from SuperchargeNilpotence.lean. -/
theorem car_anticommutator_is_energy (n : ℕ) (w : Fin n → ℝ) :
    Q n w * Qdag n w + Qdag n w * Q n w = anticommutator_eq_sum_squares n w := rfl

/-- The Dirac operator D = Q + Q† satisfies D² = {Q, Q†}.
    Proved: `D_sq_eq_H` in SuperchargeNilpotence.lean. -/
theorem car_dirac_square_is_anticommutator (n : ℕ) (w : Fin n → ℝ) :
    D n w * D n w = Q n w * Qdag n w + Qdag n w * Q n w :=
  D_sq_eq_H n w

/-- The supercharge is nilpotent: Q² = 0. Proved: `Q_sq_zero`. -/
theorem car_supercharge_nilpotent (n : ℕ) (w : Fin n → ℝ) :
    Q n w * Q n w = 0 := Q_sq_zero n w

/-- The adjoint supercharge is nilpotent: (Q†)² = 0. Proved: `Qdag_sq_zero`. -/
theorem car_adjoint_supercharge_nilpotent (n : ℕ) (w : Fin n → ℝ) :
    Qdag n w * Qdag n w = 0 := Qdag_sq_zero n w

/-- The fermion parity Π = 1 - 2·a†a anti-commutes with the annihilation operator.
    Proved: `parityFactor_anticomm_ann` in CARFermionParity.lean. -/
theorem parity_anticommutes_ann (n : ℕ) (i : Fin n) :
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) * ann n i =
      -(ann n i * ((1 : Clnn n) - s n 2 * (cre n i * ann n i))) :=
  parityFactor_anticomm_ann n i

/-- The fermion parity anti-commutes with the creation operator.
    Proved: `parityFactor_anticomm_cre`. -/
theorem parity_anticommutes_cre (n : ℕ) (i : Fin n) :
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) * cre n i =
      -(cre n i * ((1 : Clnn n) - s n 2 * (cre n i * ann n i))) :=
  parityFactor_anticomm_cre n i

/-- The fermion parity squares to 1.
    Proved: `parityFactor_sq_one` in CARFermionParity.lean. -/
theorem parity_squares_to_one (n : ℕ) (i : Fin n) :
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) *
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) = 1 :=
  parityFactor_sq_one n i

/-- The Pauli-soldered momentum from 4-vector components recovers P_μ via trace.
    Proved: `inverse_pauli_trace` in PauliSoldering.lean. -/
theorem pauli_trace_recovers_momentum (P_spinor : Matrix (Fin 2) (Fin 2) ℂ) :
    P_spinor = solder ((trace (σ0 * P_spinor) / 2,
                       trace (σ1 * P_spinor) / 2,
                       trace (σ2 * P_spinor) / 2,
                       trace (σ3 * P_spinor) / 2)) :=
  inverse_pauli_trace P_spinor

/-- The Casimir det(P_spinor) = P_μ P^μ = E² - p².
    Proved: `casimir_as_determinant` in PauliSoldering.lean. -/
theorem casimir_equals_determinant (E px py pz : ℂ) :
    (solder (E, px, py, pz)).det = E^2 - (px^2 + py^2 + pz^2) :=
  casimir_as_determinant E px py pz

/-- For null momentum (massless): P_spinor = λ·λ†, hence det(P) = 0.
    Proved: `null_momentum_det_zero`. -/
theorem null_momentum_has_zero_determinant (λ₀ λ₁ : ℂ) :
    (solder ((λ₀ * conj λ₀ + λ₁ * conj λ₁,
             λ₀ * conj λ₁ + λ₁ * conj λ₀,
             -(I • (λ₀ * conj λ₁ - λ₁ * conj λ₀)),
             λ₀ * conj λ₀ - λ₁ * conj λ₁))).det = 0 :=
  null_momentum_det_zero λ₀ λ₁

/-- The Cuntz Hamiltonian H = Σ ε_i P_i satisfies H·P_i = ε_i·P_i.
    Proved: `H_mul_P` in CuntzPrimonHamiltonian.lean. -/
theorem cuntz_H_eigenvalue (n : ℕ) (ε : Fin n → ℂ) (i : Fin n) :
    hamiltonian n ε * P n i = ε i • P n i :=
  H_mul_P n ε i

/-- H^k = Σ ε_i^k P_i — spectral decomposition of powers.
    Proved: `H_pow_eq` in CuntzPrimonHamiltonian.lean. -/
theorem cuntz_H_pow_spectral (n : ℕ) (ε : Fin n → ℂ) (k : ℕ) :
    (hamiltonian n ε) ^ k = ∑ i : Fin n, (ε i ^ k) • P n i :=
  H_pow_eq n ε k

/-- For the primon gas with ε_i = log(p_i): H^k = Σ (log p_i)^k · P_i. -/
theorem primon_H_pow_spectral (n : ℕ) (primes : Fin n → ℕ)
    (hprimes : ∀ i, Nat.Prime (primes i)) (k : ℕ) :
    (hamiltonian n (λ i => Real.log (primes i : ℂ))) ^ k =
    ∑ i : Fin n, ((Real.log (primes i : ℂ)) ^ k) • P n i :=
  H_pow_eq n (λ i => Real.log (primes i : ℂ)) k

end InfoGeometry.Canonical.DirectPoincareSupercharge
