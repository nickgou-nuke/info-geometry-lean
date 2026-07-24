import InfoGeometry.Quantum.QutritPrimitiveWeyl
import InfoGeometry.Quantum.QutritGates
import InfoGeometry.Quantum.QutritCircuitGeometry

/-!
# Generalized Pauli integration spine

This module is a theorem-safe integration point for the repository's existing
finite generalized-Pauli material.

It deliberately packages only what is already kernel-checked:

* the abstract finite Weyl-pair commutator calculus;
* the concrete qutrit Sylvester clock/shift pair and primitive cubic phase;
* the `Z₃` sector-projector eigenbasis used by the qutrit clock;
* the normalized finite Gell--Mann qutrit generators and their rotation gates;
* finite Gell--Mann string bookkeeping for qutrit registers.

It does not assert a generic `d`-dimensional Sylvester basis, Hilbert--Schmidt
orthogonality for all `d`, multi-qubit Pauli-group tensor closure, or a
higher-spin `SU(2)` representation theorem.
-/

noncomputable section

namespace InfoGeometry.Quantum.GeneralizedPauli

open InfoGeometry.Physics.HestenesCuntzPhaseSpace
open InfoGeometry.Physics.MD014TriSpinZ3Projectors
open InfoGeometry.Topology.Parafermion
open InfoGeometry.Quantum.QutritBraidIncidenceBridge
open InfoGeometry.Quantum.Qutrit
open InfoGeometry.Quantum.QutritCircuitGeometry

/-- Alias for the already-formalized finite Weyl-pair abstraction. -/
abbrev FiniteGeneralizedPauliPair (N : ℕ) (A : Type*) [Ring A] [Algebra ℂ A] :=
  FiniteWeylPair N A

/-- Every finite generalized-Pauli/Weyl pair carries both commutator readouts. -/
theorem finiteGeneralizedPauliPair_commutator_packet
    {N : ℕ} {A : Type*} [Ring A] [Algebra ℂ A]
    (W : FiniteGeneralizedPauliPair N A) :
    W.coordinate * W.momentum - W.momentum * W.coordinate =
        (1 - W.q : ℂ) • (W.coordinate * W.momentum) ∧
      W.momentum * W.coordinate - W.coordinate * W.momentum =
        (W.q - 1 : ℂ) • (W.coordinate * W.momentum) := by
  exact ⟨W.coordinate_momentum_commutator, W.momentum_coordinate_commutator⟩

/-- The repository's qutrit Sylvester pair: shift `X`, clock `Z`, primitive phase. -/
theorem qutrit_sylvester_clock_shift_packet :
    qutritGeneralizedPauliX ^ 3 = 1 ∧
      qutritPrimitiveClock ^ 3 = 1 ∧
      qutritPrimitiveClock * qutritGeneralizedPauliX =
        omega • (qutritGeneralizedPauliX * qutritPrimitiveClock) ∧
      IsPrimitiveRoot qutritPrimitiveWeylPair.q 3 ∧
      qutritGeneralizedPauliX ≠ 1 ∧
      qutritGeneralizedPauliX ^ 2 ≠ 1 ∧
      qutritPrimitiveClock ≠ 1 ∧
      qutritPrimitiveClock ^ 2 ≠ 1 := by
  exact ⟨qutritGeneralizedPauliX_exact_order_three.1,
    qutritPrimitiveClock_exact_order_three.1,
    qutritPrimitiveClock_mul_X,
    qutritPrimitiveWeylPair_q_isPrimitiveRoot,
    qutritGeneralizedPauliX_exact_order_three.2.1,
    qutritGeneralizedPauliX_exact_order_three.2.2,
    qutritPrimitiveClock_exact_order_three.2.1,
    qutritPrimitiveClock_exact_order_three.2.2⟩

/-- The qutrit clock eigenspaces are exactly the three orthogonal sector projectors. -/
theorem qutrit_sector_projector_clock_packet :
    sectorProjector0 * sectorProjector0 = sectorProjector0 ∧
      sectorProjector1 * sectorProjector1 = sectorProjector1 ∧
      sectorProjector2 * sectorProjector2 = sectorProjector2 ∧
      sectorProjector0 * sectorProjector1 = 0 ∧
      sectorProjector1 * sectorProjector2 = 0 ∧
      sectorProjector2 * sectorProjector0 = 0 ∧
      sectorProjector0 + sectorProjector1 + sectorProjector2 = 1 ∧
      sectorPhase omega * sectorPhase omega * sectorPhase omega = 1 := by
  exact ⟨sectorProjector0_idempotent,
    sectorProjector1_idempotent,
    sectorProjector2_idempotent,
    sectorProjector0_mul_sectorProjector1,
    sectorProjector1_mul_sectorProjector2,
    sectorProjector2_mul_sectorProjector0,
    sectorProjector_sum_identity,
    sectorPhase_cube_identity omega omega_cube_eq_one⟩

/-- A normalized Gell--Mann qutrit Hamiltonian is Hermitian and traceless, and its
skew-Hermitian exponential is a unitary qutrit gate. -/
theorem qutrit_gellMann_rotation_packet (Θ : Fin 8 → ℝ) :
    Matrix.IsHermitian (rotationHamiltonian Θ : Qutrit.QutritMatrix) ∧
      Matrix.trace (rotationHamiltonian Θ : Qutrit.QutritMatrix) = 0 ∧
      rotationMatrix Θ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  exact ⟨rotationHamiltonian_isHermitian Θ,
    rotationHamiltonian_trace Θ,
    rotationMatrix_mem_unitary Θ⟩

/-- Finite qutrit-register Gell--Mann strings have exactly `9^n` labels. -/
theorem qutrit_gellMannString_card (n : ℕ) :
    Fintype.card (GellMannString n) = 9 ^ n :=
  gellMannString_card n

/-- Consolidated theorem-safe generalized-Pauli inventory exposed to the quantum
`All` fabric. -/
theorem generalized_pauli_repository_synthesis :
    qutritGeneralizedPauliX ^ 3 = 1 ∧
      qutritPrimitiveClock ^ 3 = 1 ∧
      qutritPrimitiveClock * qutritGeneralizedPauliX =
        omega • (qutritGeneralizedPauliX * qutritPrimitiveClock) ∧
      IsPrimitiveRoot qutritPrimitiveWeylPair.q 3 ∧
      sectorProjector0 + sectorProjector1 + sectorProjector2 = 1 ∧
      (∀ Θ : Fin 8 → ℝ,
        Matrix.IsHermitian (rotationHamiltonian Θ : Qutrit.QutritMatrix) ∧
          Matrix.trace (rotationHamiltonian Θ : Qutrit.QutritMatrix) = 0 ∧
          rotationMatrix Θ ∈ Matrix.unitaryGroup (Fin 3) ℂ) ∧
      (∀ n : ℕ, Fintype.card (GellMannString n) = 9 ^ n) := by
  exact ⟨qutrit_sylvester_clock_shift_packet.1,
    qutrit_sylvester_clock_shift_packet.2.1,
    qutrit_sylvester_clock_shift_packet.2.2.1,
    qutrit_sylvester_clock_shift_packet.2.2.2.1,
    qutrit_sector_projector_clock_packet.2.2.2.2.2.2.1,
    qutrit_gellMann_rotation_packet,
    qutrit_gellMannString_card⟩

end InfoGeometry.Quantum.GeneralizedPauli
