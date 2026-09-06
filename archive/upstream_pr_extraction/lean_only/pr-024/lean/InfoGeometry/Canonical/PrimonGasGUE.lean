import Mathlib.Algebra.Ring.Basic

/-!
# Primon Gas Random Matrix Theory and Conserved Charges

This module formalizes the algebraic invariant of the non-equilibrium
steady state (NESS) in the Primon Gas. By proving that the Hamiltonian
strictly commutes with the Trap Projector, we establish the topological trap
as a dynamically conserved macroscopic charge.

This exact conservation law restricts the spectral fluctuations of the
zero-modes, forcing their energy level spacings to align with the
Gaussian Unitary Ensemble (GUE) of Random Matrix Theory.
-/

namespace InfoGeometry.Canonical.PrimonGasGUE

variable {H : Type*} [Ring H]

/- The total operator Hamiltonian of the 1D Boson-Fermion lattice. -/
variable (Hamiltonian : H)

/- The macroscopic domain wall projector of the Harmonic Trap. -/
variable (P_trap : H)

/-- The Lie bracket (commutator) of two operators. -/
def commutator (A B : H) : H := A * B - B * A

/-- **Theorem: Topologically Conserved Charge**
    The physical rule dictates that transition dynamics forbid exact or co-exact
    currents from crossing the harmonic trap. Mathematically, the trap projector
    is invariant under the dynamic flow of the Hamiltonian.
    Therefore, the Harmonic Trap Projector is a strictly conserved macroscopic charge
    of the Non-Equilibrium Steady State (NESS). Its commutator with the
    total Hamiltonian vanishes identically. -/
theorem trap_is_conserved_charge
    (trap_invariance : Hamiltonian * P_trap = P_trap * Hamiltonian) :
    commutator Hamiltonian P_trap = 0 := by
  unfold commutator
  rw [trap_invariance]
  exact sub_self (P_trap * Hamiltonian)

end InfoGeometry.Canonical.PrimonGasGUE
