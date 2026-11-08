import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Primon gas conserved-charge algebra

This module proves only the elementary algebraic fact that commuting elements
have zero commutator.  It does not prove a random-matrix, GUE-spacing, or
non-equilibrium statistical theorem.
-/

namespace InfoGeometry.Canonical.PrimonGasGUE

variable {H : Type*} [Ring H]

/- The total operator Hamiltonian of the 1D Boson-Fermion lattice. -/
variable (Hamiltonian : H)

/- The macroscopic domain wall projector of the Harmonic Trap. -/
variable (P_trap : H)

/-- The Lie bracket (commutator) of two operators. -/
def commutator (A B : H) : H := A * B - B * A

/-- If the Hamiltonian commutes with the trap element, their commutator is zero. -/
theorem trap_is_conserved_charge
    (trap_invariance : Hamiltonian * P_trap = P_trap * Hamiltonian) :
    commutator Hamiltonian P_trap = 0 := by
  unfold commutator
  rw [trap_invariance]
  exact sub_self (P_trap * Hamiltonian)

end InfoGeometry.Canonical.PrimonGasGUE
