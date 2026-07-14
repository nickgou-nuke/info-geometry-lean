import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Meta.Architecture

open scoped BigOperators

/-!
# Relative Modular Commuting Lift

Finite, strict operator lane that keeps `Δ` primary and exposes commuting
spectral consequences before any unbounded/type-III interface claims.

This file is intentionally conservative:
- no new ontology beyond existing finite owners,
- no unbounded functional-calculus claims,
- only diagonal commuting consequences already derivable from
  `RelativeModularOperator` and `RelativeModularHamiltonian`.
-/

namespace RelativeModularCommutingLift

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RelativeModularHamiltonian
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

section Finite

variable {n : ℕ} [Nonempty (Fin n)]

/--
Any two finite relative modular operators commute on the diagonal commuting
lane.
-/
@[rep_depth operator]
theorem relativeModularOperator_mul_comm
    (q q0 r r0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0
        * relativeModularOperator (n := n) r r0
      = relativeModularOperator (n := n) r r0
          * relativeModularOperator (n := n) q q0 := by
  unfold relativeModularOperator RelativeStatePair.modularOperator
  simp [diagMatrix, Matrix.diagonal_mul_diagonal, mul_comm]

/-- Commutator form of `relativeModularOperator_mul_comm`. -/
@[rep_depth operator]
theorem relativeModularOperator_commute
    (q q0 r r0 : PositiveRay (Fin n)) :
    Commute (relativeModularOperator (n := n) q q0)
      (relativeModularOperator (n := n) r r0) := by
  simpa [Commute] using relativeModularOperator_mul_comm (n := n) q q0 r r0

/--
Logarithmic cocycle on the diagonal readout of `Δ`.
This is the finite commuting spectral `log(Δ)` law at each coordinate.
-/
@[rep_depth operator]
theorem log_relativeModularOperator_diag_cocycle
    (q q0 q1 : PositiveRay (Fin n)) (i : Fin n) :
    Real.log (relativeModularOperator (n := n) q q1 i i)
      = Real.log (relativeModularOperator (n := n) q q0 i i)
          + Real.log (relativeModularOperator (n := n) q0 q1 i i) := by
  rw [← relativeLogDensity_eq_log_relativeModularOperator_diag (n := n) q q1 i]
  rw [← relativeLogDensity_eq_log_relativeModularOperator_diag (n := n) q q0 i]
  rw [← relativeLogDensity_eq_log_relativeModularOperator_diag (n := n) q0 q1 i]
  exact relativeLogDensity_cocycle q q0 q1 i

/--
Derived Hamiltonian (`K := -log Δ`) cocycle at diagonal coordinates.
-/
@[rep_depth operator]
theorem relativeModularHamiltonianOperator_diag_cocycle
    (q q0 q1 : PositiveRay (Fin n)) (i : Fin n) :
    relativeModularHamiltonianOperator (n := n) q q1 i i
      = relativeModularHamiltonianOperator (n := n) q q0 i i
          + relativeModularHamiltonianOperator (n := n) q0 q1 i i := by
  rw [relativeModularHamiltonianOperator_diag]
  rw [relativeModularHamiltonianOperator_diag]
  rw [relativeModularHamiltonianOperator_diag]
  exact relativeModularPotential_cocycle (q := q) (q0 := q0) (q1 := q1) i

/--
Finite commuting-lift package:
`Δ`-cocycle, diagonal `log Δ` cocycle, and operator `K` cocycle.
-/
@[rep_depth operator, capstone]
theorem finite_commuting_lift_package
    (q q0 q1 : PositiveRay (Fin n)) (i : Fin n) :
    (relativeModularOperator (n := n) q q1
      = relativeModularOperator (n := n) q q0
          * relativeModularOperator (n := n) q0 q1)
      ∧ (Real.log (relativeModularOperator (n := n) q q1 i i)
          = Real.log (relativeModularOperator (n := n) q q0 i i)
              + Real.log (relativeModularOperator (n := n) q0 q1 i i))
      ∧ (relativeModularHamiltonianOperator (n := n) q q1
          = relativeModularHamiltonianOperator (n := n) q q0
              + relativeModularHamiltonianOperator (n := n) q0 q1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact relativeModularOperator_cocycle (n := n) q q0 q1
  · exact log_relativeModularOperator_diag_cocycle (n := n) q q0 q1 i
  · exact relativeModularHamiltonianOperator_cocycle (n := n) q q0 q1

end Finite

end RelativeModularCommutingLift
