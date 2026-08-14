import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Algebra.Basic

/-!
# Abstract cyclic representation and zeta readout

This file contains a small algebraic representation record and a scalar zeta
readout.  The assumptions are only those displayed below; no C*-algebra,
state, or phase-transition structure is constructed here.
-/

namespace InfoGeometry.Physics.BostConnes

open Complex

/-- A ring carrying a complex algebra structure. -/
class BostConnesAlgebra (A : Type*) [Ring A] [Algebra ℂ A]

/-- An algebra representation with a chosen cyclic vector. -/
structure GNSRepresentation (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H] where
  pi : A →ₐ[ℂ] (H →ₗ[ℂ] H)
  vacuum : H
  cyclic : ∀ h : H, ∃ a : A, pi a vacuum = h

/-- The declared scalar partition readout. -/
noncomputable def partitionFunction (β : ℂ) : ℂ :=
  riemannZeta β

/-- A scalar readout named by the temperature parameter. -/
noncomputable def kmsState (β : ℂ) : ℂ :=
  partitionFunction β

/-- Reference parameter used by the readout. -/
def criticalBeta : ℂ := 1

/-- Definitional readout of the chosen value at `β = 1`. -/
theorem kmsState_critical : kmsState criticalBeta = riemannZeta 1 := rfl

/-- A cyclic representation has a preimage observable for every state vector,
by the `cyclic` field. -/
theorem cyclic_vacuum_representation_exists
    (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H]
    (rep : GNSRepresentation A H) (state_vector : H) :
    ∃ (observable : A), rep.pi observable rep.vacuum = state_vector := by
  exact rep.cyclic state_vector

/-- Evaluate an observable on the cyclic vacuum vector. -/
noncomputable def evaluateObservableVacuum
    (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H]
    (rep : GNSRepresentation A H) (obs : A) : H :=
  rep.pi obs rep.vacuum

end InfoGeometry.Physics.BostConnes
