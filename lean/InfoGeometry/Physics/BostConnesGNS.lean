import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Algebra.Basic

/-!
# Bost-Connes/GNS carrier interface

This file contains a small abstract GNS representation record and a zeta-valued
partition readout.  It does not construct the Bost--Connes C*-dynamical system
or prove a phase-transition theorem.
-/

namespace InfoGeometry.Physics.BostConnes

open Complex

/-- The abstract C*-algebra analog for the Bost-Connes system. -/
class BostConnesAlgebra (A : Type*) [Ring A] [Algebra ℂ A]

/-- The Gelfand-Naimark-Segal (GNS) representation mapping for a state. -/
structure GNSRepresentation (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H] where
  pi : A →ₐ[ℂ] (H →ₗ[ℂ] H)
  vacuum : H
  cyclic : ∀ h : H, ∃ a : A, pi a vacuum = h

/-- The Bost-Connes partition function mapping to the Riemann Zeta function. -/
noncomputable def partitionFunction (β : ℂ) : ℂ :=
  riemannZeta β

/-- The abstract KMS state functional parameterized by inverse temperature β. -/
noncomputable def kmsState (β : ℂ) : ℂ :=
  partitionFunction β

/-- The critical inverse temperature where the phase transition occurs. -/
def criticalBeta : ℂ := 1

/-- Definitional readout of the chosen value at `β = 1`. -/
theorem kmsState_critical : kmsState criticalBeta = riemannZeta 1 := rfl

/-- A cyclic representation has a preimage observable for every state vector,
by the `cyclic` field. -/
theorem kms_yields_cyclic_vacuum_representation
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
