import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Algebra.Basic

/-!
# Bost-Connes partition readout and cyclic GNS carrier

This file packages a formal partition-function readout together with a
minimal cyclic GNS representation carrier.  It does not prove a KMS boundary
theorem or any critical-temperature representation classification.
-/

namespace InfoGeometry.Physics.BostConnes

namespace Legacy

open Complex

/--
The algebraic carrier used by this finite readout owner.

The existing Mathlib `Algebra ℂ A` instance is the complete content here;
this alias does not claim a C*-completion or a Bost--Connes dynamical system.
-/
abbrev BostConnesAlgebra (A : Type*) [Ring A] [Algebra ℂ A] := Algebra ℂ A

/-- The Gelfand-Naimark-Segal (GNS) representation mapping for a state. -/
structure GNSRepresentation (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H] where
  pi : A →ₐ[ℂ] (H →ₗ[ℂ] H)
  vacuum : H
  cyclic : ∀ h : H, ∃ a : A, pi a vacuum = h

/-- The formal partition-function readout. -/
noncomputable def partitionFunction (β : ℂ) : ℂ :=
  riemannZeta β

/-- A scalar readout obtained from the partition-function term. -/
noncomputable def kmsState (β : ℂ) : ℂ :=
  partitionFunction β

/-- The formal critical-point parameter. -/
def criticalBeta : ℂ := 1

/-- Cyclicity of the supplied GNS representation carrier. -/
theorem cyclic_vacuum_representation_exists
    (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H]
    (rep : GNSRepresentation A H) (state_vector : H) :
    ∃ (observable : A), rep.pi observable rep.vacuum = state_vector := by
  exact rep.cyclic state_vector

/-- Evaluation of an observable on the cyclic vacuum carrier. -/
noncomputable def evaluateObservableVacuum
    (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H]
    (rep : GNSRepresentation A H) (obs : A) : H :=
  rep.pi obs rep.vacuum

end Legacy

end InfoGeometry.Physics.BostConnes
