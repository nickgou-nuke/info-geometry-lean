import InfoGeometry.Canonical.AFRecursiveLimitBridge
import InfoGeometry.MaxEnt.Finite

/-!
# InfoGeometry.Canonical.JaynesInductiveLimitBridge

Finite-stage Jaynes/MaxEnt data packaged as an inductive-limit tower.

The intended reading is the one the user requested:

* finite measurement stages are the primitive objects;
* the large-number limit is handled by compatible cones and a direct limit;
* entropy-like readouts are transported stagewise and then read back from the
  universal factorization.

This file does not claim an analytic continuum limit, a hyperfinite factor, or
any completeness theorem. It records the algebraic inductive skeleton only.
-/

noncomputable section

namespace InfoGeometry.Canonical.JaynesInductiveLimitBridge

open InfoGeometry.Canonical.AFRecursiveLimitBridge
open InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u

section Tower

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]
variable {Limit : Type u} [Semiring Limit]

/--
Jaynes-style finite inductive packet:

* a stagewise semiring tower;
* a compatible direct-limit tower;
* an entropy-like cone of stage readouts into the same target;
* compatibility of the readout with the one-step bonds.

The entropy readout is intentionally algebraic: it is the transportable
finite-stage invariant that survives the inductive system.
-/
structure JaynesInductivePacket where
  /-- Underlying finite-stage/direct-limit tower. -/
  tower : AFRecursiveLimitPacket (Stage := Stage) (Limit := Limit)
  /-- Entropy-like stagewise readout into the target semiring. -/
  entropy : ∀ n : Nat, Stage n →+* Limit
  /-- Compatibility of the entropy readout with the stage bonds. -/
  hEntropy :
    InfoGeometry.Canonical.CategoricalRecursiveClosureBridge.ConeCompatible
      (Stage := Stage) (Limit := Limit) tower.bond entropy


end Tower

end InfoGeometry.Canonical.JaynesInductiveLimitBridge
