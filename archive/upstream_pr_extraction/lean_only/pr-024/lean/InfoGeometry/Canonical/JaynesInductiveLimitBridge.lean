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
    InfoGeometry.Canonical.AFRecursiveLimitBridge.CompatibleCone
      (Stage := Stage) (Limit := Limit) tower.bond entropy

namespace JaynesInductivePacket

variable (P : JaynesInductivePacket (Stage := Stage) (Limit := Limit))

/-- The entropy readout factors uniquely through the direct limit. -/
theorem entropy_factorization_unique
    (g : DirectLimitSuperClosure P.tower.bond →+* Limit)
    (hg : ∀ n : Nat, g.comp (directLimitOf P.tower.bond n) = P.entropy n) :
    g = directLimitLift P.tower.bond P.entropy P.hEntropy :=
  InfoGeometry.Canonical.AFRecursiveLimitBridge.factorization_unique
    (Stage := Stage) (Limit := Limit)
    (bond := P.tower.bond) (toLimit := P.entropy) (hcone := P.hEntropy) (g := g) (hg := hg)

/-- The canonical readback of a finite Jaynes stage. -/
theorem entropy_readback (n : Nat) (x : Stage n) :
    directLimitLift P.tower.bond P.entropy P.hEntropy
        (directLimitOf P.tower.bond n x) =
      P.entropy n x :=
  InfoGeometry.Canonical.AFRecursiveLimitBridge.readback
    (Stage := Stage) (Limit := Limit)
    (bond := P.tower.bond) (toLimit := P.entropy) (hcone := P.hEntropy) n x

/-- The entropy readout is constant along a compatible finite tower. -/
theorem entropy_stage_constant
    (F : ∀ n : Nat, Stage n)
    (hF : ∀ n : Nat, P.tower.bond n (F n) = F (n + 1)) :
    ∀ n : Nat, P.entropy n (F n) = P.entropy 0 (F 0) :=
  InfoGeometry.Canonical.AFRecursiveLimitBridge.stageImage_constant
    (Stage := Stage) (Limit := Limit)
    (bond := P.tower.bond) (toLimit := P.entropy) (hcone := P.hEntropy)
    F hF

end JaynesInductivePacket

end Tower

end InfoGeometry.Canonical.JaynesInductiveLimitBridge
