import InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
import InfoGeometry.Canonical.FiniteInvariantTransport

/-!
# InfoGeometry.Canonical.AFRecursiveLimitBridge

Finite-to-limit algebraic bridge for the inductive/AQFT-style tower.

This file packages the already owned direct-limit skeleton in a form that
matches the finite-stage/compatible-cone/universal-factorization vocabulary
used throughout the repository.

The safe content here is deliberately narrow:

* a stagewise semiring tower with one-step bonding maps;
* a compatible cone into a target semiring;
* stage-image constancy along the tower;
* universal factorization through the direct limit;
* readback of the canonical finite-stage image;
* preservation of idempotent and square-zero stage data under the canonical
  direct-limit maps.

No AF-algebra classification theorem.
No Haag--Kastler net construction.
No von Neumann factor theorem.
-/

noncomputable section

namespace AFRecursiveLimitBridge

open InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.FiniteInvariantTransport

universe u

section Tower

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]
variable {Limit : Type u} [Semiring Limit]

/-- An AF-style finite tower: one-step bonds plus a compatible cone to a target. -/
structure AFRecursiveLimitPacket where
  /-- One-step bonding maps between finite stages. -/
  bond : ∀ n : Nat, Stage n →+* Stage (n + 1)
  /-- Cone of stage maps into the target algebra. -/
  toLimit : ∀ n : Nat, Stage n →+* Limit
  /-- Compatibility of the cone with the one-step bonds. -/
  hcone : ConeCompatible bond toLimit

namespace AFRecursiveLimitPacket

variable (P : AFRecursiveLimitPacket (Stage := Stage) (Limit := Limit))

/-- The stage-image is constant along the compatible AF tower. -/
theorem stageImage_constant
    (F : ∀ n : Nat, Stage n)
    (hF : ∀ n, P.bond n (F n) = F (n + 1)) :
    ∀ n : Nat, P.toLimit n (F n) = P.toLimit 0 (F 0) :=
  cone_stageImage_constant (Stage := Stage) (Limit := Limit)
    P.bond P.toLimit P.hcone F hF

/-- The universal factorization through the direct limit is unique. -/
theorem factorization_unique
    (g : DirectLimitSuperClosure P.bond →+* Limit)
    (hg : ∀ n : Nat, g.comp (directLimitOf P.bond n) = P.toLimit n) :
    g = directLimitLift P.bond P.toLimit P.hcone :=
  directLimit_factorization_unique (Stage := Stage) (Limit := Limit)
    P.bond P.toLimit P.hcone g hg

/-- The canonical finite-stage image is recovered by the direct-limit readback. -/
theorem readback (n : Nat) (x : Stage n) :
    directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n x) =
      P.toLimit n x :=
  directLimit_readback (Stage := Stage) (Limit := Limit)
    P.bond P.toLimit P.hcone n x

/-- The direct-limit lift agrees with the cone on the canonical finite images. -/
theorem lift_agrees_on_stages (n : Nat) (x : Stage n) :
    directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n x) =
      P.toLimit n x :=
  P.readback n x

/-- Idempotent finite-stage data remain idempotent after canonical readback. -/
theorem readback_idempotent
    (n : Nat) (p : Stage n)
    (hp : p * p = p) :
    directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n p) *
        directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n p) =
      directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n p) := by
  simpa [map_mul] using congrArg (P.toLimit n) hp

/-- Square-zero finite-stage data remain square-zero after canonical readback. -/
theorem readback_squareZero
    (n : Nat) (q : Stage n)
    (hq : q * q = 0) :
    directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n q) *
        directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n q) = 0 := by
  simpa [map_mul] using congrArg (P.toLimit n) hq

end AFRecursiveLimitPacket

/-- A bare alias for the compatibility predicate used by the AF-style packet. -/
abbrev CompatibleCone
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit) : Prop :=
  ConeCompatible (Stage := Stage) (Limit := Limit) bond toLimit

/-- The stage-image constancy theorem in direct-limit form. -/
theorem stageImage_constant
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : CompatibleCone (Stage := Stage) (Limit := Limit) bond toLimit)
    (F : ∀ n : Nat, Stage n)
    (hF : ∀ n, bond n (F n) = F (n + 1)) :
    ∀ n : Nat, toLimit n (F n) = toLimit 0 (F 0) :=
  cone_stageImage_constant (Stage := Stage) (Limit := Limit)
    bond toLimit hcone F hF

/-- The universal factorization theorem in direct-limit form. -/
theorem factorization_unique
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : CompatibleCone (Stage := Stage) (Limit := Limit) bond toLimit)
    (g : DirectLimitSuperClosure bond →+* Limit)
    (hg : ∀ n : Nat, g.comp (directLimitOf bond n) = toLimit n) :
    g = directLimitLift bond toLimit hcone :=
  directLimit_factorization_unique (Stage := Stage) (Limit := Limit)
    bond toLimit hcone g hg

/-- The direct-limit readback theorem in direct-limit form. -/
theorem readback
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : CompatibleCone (Stage := Stage) (Limit := Limit) bond toLimit)
    (n : Nat) (x : Stage n) :
    directLimitLift bond toLimit hcone (directLimitOf bond n x) = toLimit n x :=
  directLimit_readback (Stage := Stage) (Limit := Limit)
    bond toLimit hcone n x

end Tower

end AFRecursiveLimitBridge
