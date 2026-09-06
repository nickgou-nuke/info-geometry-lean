import InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
import InfoGeometry.Canonical.AFRecursiveLimitBridge
import InfoGeometry.Canonical.JaynesInductiveLimitBridge
import InfoGeometry.Canonical.JaynesLDDSBridge

/-!
# InfoGeometry.Canonical.JaynesCategoricalFormalism

Jaynes formalism through the category-language finite-to-limit lane.

This file packages the existing direct-limit spine already owned in the repo:

* compatible cones of finite-stage readouts;
* universal factorization through the algebraic direct limit;
* stage-image constancy along transported towers;
* centered-score readback for the LDDS bridge.

No analytic completion is claimed here.
-/

namespace InfoGeometry.Canonical.JaynesCategoricalFormalism

open InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

export InfoGeometry.Canonical.CategoricalRecursiveClosureBridge (ConeCompatible)
export InfoGeometry.Canonical.AFRecursiveLimitBridge (
  AFRecursiveLimitPacket
  stageImage_constant
  factorization_unique
  readback
)
export InfoGeometry.Canonical.JaynesInductiveLimitBridge (JaynesInductivePacket)
export InfoGeometry.Canonical.JaynesLDDSBridge (JaynesLDDSPacket)

universe u

section Tower

variable {Stage : Nat → Type u} [∀ n : Nat, Ring (Stage n)]
variable {Limit : Type u} [Ring Limit]

/-! ## Jaynes inductive packet aliases -/

/-- Stage-image constancy for the Jaynes entropy tower. -/
theorem entropy_stage_constant
    (P : JaynesInductivePacket (Stage := Stage) (Limit := Limit))
    (F : ∀ n : Nat, Stage n)
    (hF : ∀ n : Nat, P.tower.bond n (F n) = F (n + 1)) :
    ∀ n : Nat, P.entropy n (F n) = P.entropy 0 (F 0) :=
  InfoGeometry.Canonical.JaynesInductiveLimitBridge.JaynesInductivePacket.entropy_stage_constant
    (P := P) F hF

/-- Unique factorization of the Jaynes entropy cone through the direct limit. -/
theorem entropy_factorization_unique
    (P : JaynesInductivePacket (Stage := Stage) (Limit := Limit))
    (g : DirectLimitSuperClosure P.tower.bond →+* Limit)
    (hg : ∀ n : Nat, g.comp (directLimitOf P.tower.bond n) = P.entropy n) :
    g = directLimitLift P.tower.bond P.entropy P.hEntropy :=
  InfoGeometry.Canonical.JaynesInductiveLimitBridge.JaynesInductivePacket.entropy_factorization_unique
    (P := P) g hg

/-- Canonical readback of a finite Jaynes entropy stage. -/
theorem entropy_readback
    (P : JaynesInductivePacket (Stage := Stage) (Limit := Limit))
    (n : Nat) (x : Stage n) :
    directLimitLift P.tower.bond P.entropy P.hEntropy
        (directLimitOf P.tower.bond n x) =
      P.entropy n x :=
  InfoGeometry.Canonical.JaynesInductiveLimitBridge.JaynesInductivePacket.entropy_readback
    (P := P) n x

/-! ## Jaynes LDDS packet alias -/

/-- Jaynes centered-score readback through the direct limit. -/
theorem centeredScore_readback
    (P : JaynesLDDSPacket (Stage := Stage) (Limit := Limit))
    (n : Nat) :
    directLimitLift P.tower.bond P.tower.toLimit P.tower.hcone
        (directLimitOf P.tower.bond n (P.centeredScore n)) =
      P.tower.toLimit n (P.density n) - 1 :=
  InfoGeometry.Canonical.JaynesLDDSBridge.JaynesLDDSPacket.centeredScore_readback
    (P := P) n

end Tower

end InfoGeometry.Canonical.JaynesCategoricalFormalism
