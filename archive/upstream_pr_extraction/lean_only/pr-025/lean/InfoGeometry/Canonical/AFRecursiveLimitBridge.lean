import InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-!
# AF-style algebraic direct-limit input

`AFRecursiveLimitPacket` is the actual finite-stage cone data required to use
the repository's algebraic direct-limit owner.  Universal factorization,
stage-image constancy, and stage readback are imported from
`CategoricalRecursiveClosureBridge`; this module does not duplicate them.
-/

noncomputable section

namespace InfoGeometry.Canonical.AFRecursiveLimitBridge

open InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]
variable {Limit : Type u} [Semiring Limit]

/-- One-step bonds and a compatible cone into a direct-limit target. -/
structure AFRecursiveLimitPacket where
  bond : ∀ n : Nat, Stage n →+* Stage (n + 1)
  toLimit : ∀ n : Nat, Stage n →+* Limit
  hcone : ConeCompatible bond toLimit

namespace AFRecursiveLimitPacket

variable (P : AFRecursiveLimitPacket (Stage := Stage) (Limit := Limit))

/-- Idempotence is preserved by the canonical cone map. -/
theorem readback_idempotent
    (n : Nat) (p : Stage n)
    (hp : p * p = p) :
    directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n p) *
        directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n p) =
      directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n p) := by
  simpa [map_mul] using congrArg (P.toLimit n) hp

/-- Square-zero data is preserved by the canonical cone map. -/
theorem readback_squareZero
    (n : Nat) (q : Stage n)
    (hq : q * q = 0) :
    directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n q) *
        directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n q) = 0 := by
  simpa [map_mul] using congrArg (P.toLimit n) hq

end AFRecursiveLimitPacket

end InfoGeometry.Canonical.AFRecursiveLimitBridge
