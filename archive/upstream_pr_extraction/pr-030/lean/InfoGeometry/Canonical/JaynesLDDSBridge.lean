import InfoGeometry.Canonical.AFRecursiveLimitBridge

/-!
# InfoGeometry.Canonical.JaynesLDDSBridge

Jaynes-style limiting density of discrete states (LDDS) as an algebraic
inductive-limit skeleton.

The safe content here is the centered-density pattern:

* a finite-stage tower of algebras;
* a compatible density tower;
* the centered fluctuation `Δ - 1`;
* readback of the centered fluctuation through the direct limit;
* stagewise constancy along a compatible tower.

This is deliberately finite/algebraic.  It does not claim a measure-theoretic
continuous entropy theorem or a hyperfinite completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.JaynesLDDSBridge

open InfoGeometry.Canonical.AFRecursiveLimitBridge
open InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u

section Tower

variable {Stage : Nat → Type u}
variable [∀ n : Nat, Ring (Stage n)]
variable {Limit : Type u}
variable [Ring Limit]

/--
Jaynes LDDS packet:

* `tower` is the finite-stage/direct-limit skeleton;
* `density` is the local density operator/state at each stage;
* `hDensity` is the compatibility condition along the tower.

The centered score is the algebraic fluctuation `Δ - 1`.
-/
structure JaynesLDDSPacket where
  tower : AFRecursiveLimitPacket (Stage := Stage) (Limit := Limit)
  density : ∀ n : Nat, Stage n
  hDensity : ∀ n : Nat, tower.bond n (density n) = density (n + 1)

namespace JaynesLDDSPacket

variable (P : JaynesLDDSPacket (Stage := Stage) (Limit := Limit))

/-- The local centered density fluctuation `Δ_n - 1`. -/
def centeredScore (n : Nat) : Stage n :=
  P.density n - 1

@[simp] theorem centeredScore_def (n : Nat) :
    P.centeredScore n = P.density n - 1 := rfl

/-- The centered score is sent to the centered score in the direct limit. -/
theorem centeredScore_readback (n : Nat) :
    directLimitLift P.tower.bond P.tower.toLimit P.tower.hcone
        (directLimitOf P.tower.bond n (P.centeredScore n)) =
      P.tower.toLimit n (P.density n) - 1 := by
  calc
    directLimitLift P.tower.bond P.tower.toLimit P.tower.hcone
        (directLimitOf P.tower.bond n (P.centeredScore n))
        =
      directLimitLift P.tower.bond P.tower.toLimit P.tower.hcone
          (directLimitOf P.tower.bond n (P.density n)) -
        directLimitLift P.tower.bond P.tower.toLimit P.tower.hcone
          (directLimitOf P.tower.bond n (1 : Stage n)) := by
            simp [centeredScore, map_sub]
    _ = P.tower.toLimit n (P.density n) - 1 := by
          rw [directLimit_readback P.tower.bond P.tower.toLimit P.tower.hcone n (P.density n)]
          rw [directLimit_readback P.tower.bond P.tower.toLimit P.tower.hcone n (1 : Stage n)]
          simp

/-- The tower image of the density is constant along compatible stages. -/
theorem density_stage_constant
    (F : ∀ n : Nat, Stage n)
    (hF : ∀ n : Nat, P.tower.bond n (F n) = F (n + 1)) :
    ∀ n : Nat, P.tower.toLimit n (F n) = P.tower.toLimit 0 (F 0) :=
  cone_stageImage_constant (Stage := Stage) (Limit := Limit)
    P.tower.bond P.tower.toLimit P.tower.hcone F hF

/-- The density tower readback is the same at every compatible stage. -/
theorem density_readback (n : Nat) :
    directLimitLift P.tower.bond P.tower.toLimit P.tower.hcone
        (directLimitOf P.tower.bond n (P.density n)) =
      P.tower.toLimit n (P.density n) :=
  directLimit_readback P.tower.bond P.tower.toLimit P.tower.hcone n (P.density n)

/-- The centered score is compatible with the identity reference state. -/
theorem centeredScore_compatibility (n : Nat) :
    P.tower.bond n (P.centeredScore n) = P.centeredScore (n + 1) := by
  simp [centeredScore, P.hDensity n, map_sub]

end JaynesLDDSPacket

end Tower

end InfoGeometry.Canonical.JaynesLDDSBridge
