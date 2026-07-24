import InfoGeometry.Clifford.MatToCantorOperator
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.RealCantorOpLimit

open InfoGeometry.Clifford.MatToCantorOperator
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

abbrev Stage (n : ℕ) : Type := RealCantorOp n

/-- One-step bonding maps for the Cantor operator tower. -/
abbrev stageBond : ∀ n : ℕ, Stage n →+* Stage (n + 1) :=
  fun n => (cantorOpEmbed n).toRingHom

abbrev Limit : Type :=
  DirectLimitSuperClosure (Stage := Stage) stageBond

def ofStage (n : ℕ) : Stage n →+* Limit :=
  directLimitOf (Stage := Stage) stageBond n

/-- The base-ring action on the direct limit induced by the stage-0 embedding. -/
noncomputable def realAlgebraMap : ℝ →+* Limit :=
  (ofStage 0).comp (algebraMap ℝ (Stage 0))

/-- The scalar embedding is independent of the finite representative stage. -/
@[simp] theorem realAlgebraMap_stage (n : ℕ) (r : ℝ) :
    realAlgebraMap r = ofStage n (algebraMap ℝ (Stage n) r) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        realAlgebraMap r = ofStage n (algebraMap ℝ (Stage n) r) := ih
        _ = ofStage (n + 1) (cantorOpEmbed n (algebraMap ℝ (Stage n) r)) := by
              symm
              exact directLimitOf_bond (Stage := Stage) stageBond n (algebraMap ℝ (Stage n) r)
        _ = ofStage (n + 1) (algebraMap ℝ (Stage (n + 1)) r) := by
              rw [← AlgHom.commutes (cantorOpEmbed n) r]

noncomputable instance : Algebra ℝ Limit :=
  RingHom.toAlgebra' realAlgebraMap (by
    intro r x
    induction x using DirectLimit.induction with
    | _ n x =>
        rw [realAlgebraMap_stage]
        simpa using congrArg (ofStage n) (Algebra.commutes r x))

end InfoGeometry.Clifford.RealCantorOpLimit
