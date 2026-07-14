import InfoGeometry.Physics.ZornMatrixSU3
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic

/-!
# D₄ triality audit copy
-/

namespace InfoGeometry.Physics.D4Triality_audit

open InfoGeometry.Physics.ZornMatrixSU3

/-- `\{\mathrm{vector},\mathrm{spinorPlus},\mathrm{spinorMinus}\}`. -/
inductive TrialityBranch
  | vector
  | spinorPlus
  | spinorMinus

deriving DecidableEq, Fintype, Repr

/-- `\mathrm{vector}\oplus\mathrm{spinorPlus}\oplus\mathrm{spinorMinus}`. -/
structure TrialityPacket (R : Type*) where
  vector : Fin 8 → R
  spinorPlus : Fin 8 → R
  spinorMinus : Fin 8 → R

def TrialityPacket.branch {R : Type*} (P : TrialityPacket R) : TrialityBranch → Fin 8 → R :=
  fun b => match b with
    | TrialityBranch.vector => P.vector
    | TrialityBranch.spinorPlus => P.spinorPlus
    | TrialityBranch.spinorMinus => P.spinorMinus

def TrialityPacket.ofBranch {R : Type*} (f : TrialityBranch → Fin 8 → R) : TrialityPacket R :=
  { vector := f TrialityBranch.vector
    spinorPlus := f TrialityBranch.spinorPlus
    spinorMinus := f TrialityBranch.spinorMinus }

structure TrialityAction where
  perm : Equiv.Perm TrialityBranch
  deriving DecidableEq, Fintype

def TrialityAction.apply {R : Type*} (τ : TrialityAction) (P : TrialityPacket R) : TrialityPacket R :=
  TrialityPacket.ofBranch fun b => P.branch (τ.perm b)

@[simp]
theorem TrialityAction.apply_branch {R : Type*} (τ : TrialityAction) (P : TrialityPacket R) (b : TrialityBranch) :
    (τ.apply P).branch b = P.branch (τ.perm b) := by
  cases b <;> rfl

def S3Triality : Finset TrialityAction :=
  Finset.univ.image fun σ : Equiv.Perm TrialityBranch => ({ perm := σ } : TrialityAction)

def TrialityAction.inS3 (τ : TrialityAction) : Prop := τ ∈ S3Triality

theorem S3Triality_card : S3Triality.card = 6 := by
  decide

structure ColorPermutationAction where
  perm : Equiv.Perm (Fin 3)

def ColorPermutationAction.apply (τ : ColorPermutationAction) (Z : ZornMatrix) : ZornMatrix :=
  { a := Z.a
    b := Z.b
    x := fun i => Z.x (τ.perm i)
    y := fun i => Z.y (τ.perm i) }

theorem ColorPermutationAction.preserves_norm (τ : ColorPermutationAction) (Z : ZornMatrix) :
    ZornMatrixSU3.norm (τ.apply Z) = ZornMatrixSU3.norm Z := by
  have h_dot :
      ZornMatrixSU3.dotProduct (fun i => Z.x (τ.perm i)) (fun i => Z.y (τ.perm i)) =
        ZornMatrixSU3.dotProduct Z.x Z.y := by
    rw [show
        ZornMatrixSU3.dotProduct (fun i => Z.x (τ.perm i)) (fun i => Z.y (τ.perm i)) =
          ∑ i : Fin 3, Z.x (τ.perm i) * Z.y (τ.perm i) by
        simp [ZornMatrixSU3.dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
          Fin.sum_univ_three]]
    rw [show
        ZornMatrixSU3.dotProduct Z.x Z.y = ∑ i : Fin 3, Z.x i * Z.y i by
        simp [ZornMatrixSU3.dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
          Fin.sum_univ_three]]
    exact Fintype.sum_bijective (fun i : Fin 3 => τ.perm i) τ.perm.bijective
      (fun i : Fin 3 => Z.x (τ.perm i) * Z.y (τ.perm i))
      (fun i : Fin 3 => Z.x i * Z.y i)
      (fun _ => rfl)
  simp [ColorPermutationAction.apply, ZornMatrixSU3.norm, h_dot]

@[simp]
def tripotent (Z : ZornMatrix) : ZornMatrix :=
  { a := (0 : ℝ)
    b := (0 : ℝ)
    x := Z.x
    y := fun i => -Z.y i }

@[simp]
theorem tripotent_tripotent (Z : ZornMatrix) :
    tripotent (tripotent Z) = { a := (0 : ℝ), b := (0 : ℝ), x := Z.x, y := Z.y } := by
  ext i <;> simp [tripotent]

theorem tripotent_cube (Z : ZornMatrix) :
    tripotent (tripotent (tripotent Z)) = tripotent Z := by
  ext i <;> simp [tripotent]

theorem ColorPermutationAction.commutes_with_tripotent (τ : ColorPermutationAction) (Z : ZornMatrix) :
    ColorPermutationAction.apply τ (tripotent Z) = tripotent (ColorPermutationAction.apply τ Z) := by
  simp [ColorPermutationAction.apply, tripotent]

#print axioms InfoGeometry.Physics.D4Triality_audit.TrialityPacket.branch
#print axioms InfoGeometry.Physics.D4Triality_audit.TrialityPacket.ofBranch
#print axioms InfoGeometry.Physics.D4Triality_audit.TrialityAction.apply
#print axioms InfoGeometry.Physics.D4Triality_audit.TrialityAction.apply_branch
#print axioms InfoGeometry.Physics.D4Triality_audit.S3Triality_card
#print axioms InfoGeometry.Physics.D4Triality_audit.ColorPermutationAction.apply
#print axioms InfoGeometry.Physics.D4Triality_audit.ColorPermutationAction.preserves_norm
#print axioms InfoGeometry.Physics.D4Triality_audit.tripotent
#print axioms InfoGeometry.Physics.D4Triality_audit.tripotent_tripotent
#print axioms InfoGeometry.Physics.D4Triality_audit.tripotent_cube
#print axioms InfoGeometry.Physics.D4Triality_audit.ColorPermutationAction.commutes_with_tripotent

end InfoGeometry.Physics.D4Triality_audit
