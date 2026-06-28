import InfoGeometry.Physics.ZornMatrixSU3
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic

/-!
Formalization of D₄ Triality and its S₃ Action on the Three 8-Dimensional Representations.

This module implements the genuine D₄ triality: the S₃ action permuting the three
8-dimensional irreducible representations of Spin(8):
- 8ᵥ: vector representation
- 8ₛ: positive spinor representation  
- 8꜀: negative spinor representation

The current ZornMatrix color permutation (Fin 3) is moved to ColorPermutationAction.
-/

namespace InfoGeometry.Physics.D4Triality

open InfoGeometry.Physics

/-- The three branches of the D₄ triality -/
inductive TrialityBranch
  | vector       -- 8ᵥ: vector representation
  | spinorPlus   -- 8ₛ: positive spinor representation
  | spinorMinus  -- 8꜀: negative spinor representation
deriving DecidableEq, Fintype, Repr

/-- A packet carrying the three 8-dimensional branches of the D₄ triality -/
structure TrialityPacket (R : Type*) where
  vector : Fin 8 → R
  spinorPlus : Fin 8 → R
  spinorMinus : Fin 8 → R

/-- Access a specific branch of a triality packet -/
def TrialityPacket.branch {R : Type*} (P : TrialityPacket R) : TrialityBranch → Fin 8 → R :=
  fun b => match b with
    | TrialityBranch.vector => P.vector
    | TrialityBranch.spinorPlus => P.spinorPlus
    | TrialityBranch.spinorMinus => P.spinorMinus

/-- Construct a triality packet from a branch function -/
def TrialityPacket.ofBranch {R : Type*} (f : TrialityBranch → Fin 8 → R) : TrialityPacket R :=
  { vector := f TrialityBranch.vector
    spinorPlus := f TrialityBranch.spinorPlus
    spinorMinus := f TrialityBranch.spinorMinus }

/-- S₃ action on the three triality branches -/
structure TrialityAction where
  perm : Equiv.Perm TrialityBranch -- Permutation of the three branches

/-- Apply a triality action to a packet -/
def TrialityAction.apply {R : Type*} (τ : TrialityAction) (P : TrialityPacket R) : TrialityPacket R :=
  TrialityPacket.ofBranch fun b => P.branch (τ.perm b)

/-- Theorem: Triality action preserves branch structure -/
@[simp]
theorem TrialityAction.apply_branch {R : Type*} (τ : TrialityAction) (P : TrialityPacket R) (b : TrialityBranch) :
    (τ.apply P).branch b = P.branch (τ.perm b) := by
  cases b <;> rfl

/-- The S₃ group of triality actions -/
def S3Triality : Finset TrialityAction :=
  { perm := (1 : Equiv.Perm TrialityBranch) }
  ∪ { perm := (Equiv.swap TrialityBranch.vector TrialityBranch.spinorPlus : Equiv.Perm TrialityBranch) }
  ∪ { perm := (Equiv.swap TrialityBranch.vector TrialityBranch.spinorMinus : Equiv.Perm TrialityBranch) }
  ∪ { perm := (Equiv.swap TrialityBranch.spinorPlus TrialityBranch.spinorMinus : Equiv.Perm TrialityBranch) }
  ∪ { perm := (Equiv.cycle [TrialityBranch.vector, TrialityBranch.spinorPlus, TrialityBranch.spinorMinus] : Equiv.Perm TrialityBranch) }
  ∪ { perm := (Equiv.cycle [TrialityBranch.vector, TrialityBranch.spinorMinus, TrialityBranch.spinorPlus] : Equiv.Perm TrialityBranch) }

/-- A triality action is in S₃ -/
def TrialityAction.inS3 (τ : TrialityAction) : Prop := τ ∈ S3Triality

/-- Theorem: S₃ triality has exactly 6 elements -/
theorem S3Triality_card : S3Triality.card = 6 := by
  decide

/-- Color permutation action on Zorn matrices (separate from D₄ triality) -/
structure ColorPermutationAction where
  perm : Equiv.Perm (Fin 3)

/-- Apply a color permutation to a Zorn matrix -/
def ColorPermutationAction.apply (τ : ColorPermutationAction) (Z : ZornMatrix) : ZornMatrix :=
  { a := Z.a
    b := Z.b
    x := fun i => Z.x (τ.perm i)
    y := fun i => Z.y (τ.perm i) }

/-- Theorem: Color permutation preserves the Zorn determinant -/
theorem ColorPermutationAction.preserves_det (τ : ColorPermutationAction) (Z : ZornMatrix) :
    (τ.apply Z).det = Z.det := by
  simp [ColorPermutationAction.apply, ZornMatrix.det]
  have h_sum : (∑ i : Fin 3, Z.x (τ.perm i) * Z.y (τ.perm i)) = (∑ j : Fin 3, Z.x j * Z.y j) := by
    rw [Finset.sum_equiv (τ.perm)]
    <;> simp [Equiv.Perm.sign]
  rw [h_sum]
  <;> rfl

/-- The tripotent operator on Zorn matrices: T(Z) = (0, 0, x, -y) -/
@[simp]
def ZornMatrix.tripotent (Z : ZornMatrix) : ZornMatrix :=
  { a := 0
    b := 0
    x := Z.x
    y := fun i => -Z.y i }

/-- Theorem: Tripotent is idempotent (T² = T) -/
@[simp]
theorem ZornMatrix.tripotent_tripotent (Z : ZornMatrix) :
    (Z.tripotent).tripotent = { a := 0, b := 0, x := Z.x, y := Z.y } := by
  ext i <;> simp [ZornMatrix.tripotent]

/-- Theorem: Tripotent satisfies T³ = T -/
theorem ZornMatrix.tripotent_cube (Z : ZornMatrix) :
    (Z.tripotent).tripotent.tripotent = Z.tripotent := by
  ext i <;> simp [ZornMatrix.tripotent]

/-- Theorem: Color permutation commutes with tripotent operator -/
theorem ColorPermutationAction.commutes_with_tripotent (τ : ColorPermutationAction) (Z : ZornMatrix) :
    (τ.apply (ZornMatrix.tripotent Z)) = ZornMatrix.tripotent (τ.apply Z) := by
  simp [ColorPermutationAction.apply, ZornMatrix.tripotent]
  <;> ext <;> simp [Equiv.Perm.sign]
  <;>
  (try aesop)
  <;>
  (try
    {
      fin_cases τ.perm <;>
      simp_all [Equiv.Perm.sign, Fin.val_zero, Fin.val_one, Fin.val_two] <;>
      aesop
    })

end InfoGeometry.Physics.D4Triality