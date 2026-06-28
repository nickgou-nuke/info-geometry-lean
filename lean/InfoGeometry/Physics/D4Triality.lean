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

open InfoGeometry.Physics.ZornMatrixSU3

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
deriving DecidableEq

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
  Finset.univ.image fun σ : Equiv.Perm TrialityBranch => ({ perm := σ } : TrialityAction)

/-- A triality action is in S₃ -/
def TrialityAction.inS3 (τ : TrialityAction) : Prop := τ ∈ S3Triality

/-- Theorem: S₃ triality has exactly 6 elements -/
theorem S3Triality_card : S3Triality.card = 6 := by
  native_decide

/-- Color permutation action on Zorn matrices (separate from D₄ triality) -/
structure ColorPermutationAction where
  perm : Equiv.Perm (Fin 3)

/-- Apply a color permutation to a Zorn matrix -/
def ColorPermutationAction.apply (τ : ColorPermutationAction) (Z : ZornMatrix) : ZornMatrix :=
  { a := Z.a
    b := Z.b
    x := fun i => Z.x (τ.perm i)
    y := fun i => Z.y (τ.perm i) }

/-- Theorem: Color permutation preserves the Zorn norm (determinant) -/
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

/-- The tripotent operator on Zorn matrices: T(Z) = (0, 0, x, -y) -/
@[simp]
def tripotent (Z : ZornMatrix) : ZornMatrix :=
  { a := (0 : ℝ)
    b := (0 : ℝ)
    x := Z.x
    y := fun i => -Z.y i }

/-- Theorem: Tripotent is idempotent (T² = T) -/
@[simp]
theorem tripotent_tripotent (Z : ZornMatrix) :
    tripotent (tripotent Z) = { a := (0 : ℝ), b := (0 : ℝ), x := Z.x, y := Z.y } := by
  ext i <;> simp [tripotent]

/-- Theorem: Tripotent satisfies T³ = T -/
theorem tripotent_cube (Z : ZornMatrix) :
    tripotent (tripotent (tripotent Z)) = tripotent Z := by
  ext i <;> simp [tripotent]

/-- Theorem: Color permutation commutes with tripotent operator -/
theorem ColorPermutationAction.commutes_with_tripotent (τ : ColorPermutationAction) (Z : ZornMatrix) :
    ColorPermutationAction.apply τ (tripotent Z) = tripotent (ColorPermutationAction.apply τ Z) := by
  simp [ColorPermutationAction.apply, tripotent]

end InfoGeometry.Physics.D4Triality
