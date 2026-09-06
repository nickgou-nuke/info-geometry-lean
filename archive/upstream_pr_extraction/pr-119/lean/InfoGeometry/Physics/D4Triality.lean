import InfoGeometry.Physics.ZornMatrixSU3
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic

/-!
# D₄ triality

\[
\mathrm{TrialityBranch} = \{\mathrm{vector},\mathrm{spinorPlus},\mathrm{spinorMinus}\},
\qquad
|S_3|=6.
\]

\[
\mathrm{tripotent}(Z)^3=\mathrm{tripotent}(Z),
\qquad
\mathrm{ColorPermutationAction}(\tau)(Z)\text{ preserves }\|Z\|.
\]

This file records a finite three-branch permutation packet and two exact
matrix readbacks.  It does not assert a classification theorem or a physical
interpretation.
-/

namespace InfoGeometry.Physics.D4Triality

open InfoGeometry.Physics.ZornMatrixSU3

/-- `\{\mathrm{vector},\mathrm{spinorPlus},\mathrm{spinorMinus}\}`. -/
inductive TrialityBranch
  | vector       -- 8ᵥ: vector representation
  | spinorPlus   -- 8ₛ: positive spinor representation
  | spinorMinus  -- 8꜀: negative spinor representation
deriving DecidableEq, Fintype, Repr

/-- `\mathrm{vector}\oplus\mathrm{spinorPlus}\oplus\mathrm{spinorMinus}`. -/
abbrev TrialityPacket (R : Type*) :=
  (Fin 8 → R) × (Fin 8 → R) × (Fin 8 → R)

/-- Compatibility accessor for the vector branch. -/
abbrev TrialityPacket.vector (P : TrialityPacket R) : Fin 8 → R := P.1

/-- Compatibility accessor for the positive-spinor branch. -/
abbrev TrialityPacket.spinorPlus (P : TrialityPacket R) : Fin 8 → R := P.2.1

/-- Compatibility accessor for the negative-spinor branch. -/
abbrev TrialityPacket.spinorMinus (P : TrialityPacket R) : Fin 8 → R := P.2.2

/-- `P\mapsto P_b`. -/
def TrialityPacket.branch {R : Type*} (P : TrialityPacket R) : TrialityBranch → Fin 8 → R :=
  fun b => match b with
    | TrialityBranch.vector => P.vector
    | TrialityBranch.spinorPlus => P.spinorPlus
    | TrialityBranch.spinorMinus => P.spinorMinus

/-- `f\mapsto P_f`. -/
def TrialityPacket.ofBranch {R : Type*} (f : TrialityBranch → Fin 8 → R) : TrialityPacket R :=
  (f TrialityBranch.vector,
    f TrialityBranch.spinorPlus,
    f TrialityBranch.spinorMinus)

/-- `S_3` action on the three branches. -/
abbrev TrialityAction := Equiv.Perm TrialityBranch

/-- Compatibility accessor for the underlying triality permutation. -/
abbrev TrialityAction.perm (τ : TrialityAction) : Equiv.Perm TrialityBranch := τ

/-- `\tau\cdot P`. -/
def TrialityAction.apply {R : Type*} (τ : TrialityAction) (P : TrialityPacket R) : TrialityPacket R :=
  TrialityPacket.ofBranch fun b => P.branch (τ.perm b)

/-- `(\tau\cdot P)_b = P_{\tau(b)}`. -/
@[simp]
theorem TrialityAction.apply_branch {R : Type*} (τ : TrialityAction) (P : TrialityPacket R) (b : TrialityBranch) :
    (τ.apply P).branch b = P.branch (τ.perm b) := by
  cases b <;> rfl

/-- Finite `S_3` triality action set. -/
def S3Triality : Finset TrialityAction :=
  Finset.univ.image (fun σ : Equiv.Perm TrialityBranch => σ)

/-- `\tau\in S_3`. -/
def TrialityAction.inS3 (τ : TrialityAction) : Prop := τ ∈ S3Triality

/-- `|S_3|=6`. -/
theorem S3Triality_card : S3Triality.card = 6 := by
  decide

/-- `\mathrm{Fin}\,3` permutation on Zorn matrices. -/
abbrev ColorPermutationAction := Equiv.Perm (Fin 3)

/-- Compatibility accessor for the underlying color permutation. -/
abbrev ColorPermutationAction.perm (τ : ColorPermutationAction) : Equiv.Perm (Fin 3) := τ

/-- `\tau\cdot Z`. -/
def ColorPermutationAction.apply (τ : ColorPermutationAction) (Z : ZornMatrix) : ZornMatrix :=
  { a := Z.a
    b := Z.b
    x := fun i => Z.x (τ.perm i)
    y := fun i => Z.y (τ.perm i) }

/-- `\|\tau\cdot Z\|=\|Z\|`. -/
theorem ColorPermutationAction.preserves_norm (τ : ColorPermutationAction) (Z : ZornMatrix) :
    InfoGeometry.Physics.ZornMatrixSU3.norm (τ.apply Z) =
      InfoGeometry.Physics.ZornMatrixSU3.norm Z := by
  have h_dot :
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct (fun i => Z.x (τ.perm i)) (fun i => Z.y (τ.perm i)) =
        InfoGeometry.Physics.ZornMatrixSU3.dotProduct Z.x Z.y := by
    rw [show
        InfoGeometry.Physics.ZornMatrixSU3.dotProduct (fun i => Z.x (τ.perm i)) (fun i => Z.y (τ.perm i)) =
          ∑ i : Fin 3, Z.x (τ.perm i) * Z.y (τ.perm i) by
        simp only [InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
          InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
          Fin.sum_univ_three]]
    rw [show
        InfoGeometry.Physics.ZornMatrixSU3.dotProduct Z.x Z.y = ∑ i : Fin 3, Z.x i * Z.y i by
        simp only [InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
          InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
          Fin.sum_univ_three]]
    exact Equiv.sum_comp τ.perm (fun i => Z.x i * Z.y i)
  simp [ColorPermutationAction.apply, InfoGeometry.Physics.ZornMatrixSU3.norm, h_dot]

/-- `T(Z)=(0,0,x,-y)`. -/
@[simp]
def tripotent (Z : ZornMatrix) : ZornMatrix :=
  { a := (0 : ℝ)
    b := (0 : ℝ)
    x := Z.x
    y := fun i => -Z.y i }

/-- `T(T(Z))=T(Z)`. -/
@[simp]
theorem tripotent_tripotent (Z : ZornMatrix) :
    tripotent (tripotent Z) = { a := (0 : ℝ), b := (0 : ℝ), x := Z.x, y := Z.y } := by
  ext i <;> simp [tripotent]

/-- `T^3=T`. -/
theorem tripotent_cube (Z : ZornMatrix) :
    tripotent (tripotent (tripotent Z)) = tripotent Z := by
  ext i <;> simp [tripotent]

/-- `\tau\cdot T(Z)=T(\tau\cdot Z)`. -/
theorem ColorPermutationAction.commutes_with_tripotent (τ : ColorPermutationAction) (Z : ZornMatrix) :
    ColorPermutationAction.apply τ (tripotent Z) = tripotent (ColorPermutationAction.apply τ Z) := by
  simp [ColorPermutationAction.apply, tripotent]

end InfoGeometry.Physics.D4Triality
