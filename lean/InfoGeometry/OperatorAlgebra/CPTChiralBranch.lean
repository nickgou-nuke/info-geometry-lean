/-
InfoGeometry/OperatorAlgebra/CPTChiralBranch.lean

CPT branch of the modular chiral mirror.

This module packages the sign branch where Tomita modular conjugation also acts
as CPT: it mirrors the algebra into the commutant and flips chirality.

The key relation is

  Jχ = -χJ.

Consequently, the left and right chiral projectors are exchanged by the
modular/CPT mirror.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.TomitaCartanSplit
import InfoGeometry.OperatorAlgebra.ModularChiralMirror

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CPTChiralBranch

open InfoGeometry.OperatorAlgebra.TomitaCartanSplit
open InfoGeometry.OperatorAlgebra.ModularChiralMirror

/-! ## 1. CPT Tomita/chiral branch -/

/--
CPT algebraic branch of the modular chiral mirror.

`tomita` records the algebra/commutant mirror.

`mirror` records the chiral-flipping relation `Jχ = -χJ`.

`tomitaMirror_eq_J_conj` identifies the abstract Tomita mirror with
conjugation by the same operator `J`.

Representation-specific physical calibration belongs in the concrete owner
file that proves it; this structure only carries the algebraic data used below.
-/
structure CPTChiralTomitaBranch
    (Op : Type*) [Ring Op] [Algebra ℝ Op] where
  /-- Algebra/commutant Tomita routing. -/
  tomita : TomitaAlgebraPair Op

  /-- Chiral-flipping modular mirror datum. -/
  mirror : ModularChiralMirrorDatum Op

  /-- The abstract Tomita mirror is conjugation by `J`. -/
  tomitaMirror_eq_J_conj :
    ∀ x : Op, tomita.Jconj x = (mirror.J * x) * mirror.J

namespace CPTChiralTomitaBranch

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]
variable (B : CPTChiralTomitaBranch Op)

/-- Left chiral support: `P_L x = x`. -/
def LeftSupported
    (x : Op) : Prop :=
  B.mirror.P_left * x = x

/-- Right chiral support: `P_R x = x`. -/
def RightSupported
    (x : Op) : Prop :=
  B.mirror.P_right * x = x

/-- The raw CPT conjugate of an operator. -/
def cptConj
    (x : Op) : Op :=
  (B.mirror.J * x) * B.mirror.J

/-- CPT sends left-supported operators to right-supported operators. -/
theorem cptConj_left_to_right
    {x : Op}
    (hx : B.LeftSupported x) :
    B.RightSupported (B.cptConj x) := by
  dsimp [LeftSupported, RightSupported, cptConj] at hx ⊢
  calc
    B.mirror.P_right * ((B.mirror.J * x) * B.mirror.J)
        = ((B.mirror.P_right * B.mirror.J) * x) * B.mirror.J := by
            rw [← mul_assoc, ← mul_assoc]
    _ = ((B.mirror.J * B.mirror.P_left) * x) * B.mirror.J := by
            rw [← B.mirror.J_mul_P_left]
    _ = (B.mirror.J * (B.mirror.P_left * x)) * B.mirror.J := by
            rw [mul_assoc B.mirror.J B.mirror.P_left x]
    _ = (B.mirror.J * x) * B.mirror.J := by
            rw [hx]

/-- CPT sends right-supported operators to left-supported operators. -/
theorem cptConj_right_to_left
    {x : Op}
    (hx : B.RightSupported x) :
    B.LeftSupported (B.cptConj x) := by
  dsimp [LeftSupported, RightSupported, cptConj] at hx ⊢
  calc
    B.mirror.P_left * ((B.mirror.J * x) * B.mirror.J)
        = ((B.mirror.P_left * B.mirror.J) * x) * B.mirror.J := by
            rw [← mul_assoc, ← mul_assoc]
    _ = ((B.mirror.J * B.mirror.P_right) * x) * B.mirror.J := by
            rw [← B.mirror.J_mul_P_right]
    _ = (B.mirror.J * (B.mirror.P_right * x)) * B.mirror.J := by
            rw [mul_assoc B.mirror.J B.mirror.P_right x]
    _ = (B.mirror.J * x) * B.mirror.J := by
            rw [hx]

/--
If `x` lies on the algebra side and is left-chiral, then its Tomita/CPT mirror
lies on the commutant side and is right-chiral.
-/
theorem algebra_left_to_commutant_right
    {x : Op}
    (hM : x ∈ B.tomita.M)
    (hL : B.LeftSupported x) :
    B.tomita.Jconj x ∈ B.tomita.Mcomm ∧
      B.RightSupported (B.tomita.Jconj x) := by
  constructor
  · exact B.tomita.J_maps_M_to_comm x hM
  · rw [B.tomitaMirror_eq_J_conj x]
    exact B.cptConj_left_to_right hL

/--
If `x` lies on the algebra side and is right-chiral, then its Tomita/CPT mirror
lies on the commutant side and is left-chiral.
-/
theorem algebra_right_to_commutant_left
    {x : Op}
    (hM : x ∈ B.tomita.M)
    (hR : B.RightSupported x) :
    B.tomita.Jconj x ∈ B.tomita.Mcomm ∧
      B.LeftSupported (B.tomita.Jconj x) := by
  constructor
  · exact B.tomita.J_maps_M_to_comm x hM
  · rw [B.tomitaMirror_eq_J_conj x]
    exact B.cptConj_right_to_left hR

end CPTChiralTomitaBranch

/-! ## 2. Owner target -/

/-- Owner target for reading a supplied CPT-calibrated Tomita/chiral branch. -/
def CPTChiralBranchOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℝ Op] : Prop :=
  ∀ B : CPTChiralTomitaBranch Op,
    (∀ x : Op, B.tomita.Jconj x = (B.mirror.J * x) * B.mirror.J) ∧
    (∀ x : Op, x ∈ B.tomita.M → B.LeftSupported x →
      B.tomita.Jconj x ∈ B.tomita.Mcomm ∧
        B.RightSupported (B.tomita.Jconj x)) ∧
    (∀ x : Op, x ∈ B.tomita.M → B.RightSupported x →
      B.tomita.Jconj x ∈ B.tomita.Mcomm ∧
        B.LeftSupported (B.tomita.Jconj x))

/-- A supplied CPT/chiral branch gives the Tomita mirror and chirality swap laws. -/
theorem cptChiralBranchOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℝ Op] :
    CPTChiralBranchOwnerTarget Op := by
  intro B
  exact ⟨
    (fun x => B.tomitaMirror_eq_J_conj x),
    (fun x hM hL => B.algebra_left_to_commutant_right hM hL),
    (fun x hM hR => B.algebra_right_to_commutant_left hM hR)⟩

end InfoGeometry.OperatorAlgebra.CPTChiralBranch
