/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.BartonSudberyTrialityAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Three-channel triality action

This file packages the already verified component actions on the three tensor
channels into one finite `Fin 3` carrier.  It does not define the
Barton--Sudbery tensor--tensor bracket or claim Jacobi closure.
-/

namespace InfoGeometry.Exceptional.BartonSudberyThreeChannelAction

open InfoGeometry.Exceptional.CompositionTriality
open InfoGeometry.Exceptional.CompositionTriality.TrialityTriple
open InfoGeometry.Exceptional.BartonSudberyTrialityAction
open scoped TensorProduct

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem bartonSudberyThreeChannel_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- In any noncommutative ring `[Ring E]`, the pointwise commutator on `Fin 3 → E`
is skew-symmetric in each channel: `(T * U - U * T) i = -((U * T - T * U) i)`. -/
theorem ring_three_channel_commutator_skew
    {E : Type*} [Ring E] (T U : Fin 3 → E) (i : Fin 3) :
    (T * U - U * T) i = -((U * T - T * U) i) := by
  change T i * U i - U i * T i = -(U i * T i - T i * U i)
  exact (neg_sub (U i * T i) (T i * U i)).symm

variable {R A B : Type*} [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  {mulA : A →ₗ[R] A →ₗ[R] A}
  {mulB : B →ₗ[R] B →ₗ[R] B}

abbrev ThreeTensorChannels (R A B : Type*) [CommRing R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] := Fin 3 → (A ⊗[R] B)

def channelAction
    (T : TrialityTriple mulA) : Module.End R (ThreeTensorChannels R A B) where
  toFun x i := match i with
    | 0 => leftTrialityAction₁ (A := A) (B := B) T (x 0)
    | 1 => leftTrialityAction₂ (A := A) (B := B) T (x 1)
    | 2 => leftTrialityAction₃ (A := A) (B := B) T (x 2)
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' r x := by
    funext i
    fin_cases i <;> simp

@[simp] theorem channelAction_apply_zero
    (T : TrialityTriple mulA) (x : ThreeTensorChannels R A B) :
    channelAction (R := R) (A := A) (B := B) T x 0 =
      leftTrialityAction₁ (A := A) (B := B) T (x 0) := rfl

@[simp] theorem channelAction_apply_one
    (T : TrialityTriple mulA) (x : ThreeTensorChannels R A B) :
    channelAction (R := R) (A := A) (B := B) T x 1 =
      leftTrialityAction₂ (A := A) (B := B) T (x 1) := rfl

@[simp] theorem channelAction_apply_two
    (T : TrialityTriple mulA) (x : ThreeTensorChannels R A B) :
    channelAction (R := R) (A := A) (B := B) T x 2 =
      leftTrialityAction₃ (A := A) (B := B) T (x 2) := rfl

theorem channelAction_commutator
    (T U : TrialityTriple mulA) :
    channelAction (R := R) (A := A) (B := B) (commutator T U) =
      endCommutator
        (channelAction (R := R) (A := A) (B := B) T)
        (channelAction (R := R) (A := A) (B := B) U) := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i
  · change leftTrialityAction₁ (A := A) (B := B) (commutator T U) (x 0) = _
    rw [leftTrialityAction₁_commutator T U]
    rfl
  · change leftTrialityAction₂ (A := A) (B := B) (commutator T U) (x 1) = _
    rw [leftTrialityAction₂_commutator T U]
    rfl
  · change leftTrialityAction₃ (A := A) (B := B) (commutator T U) (x 2) = _
    rw [leftTrialityAction₃_commutator T U]
    rfl

def rightChannelAction
    (T : TrialityTriple mulB) : Module.End R (ThreeTensorChannels R A B) where
  toFun x i := match i with
    | 0 => rightTrialityAction₁ (A := A) (B := B) T (x 0)
    | 1 => rightTrialityAction₂ (A := A) (B := B) T (x 1)
    | 2 => rightTrialityAction₃ (A := A) (B := B) T (x 2)
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' r x := by
    funext i
    fin_cases i <;> simp

theorem rightChannelAction_commutator
    (T U : TrialityTriple mulB) :
    rightChannelAction (R := R) (A := A) (B := B) (commutator T U) =
      endCommutator
        (rightChannelAction (R := R) (A := A) (B := B) T)
        (rightChannelAction (R := R) (A := A) (B := B) U) := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i
  · change rightTrialityAction₁ (A := A) (B := B) (commutator T U) (x 0) = _
    rw [rightTrialityAction₁_commutator T U]
    rfl
  · change rightTrialityAction₂ (A := A) (B := B) (commutator T U) (x 1) = _
    rw [rightTrialityAction₂_commutator T U]
    rfl
  · change rightTrialityAction₃ (A := A) (B := B) (commutator T U) (x 2) = _
    rw [rightTrialityAction₃_commutator T U]
    rfl

end InfoGeometry.Exceptional.BartonSudberyThreeChannelAction
