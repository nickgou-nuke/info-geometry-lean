/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.LinearMap.End
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Tactic.Abel

set_option linter.unusedVariables false

/-!
# Cartan Involution Foundation (Strictly Algebraic)

This module implements the algebraic foundation for gradings using Cartan 
involutions in any non-commutative ring `[Ring B]` with `[Invertible (2 : B)]`
and in the endomorphism ring `Module.End 𝕜 E`. 

Hierarchy:
1. A Cartan involution θ is an element/endomorphism squaring to identity.
2. It generates canonical projectors P₊ and P₋.
3. These projectors define the space grading and operator parity.

All proofs are purely algebraic, avoiding point-wise evaluation on vectors to
ensure maximum performance and universe consistency.
-/

namespace InfoGeometry.Cartan

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem cartanInvolution_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

section NoncommRing

variable {B : Type*} [Ring B] [Invertible (2 : B)] (θ : B)

/-- A Cartan involution in any noncommutative ring `[Ring B]` is an element squaring to `1`. -/
def IsRingCartanInvolution : Prop := θ * θ = 1

/-- Positive Cartan projector `P₊ = ⅟2 * (1 + θ)` in any `[Ring B] [Invertible (2 : B)]`. -/
def ringPplus : B := ⅟(2 : B) * (1 + θ)

/-- Negative Cartan projector `P₋ = ⅟2 * (1 - θ)` in any `[Ring B] [Invertible (2 : B)]`. -/
def ringPminus : B := ⅟(2 : B) * (1 - θ)

/-- In any noncommutative ring `[Ring B] [Invertible (2 : B)]`, `ringPplus θ + ringPminus θ = 1`. -/
theorem ringPplus_add_ringPminus : ringPplus θ + ringPminus θ = 1 := by
  dsimp [ringPplus, ringPminus]
  rw [← mul_add]
  have h_sum : (1 + θ) + (1 - θ) = (2 : B) := by
    rw [← one_add_one_eq_two]
    abel
  rw [h_sum, invOf_mul_self]

/-- In any noncommutative ring `[Ring B] [Invertible (2 : B)]`, `⅟(2 : B)` commutes with every element. -/
theorem invOf_two_commute (b : B) : Commute (⅟(2 : B)) b :=
  (Commute.ofNat_left 2 b).invOf_left

/-- In any noncommutative ring `[Ring B] [Invertible (2 : B)]`, `ringPplus θ * ringPminus θ = 0`. -/
theorem ringPplus_mul_ringPminus (hθ : IsRingCartanInvolution θ) :
    ringPplus θ * ringPminus θ = 0 := by
  dsimp [ringPplus, ringPminus]
  have hc := (invOf_two_commute (1 + θ)).eq
  have hexp : (1 + θ) * (1 - θ) = 0 := by
    calc
      (1 + θ) * (1 - θ) = 1 - θ * θ := by noncomm_ring
      _ = 0 := by rw [hθ, sub_self]
  calc
    ⅟(2 : B) * (1 + θ) * (⅟(2 : B) * (1 - θ)) =
        ⅟(2 : B) * ((1 + θ) * ⅟(2 : B)) * (1 - θ) := by noncomm_ring
    _ = ⅟(2 : B) * (⅟(2 : B) * (1 + θ)) * (1 - θ) := by rw [← hc]
    _ = (⅟(2 : B) * ⅟(2 : B)) * ((1 + θ) * (1 - θ)) := by noncomm_ring
    _ = 0 := by rw [hexp, mul_zero]

/-- In any noncommutative ring `[Ring B] [Invertible (2 : B)]`, `ringPminus θ * ringPplus θ = 0`. -/
theorem ringPminus_mul_ringPplus (hθ : IsRingCartanInvolution θ) :
    ringPminus θ * ringPplus θ = 0 := by
  dsimp [ringPplus, ringPminus]
  have hc := (invOf_two_commute (1 - θ)).eq
  have hexp : (1 - θ) * (1 + θ) = 0 := by
    calc
      (1 - θ) * (1 + θ) = 1 - θ * θ := by noncomm_ring
      _ = 0 := by rw [hθ, sub_self]
  calc
    ⅟(2 : B) * (1 - θ) * (⅟(2 : B) * (1 + θ)) =
        ⅟(2 : B) * ((1 - θ) * ⅟(2 : B)) * (1 + θ) := by noncomm_ring
    _ = ⅟(2 : B) * (⅟(2 : B) * (1 - θ)) * (1 + θ) := by rw [← hc]
    _ = (⅟(2 : B) * ⅟(2 : B)) * ((1 - θ) * (1 + θ)) := by noncomm_ring
    _ = 0 := by rw [hexp, mul_zero]

/-- In any noncommutative ring `[Ring B] [Invertible (2 : B)]`, `ringPplus θ` is idempotent. -/
theorem ringPplus_idempotent (hθ : IsRingCartanInvolution θ) :
    ringPplus θ * ringPplus θ = ringPplus θ := by
  calc
    ringPplus θ * ringPplus θ =
        ringPplus θ * (ringPplus θ + ringPminus θ) := by
      rw [mul_add, ringPplus_mul_ringPminus θ hθ, add_zero]
    _ = ringPplus θ := by rw [ringPplus_add_ringPminus, mul_one]

/-- In any noncommutative ring `[Ring B] [Invertible (2 : B)]`, `ringPminus θ` is idempotent. -/
theorem ringPminus_idempotent (hθ : IsRingCartanInvolution θ) :
    ringPminus θ * ringPminus θ = ringPminus θ := by
  calc
    ringPminus θ * ringPminus θ =
        (ringPplus θ + ringPminus θ) * ringPminus θ := by
      rw [add_mul, ringPplus_mul_ringPminus θ hθ, zero_add]
    _ = ringPminus θ := by rw [ringPplus_add_ringPminus, one_mul]

end NoncommRing

/-- A Cartan involution is an endomorphism that squares to the identity. -/
def IsCartanInvolution {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] (θ : Module.End 𝕜 E) : Prop :=
  θ * θ = 1

variable {𝕜 E : Type*} [CommRing 𝕜] [Invertible (2 : 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]
variable (θ : Module.End 𝕜 E)

/-- Projection to the +1 eigenspace: P₊ = 1/2 (id + θ). -/
noncomputable def Pplus : Module.End 𝕜 E :=
  (⅟(2 : 𝕜)) • (1 + θ)

/-- Projection to the -1 eigenspace: P₋ = 1/2 (id - θ). -/
noncomputable def Pminus : Module.End 𝕜 E :=
  (⅟(2 : 𝕜)) • (1 - θ)

/-! ### Strictly Algebraic Identities (Endomorphism Ring) -/

/-- Pplus is idempotent: P₊ * P₊ = P₊. -/
lemma Pplus_idempotent (hθ : IsCartanInvolution θ) : (Pplus θ) * (Pplus θ) = Pplus θ := by
  dsimp [Pplus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_expand : (1 + θ) * (1 + θ) = (2 : 𝕜) • (1 + θ) := by
    calc
      (1 + θ) * (1 + θ) = 1 + θ + θ + θ * θ := by
        rw [add_mul, one_mul, mul_add, mul_one, ← add_assoc]
      _ = 1 + θ + θ + 1 := by
        rw [hθ]
      _ = (1 + 1) + (θ + θ) := by
        abel_nf
      _ = (2 : 𝕜) • 1 + (2 : 𝕜) • θ := by
        rw [two_smul, two_smul]
      _ = (2 : 𝕜) • (1 + θ) := by
        rw [smul_add]
  rw [h_expand, smul_smul, mul_assoc, invOf_mul_self, mul_one]

/-- Pminus is idempotent: P₋ * P₋ = P₋. -/
lemma Pminus_idempotent (hθ : IsCartanInvolution θ) : (Pminus θ) * (Pminus θ) = Pminus θ := by
  dsimp [Pminus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_expand : (1 - θ) * (1 - θ) = (2 : 𝕜) • (1 - θ) := by
    calc
      (1 - θ) * (1 - θ) = 1 - θ - θ + θ * θ := by
        rw [sub_mul, one_mul, mul_sub, mul_one]
        abel_nf
      _ = 1 - θ - θ + 1 := by
        rw [hθ]
      _ = (1 + 1) - (θ + θ) := by
        abel_nf
      _ = (2 : 𝕜) • 1 - (2 : 𝕜) • θ := by
        rw [two_smul, two_smul]
      _ = (2 : 𝕜) • (1 - θ) := by
        rw [smul_sub]
  rw [h_expand, smul_smul, mul_assoc, invOf_mul_self, mul_one]

/-- The sum of the projectors is the identity. -/
lemma Pplus_add_Pminus_eq_id : Pplus θ + Pminus θ = 1 := by
  dsimp [Pplus, Pminus]
  rw [← smul_add]
  have h_sum : (1 + θ) + (1 - θ) = (2 : 𝕜) • 1 := by
    calc
      (1 + θ) + (1 - θ) = (1 + 1) := by
        abel_nf
      _ = (2 : 𝕜) • 1 := by
        rw [two_smul]
  rw [h_sum, smul_smul, invOf_mul_self, one_smul]

/-- Projectors are complementary: P₊ * P₋ = 0. -/
lemma Pplus_comp_Pminus (hθ : IsCartanInvolution θ) : (Pplus θ) * (Pminus θ) = 0 := by
  dsimp [Pplus, Pminus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_expand : (1 + θ) * (1 - θ) = 1 - θ * θ := by
    rw [add_mul, one_mul, mul_sub, mul_one]
    abel_nf
  rw [h_expand, hθ, sub_self, smul_zero]

/-- Projectors are complementary in the opposite order: P₋ * P₊ = 0. -/
lemma Pminus_comp_Pplus (hθ : IsCartanInvolution θ) : (Pminus θ) * (Pplus θ) = 0 := by
  dsimp [Pplus, Pminus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_expand : (1 - θ) * (1 + θ) = 1 - θ * θ := by
    rw [sub_mul, one_mul, mul_add, mul_one]
    abel_nf
  rw [h_expand, hθ, sub_self, smul_zero]

/-- The involution acts as `+1` after projection to its positive eigenspace. -/
lemma involution_comp_Pplus (hθ : IsCartanInvolution θ) :
    θ * Pplus θ = Pplus θ := by
  dsimp [Pplus]
  rw [mul_smul_comm]
  congr 1
  calc
    θ * (1 + θ) = θ * 1 + θ * θ := by rw [mul_add]
    _ = θ + 1 := by rw [mul_one, hθ]
    _ = 1 + θ := by rw [add_comm]

/-- The involution acts as `-1` after projection to its negative eigenspace. -/
lemma involution_comp_Pminus (hθ : IsCartanInvolution θ) :
    θ * Pminus θ = -Pminus θ := by
  dsimp [Pminus]
  rw [mul_smul_comm, ← smul_neg]
  congr 1
  calc
    θ * (1 - θ) = θ * 1 - θ * θ := by rw [mul_sub]
    _ = θ - 1 := by rw [mul_one, hθ]
    _ = -(1 - θ) := by rw [neg_sub]

/-- An endomorphism anticommuting with `θ` sends the positive projector
channel into the negative channel. The statement only uses the displayed
anticommutation law; involutivity is needed separately for the projectors to
be idempotent eigenspace projections. -/
lemma anticommutingEnd_comp_Pplus (T : Module.End 𝕜 E)
    (hT : T * θ = -(θ * T)) :
    T * Pplus θ = Pminus θ * T := by
  dsimp [Pplus, Pminus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  calc
    T * (1 + θ) = T * 1 + T * θ := by rw [mul_add]
    _ = T + -(θ * T) := by rw [mul_one, hT]
    _ = T - θ * T := by abel
    _ = (1 - θ) * T := by rw [sub_mul, one_mul]

/-- An endomorphism anticommuting with `θ` sends the negative projector
channel into the positive channel. -/
lemma anticommutingEnd_comp_Pminus (T : Module.End 𝕜 E)
    (hT : T * θ = -(θ * T)) :
    T * Pminus θ = Pplus θ * T := by
  dsimp [Pplus, Pminus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  calc
    T * (1 - θ) = T * 1 - T * θ := by rw [mul_sub]
    _ = T + θ * T := by rw [mul_one, hT, sub_neg_eq_add]
    _ = (1 + θ) * T := by rw [add_mul, one_mul]

/-! ### Vector Bridge Lemmas (Pointwise Descent) -/

lemma Pplus_apply (x : E) : (Pplus θ) x = (⅟(2 : 𝕜)) • (x + θ x) := by
  simp only [Pplus, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply]

lemma Pminus_apply (x : E) : (Pminus θ) x = (⅟(2 : 𝕜)) • (x - θ x) := by
  simp only [Pminus, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]

lemma decompose (hθ : IsCartanInvolution θ) (x : E) : x = (Pplus θ) x + (Pminus θ) x := by
  have _ := Pplus_idempotent θ hθ
  rw [← LinearMap.add_apply, Pplus_add_Pminus_eq_id, Module.End.one_apply]

end InfoGeometry.Cartan
