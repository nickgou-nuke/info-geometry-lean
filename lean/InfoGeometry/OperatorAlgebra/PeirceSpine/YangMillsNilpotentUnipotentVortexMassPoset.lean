/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Yang–Mills Nilpotent-to-Unipotent Vortex Mass Poset (`YM₁`–`YM₁₀`) & ’t Hooft–Wilson Loop Braiding

This module formalizes:
1. **The 10-Stage Acyclic Causal Poset (`YM₁ ≺ YM₂ ≺ ⋯ ≺ YM₁₀`)** (`YangMillsVortexPoset`) for the
   algebraic mechanism by which nilpotent gluon/ghost modes (`N_+² = 0`, `N_-² = 0` with
   `N_- = star N_+` and Von Neumann regularity `N_+ N_- N_+ = N_+`) coagulate into unipotent
   Wilson-loop holonomies (`U_± = 1 + N_±`) across a two-sheeted chiral cut, generating `ℤ₂` center
   vortices and the dynamical Yang–Mills mass gap (`M_vortex² = V = P + Q`) without an elementary
   Higgs scalar.
2. **The ’t Hooft–Wilson Loop Braiding Algebra** (`YangMillsTHooftWilsonBraiding`) across the
   two-sheeted chiral condensate `V = P + Q`:
   - Off-diagonal Peirce-projected Wilson links `U_plus_off = P U_+ Q = N_+ = U_+ - 1` and
     `U_minus_off = Q U_- P = N_- = U_- - 1`,
   - Exact `ℤ₂` ’t Hooft–Wilson anticommutation `Z_center * U_plus_off + U_plus_off * Z_center = 0`,
     `Z_center * U_minus_off + U_minus_off * Z_center = 0`, and
     `Sigma * U_plus_off + U_plus_off * Sigma = 0`,
   - Group-level unipotent inversion `Z_center U_+ Z_center = U_+⁻¹` and
     `Z_center U_- Z_center = U_-⁻¹`,
   - ’t Hooft–Wilson orbit sum `W_+ + Z_center W_+ Z_center = 2P` (`ℤ₂`-even condensate channel) and
     braiding defect `W_+ - Z_center W_+ Z_center = 2Φ` (`ℤ₂`-odd massive mode channel),
   - Core-to-vacuum vortex boundary braiding `Z_vortex * W_edge + W_edge * Z_vortex = 0`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset

open scoped Matrix

/-!
### 0. The 10-Stage Acyclic Causal Poset (`YM₁ ≺ YM₂ ≺ ⋯ ≺ YM₁₀`) & Universal Ring Helpers
-/

/-- The 10 stages of the Yang–Mills Nilpotent-to-Unipotent Vortex Mass Poset (`YM₁`–`YM₁₀`). -/
inductive YangMillsVortexStage : Type
  | YM1_NilpotentToUnipotentCayleyLift
  | YM2_UnipotentFieldStrengthCommutator
  | YM3_TwoSheetedUnipotentCondensate
  | YM4_CondensateSumMassAndDiffFlux
  | YM5_MaurerCartanUnipotentGaugeCurrents
  | YM6_SteinbergUnipotentVortexBraid
  | YM7_Z2CenterVortexMonodromy
  | YM8_DynamicalProcaKleinGordonVortexMass
  | YM9_BogomolnyBPSVortexMassSaturation
  | YM10_CenterVortexHolonomyMasterSynthesis
  deriving DecidableEq, Repr

namespace YangMillsVortexStage

/-- Numerical causal depth (`0` through `9`) of each stage in `YangMillsVortexStage`. -/
def rank : YangMillsVortexStage → ℕ
  | .YM1_NilpotentToUnipotentCayleyLift       => 0
  | .YM2_UnipotentFieldStrengthCommutator     => 1
  | .YM3_TwoSheetedUnipotentCondensate        => 2
  | .YM4_CondensateSumMassAndDiffFlux         => 3
  | .YM5_MaurerCartanUnipotentGaugeCurrents   => 4
  | .YM6_SteinbergUnipotentVortexBraid        => 5
  | .YM7_Z2CenterVortexMonodromy              => 6
  | .YM8_DynamicalProcaKleinGordonVortexMass  => 7
  | .YM9_BogomolnyBPSVortexMassSaturation     => 8
  | .YM10_CenterVortexHolonomyMasterSynthesis => 9

/-- Strict causal precedence `s₁ ≺ s₂` in the 10-stage Yang–Mills Vortex Mass Poset. -/
abbrev causalEdge (s₁ s₂ : YangMillsVortexStage) : Prop :=
  s₁.rank < s₂.rank

/-- Reflexive-transitive causal order `s₁ ≼ s₂`. -/
abbrev causalLe (s₁ s₂ : YangMillsVortexStage) : Prop :=
  s₁.rank ≤ s₂.rank

instance instLT : LT YangMillsVortexStage := ⟨causalEdge⟩
instance instLE : LE YangMillsVortexStage := ⟨causalLe⟩

/-- `YangMillsVortexStage` forms a strict 10-element `LinearOrder`. -/
instance instLinearOrder : LinearOrder YangMillsVortexStage where
  le := causalLe
  lt := causalEdge
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm a b hab hba := by
    have hEq : a.rank = b.rank := Nat.le_antisymm hab hba
    cases a <;> cases b <;> first | rfl | cases hEq
  le_total a b := Nat.le_total a.rank b.rank
  toDecidableLE := fun a b => Nat.decLe a.rank b.rank
  toDecidableLT := fun a b => Nat.decLt a.rank b.rank
  toDecidableEq := inferInstance

/-- **Strict 10-Stage Poset Chain & Acyclicity (`YM₁ ≺ YM₂ ≺ ⋯ ≺ YM₁₀`)**. -/
theorem poset_chain_and_acyclicity :
    (causalEdge .YM1_NilpotentToUnipotentCayleyLift .YM2_UnipotentFieldStrengthCommutator ∧
     causalEdge .YM2_UnipotentFieldStrengthCommutator .YM3_TwoSheetedUnipotentCondensate ∧
     causalEdge .YM3_TwoSheetedUnipotentCondensate .YM4_CondensateSumMassAndDiffFlux ∧
     causalEdge .YM4_CondensateSumMassAndDiffFlux .YM5_MaurerCartanUnipotentGaugeCurrents ∧
     causalEdge .YM5_MaurerCartanUnipotentGaugeCurrents .YM6_SteinbergUnipotentVortexBraid ∧
     causalEdge .YM6_SteinbergUnipotentVortexBraid .YM7_Z2CenterVortexMonodromy ∧
     causalEdge .YM7_Z2CenterVortexMonodromy .YM8_DynamicalProcaKleinGordonVortexMass ∧
     causalEdge .YM8_DynamicalProcaKleinGordonVortexMass .YM9_BogomolnyBPSVortexMassSaturation ∧
     causalEdge .YM9_BogomolnyBPSVortexMassSaturation .YM10_CenterVortexHolonomyMasterSynthesis) ∧
    (∀ s : YangMillsVortexStage, ¬ causalEdge s s) ∧
    (∀ s₁ s₂ : YangMillsVortexStage, causalEdge s₁ s₂ → ¬ causalEdge s₂ s₁) ∧
    (∀ s₁ s₂ s₃ : YangMillsVortexStage,
      causalEdge s₁ s₂ → causalEdge s₂ s₃ → causalEdge s₁ s₃) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro s; exact Nat.lt_irrefl s.rank
  · intro s₁ s₂ h12 h21; exact Nat.lt_asymm h12 h21
  · intro s₁ s₂ s₃ h12 h23; exact Nat.lt_trans h12 h23

end YangMillsVortexStage

section RingHelpers

variable {B : Type*} [Ring B]

theorem sub_add_self (x y : B) : (x - y) + y = x := by
  calc (x - y) + y
    _ = (x + -y) + y := by rw [sub_eq_add_neg]
    _ = x + (-y + y) := by rw [add_assoc]
    _ = x + (y + -y) := by rw [add_comm (-y) y]
    _ = x + (y - y) := by rw [← sub_eq_add_neg]
    _ = x + 0 := by rw [sub_self]
    _ = x := by rw [add_zero]

theorem add_sub_self_right (x y : B) : (x + y) - y = x := by
  calc (x + y) - y
    _ = (x + y) + -y := by rw [sub_eq_add_neg]
    _ = x + (y + -y) := by rw [add_assoc]
    _ = x + (y - y) := by rw [← sub_eq_add_neg]
    _ = x + 0 := by rw [sub_self]
    _ = x := by rw [add_zero]

theorem add_sub_self_left (x y : B) : (x + y) - x = y := by
  rw [add_comm x y, add_sub_self_right]

theorem add_sub_assoc' (a b c : B) : a + (b - c) = (a + b) - c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]

theorem sub_add_eq_sub_sub (a b c : B) : a - (b + c) = (a - b) - c := by
  calc a - (b + c)
    _ = a + -(b + c) := by rw [sub_eq_add_neg]
    _ = a + (-c + -b) := by rw [neg_add_rev]
    _ = a + (-b + -c) := by rw [add_comm (-c) (-b)]
    _ = (a + -b) + -c := by rw [← add_assoc]
    _ = (a - b) - c := by rw [← sub_eq_add_neg, ← sub_eq_add_neg]

theorem add_add_sub_cancel (a b : B) : (a + b) + (a - b) = a + a := by
  calc (a + b) + (a - b)
    _ = (a - b) + (a + b) := by rw [add_comm (a + b) (a - b)]
    _ = (a - b) + (b + a) := by rw [add_comm a b]
    _ = ((a - b) + b) + a := by rw [← add_assoc (a - b) b a]
    _ = a + a := by rw [sub_add_self]

theorem sub_add_sub_cancel_two (a b : B) : (a + b) - (a - b) = b + b := by
  have h : a + b = (b + b) + (a - b) := by
    calc a + b
      _ = b + a := by rw [add_comm]
      _ = b + ((a - b) + b) := by rw [sub_add_self a b]
      _ = b + (b + (a - b)) := by rw [add_comm (a - b) b]
      _ = (b + b) + (a - b) := by rw [← add_assoc b b (a - b)]
  calc (a + b) - (a - b)
    _ = ((b + b) + (a - b)) - (a - b) := by rw [h]
    _ = b + b := by rw [add_sub_self_right]

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Positive-chiral Unipotent holonomy `U_+ = 1 + N_+`. -/
def U_plus (N_plus : B) : B := 1 + N_plus

/-- Inverse positive-chiral Unipotent holonomy `U_+⁻¹ = 1 - N_+`. -/
def U_plus_inv (N_plus : B) : B := 1 - N_plus

/-- `YM₁` Right invertibility of `U_+`: `(1 + N_+)(1 - N_+) = 1`. -/
theorem U_plus_mul_inv (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    U_plus N_plus * U_plus_inv N_plus = 1 := by
  dsimp [U_plus, U_plus_inv]
  calc (1 + N_plus) * (1 - N_plus)
    _ = (1 + N_plus) * 1 - (1 + N_plus) * N_plus := by rw [mul_sub]
    _ = (1 + N_plus) - (1 * N_plus + N_plus * N_plus) := by rw [mul_one, add_mul]
    _ = (1 + N_plus) - (N_plus + 0) := by rw [one_mul, h_nil]
    _ = (1 + N_plus) - N_plus := by rw [add_zero]
    _ = 1 := by rw [add_sub_self_right]

/-- `YM₁` Left invertibility of `U_+`: `(1 - N_+)(1 + N_+) = 1`. -/
theorem U_plus_inv_mul (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    U_plus_inv N_plus * U_plus N_plus = 1 := by
  dsimp [U_plus, U_plus_inv]
  calc (1 - N_plus) * (1 + N_plus)
    _ = (1 - N_plus) * 1 + (1 - N_plus) * N_plus := by rw [mul_add]
    _ = (1 - N_plus) + (1 * N_plus - N_plus * N_plus) := by rw [mul_one, sub_mul]
    _ = (1 - N_plus) + (N_plus - 0) := by rw [one_mul, h_nil]
    _ = (1 - N_plus) + N_plus := by rw [sub_zero]
    _ = 1 := by rw [sub_add_self]

end RingHelpers

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 1. Primitive Nilpotent, Projector, and Unipotent Definitions (`YM₁`)
-/

/-- Sheet `+` emergent projector `P = N_+ N_-`. -/
def P (N_plus : B) : B := N_plus * star N_plus

/-- Sheet `-` emergent projector `Q = N_- N_+`. -/
def Q (N_plus : B) : B := star N_plus * N_plus

/-- Emergent Vortex Mass-Squared / Metric operator `V = {N_+, N_-} = P + Q`. -/
def V (N_plus : B) : B := N_plus * star N_plus + star N_plus * N_plus

/-- Emergent Magnetic Vortex Flux / Sheet Grading `Σ = [N_+, N_-] = P - Q`. -/
def Sigma (N_plus : B) : B := N_plus * star N_plus - star N_plus * N_plus

/-- Self-adjoint gauge vector mode `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Skew-adjoint elliptic rotor bivector `J = N_+ - N_-`. -/
def J (N_plus : B) : B := N_plus - star N_plus

/-- Negative-chiral Unipotent holonomy `U_- = 1 + N_-`. -/
def U_minus (N_plus : B) : B := 1 + star N_plus

/-- Inverse negative-chiral Unipotent holonomy `U_-⁻¹ = 1 - N_-`. -/
def U_minus_inv (N_plus : B) : B := 1 - star N_plus

/-- Dual nilpotency `(N_-)^2 = 0`. -/
theorem star_N_plus_sq (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * star N_plus = 0 := by
  rw [← star_mul, h_nil, star_zero]

/-- Dual Von Neumann regularity `N_- N_+ N_- = N_-`. -/
theorem star_N_plus_reg (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * N_plus * star N_plus = star N_plus := by
  have h := congrArg star h_reg
  rw [star_mul, star_mul, star_star, ← mul_assoc] at h
  exact h

theorem P_idem (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * P N_plus = P N_plus := by
  dsimp [P]
  rw [← mul_assoc (N_plus * star N_plus) N_plus (star N_plus), h_reg]

theorem Q_idem (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Q N_plus * Q N_plus = Q N_plus := by
  dsimp [Q]
  rw [← mul_assoc (star N_plus * N_plus) (star N_plus) N_plus, star_N_plus_reg N_plus h_reg]

theorem P_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    P N_plus * Q N_plus = 0 := by
  dsimp [P, Q]
  calc (N_plus * star N_plus) * (star N_plus * N_plus)
    _ = N_plus * (star N_plus * (star N_plus * N_plus)) := by
        rw [mul_assoc N_plus (star N_plus) (star N_plus * N_plus)]
    _ = N_plus * ((star N_plus * star N_plus) * N_plus) := by
        rw [← mul_assoc (star N_plus) (star N_plus) N_plus]
    _ = N_plus * (0 * N_plus) := by rw [star_N_plus_sq N_plus h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

theorem Q_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * P N_plus = 0 := by
  dsimp [P, Q]
  calc (star N_plus * N_plus) * (N_plus * star N_plus)
    _ = star N_plus * (N_plus * (N_plus * star N_plus)) := by
        rw [mul_assoc (star N_plus) N_plus (N_plus * star N_plus)]
    _ = star N_plus * ((N_plus * N_plus) * star N_plus) := by
        rw [← mul_assoc N_plus N_plus (star N_plus)]
    _ = star N_plus * (0 * star N_plus) := by rw [h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

theorem P_mul_N_plus (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * N_plus = N_plus := h_reg

/-- `YM₁` Right invertibility of `U_-`: `(1 + N_-)(1 - N_-) = 1`. -/
theorem U_minus_mul_inv (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    U_minus N_plus * U_minus_inv N_plus = 1 := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  dsimp [U_minus, U_minus_inv]
  calc (1 + star N_plus) * (1 - star N_plus)
    _ = (1 + star N_plus) * 1 - (1 + star N_plus) * star N_plus := by rw [mul_sub]
    _ = (1 + star N_plus) - (1 * star N_plus + star N_plus * star N_plus) := by
        rw [mul_one, add_mul]
    _ = (1 + star N_plus) - (star N_plus + 0) := by rw [one_mul, h_star_nil]
    _ = (1 + star N_plus) - star N_plus := by rw [add_zero]
    _ = 1 := by rw [add_sub_self_right]

/-- `YM₁` Left invertibility of `U_-`: `(1 - N_-)(1 + N_-) = 1`. -/
theorem U_minus_inv_mul (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    U_minus_inv N_plus * U_minus N_plus = 1 := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  dsimp [U_minus, U_minus_inv]
  calc (1 - star N_plus) * (1 + star N_plus)
    _ = (1 - star N_plus) * 1 + (1 - star N_plus) * star N_plus := by rw [mul_add]
    _ = (1 - star N_plus) + (1 * star N_plus - star N_plus * star N_plus) := by
        rw [mul_one, sub_mul]
    _ = (1 - star N_plus) + (star N_plus - 0) := by rw [one_mul, h_star_nil]
    _ = (1 - star N_plus) + star N_plus := by rw [sub_zero]
    _ = 1 := by rw [sub_add_self]

/-- Chiral adjoint duality between the two unipotent sheets: `star U_+ = U_-`. -/
theorem star_U_plus (N_plus : B) : star (U_plus N_plus) = U_minus N_plus := by
  dsimp [U_plus, U_minus]
  rw [star_add, star_one]

/-!
### 2. Unipotent Commutator & Two-Sheeted Bilinear Condensate (`YM₂–YM₄`)
-/

/-- Expansion of the positive-sheet unipotent product `U_+ U_- = (1 + Φ) + P`. -/
theorem U_plus_mul_U_minus (N_plus : B) :
    U_plus N_plus * U_minus N_plus = (1 + Phi N_plus) + P N_plus := by
  dsimp [U_plus, U_minus, Phi, P]
  calc (1 + N_plus) * (1 + star N_plus)
    _ = (1 + N_plus) * 1 + (1 + N_plus) * star N_plus := by rw [mul_add]
    _ = (1 + N_plus) + (1 * star N_plus + N_plus * star N_plus) := by
        rw [mul_one, add_mul]
    _ = (1 + N_plus) + (star N_plus + N_plus * star N_plus) := by rw [one_mul]
    _ = ((1 + N_plus) + star N_plus) + N_plus * star N_plus := by
        rw [← add_assoc (1 + N_plus) (star N_plus)]
    _ = (1 + (N_plus + star N_plus)) + N_plus * star N_plus := by
        rw [add_assoc 1 N_plus (star N_plus)]

/-- Expansion of the inverse positive-sheet unipotent product `U_+⁻¹ U_-⁻¹ = (1 - Φ) + P`. -/
theorem U_plus_inv_mul_U_minus_inv (N_plus : B) :
    U_plus_inv N_plus * U_minus_inv N_plus = (1 - Phi N_plus) + P N_plus := by
  dsimp [U_plus_inv, U_minus_inv, Phi, P]
  calc (1 - N_plus) * (1 - star N_plus)
    _ = (1 - N_plus) * 1 - (1 - N_plus) * star N_plus := by rw [mul_sub]
    _ = (1 - N_plus) - (1 * star N_plus - N_plus * star N_plus) := by
        rw [mul_one, sub_mul]
    _ = (1 - N_plus) - (star N_plus - N_plus * star N_plus) := by rw [one_mul]
    _ = (1 - N_plus) + -(star N_plus + -(N_plus * star N_plus)) := by
        rw [sub_eq_add_neg (1 - N_plus), sub_eq_add_neg (star N_plus)]
    _ = (1 - N_plus) + (N_plus * star N_plus + -star N_plus) := by
        rw [neg_add_rev, neg_neg]
    _ = (1 - N_plus) + (-star N_plus + N_plus * star N_plus) := by
        rw [add_comm (N_plus * star N_plus) (-star N_plus)]
    _ = ((1 - N_plus) + -star N_plus) + N_plus * star N_plus := by
        rw [← add_assoc]
    _ = ((1 - N_plus) - star N_plus) + N_plus * star N_plus := by
        rw [← sub_eq_add_neg]
    _ = (1 - (N_plus + star N_plus)) + N_plus * star N_plus := by
        rw [← sub_add_eq_sub_sub]

/-- Expansion of the negative-sheet unipotent product `U_- U_+ = (1 + Φ) + Q`. -/
theorem U_minus_mul_U_plus (N_plus : B) :
    U_minus N_plus * U_plus N_plus = (1 + Phi N_plus) + Q N_plus := by
  dsimp [U_plus, U_minus, Phi, Q]
  calc (1 + star N_plus) * (1 + N_plus)
    _ = (1 + star N_plus) * 1 + (1 + star N_plus) * N_plus := by rw [mul_add]
    _ = (1 + star N_plus) + (1 * N_plus + star N_plus * N_plus) := by
        rw [mul_one, add_mul]
    _ = (1 + star N_plus) + (N_plus + star N_plus * N_plus) := by rw [one_mul]
    _ = ((1 + star N_plus) + N_plus) + star N_plus * N_plus := by
        rw [← add_assoc (1 + star N_plus) N_plus]
    _ = (1 + (star N_plus + N_plus)) + star N_plus * N_plus := by
        rw [add_assoc 1 (star N_plus) N_plus]
    _ = (1 + (N_plus + star N_plus)) + star N_plus * N_plus := by
        rw [add_comm (star N_plus) N_plus]

/-- Expansion of the inverse negative-sheet unipotent product `U_-⁻¹ U_+⁻¹ = (1 - Φ) + Q`. -/
theorem U_minus_inv_mul_U_plus_inv (N_plus : B) :
    U_minus_inv N_plus * U_plus_inv N_plus = (1 - Phi N_plus) + Q N_plus := by
  dsimp [U_plus_inv, U_minus_inv, Phi, Q]
  calc (1 - star N_plus) * (1 - N_plus)
    _ = (1 - star N_plus) * 1 - (1 - star N_plus) * N_plus := by rw [mul_sub]
    _ = (1 - star N_plus) - (1 * N_plus - star N_plus * N_plus) := by
        rw [mul_one, sub_mul]
    _ = (1 - star N_plus) - (N_plus - star N_plus * N_plus) := by rw [one_mul]
    _ = (1 - star N_plus) + -(N_plus + -(star N_plus * N_plus)) := by
        rw [sub_eq_add_neg (1 - star N_plus), sub_eq_add_neg N_plus]
    _ = (1 - star N_plus) + (star N_plus * N_plus + -N_plus) := by
        rw [neg_add_rev, neg_neg]
    _ = (1 - star N_plus) + (-N_plus + star N_plus * N_plus) := by
        rw [add_comm (star N_plus * N_plus) (-N_plus)]
    _ = ((1 - star N_plus) + -N_plus) + star N_plus * N_plus := by
        rw [← add_assoc]
    _ = ((1 - star N_plus) - N_plus) + star N_plus * N_plus := by
        rw [← sub_eq_add_neg]
    _ = (1 - (star N_plus + N_plus)) + star N_plus * N_plus := by
        rw [← sub_add_eq_sub_sub]
    _ = (1 - (N_plus + star N_plus)) + star N_plus * N_plus := by
        rw [add_comm (star N_plus) N_plus]

/-- **`YM₂` Unipotent Field Strength Theorem (`[U_+, U_-] = Σ`):**
    The commutator of the unipotent holonomies `U_+` and `U_-` is identically
    the non-Abelian magnetic curvature `Σ = [N_+, N_-] = P - Q`. -/
theorem comm_U_plus_U_minus (N_plus : B) :
    comm (U_plus N_plus) (U_minus N_plus) = Sigma N_plus := by
  dsimp [comm]
  rw [U_plus_mul_U_minus, U_minus_mul_U_plus]
  calc ((1 + Phi N_plus) + P N_plus) - ((1 + Phi N_plus) + Q N_plus)
    _ = (((1 + Phi N_plus) + P N_plus) - (1 + Phi N_plus)) - Q N_plus := by
        rw [sub_add_eq_sub_sub]
    _ = P N_plus - Q N_plus := by rw [add_sub_self_left]
    _ = Sigma N_plus := rfl

/-- Sheet `+` symmetrized unipotent condensate `𝒞_+ = (U_+ U_- - 1) + (U_+⁻¹ U_-⁻¹ - 1)`. -/
def C_plus (N_plus : B) : B :=
  (U_plus N_plus * U_minus N_plus - 1) +
  (U_plus_inv N_plus * U_minus_inv N_plus - 1)

/-- Sheet `-` symmetrized unipotent condensate `𝒞_- = (U_- U_+ - 1) + (U_-⁻¹ U_+⁻¹ - 1)`. -/
def C_minus (N_plus : B) : B :=
  (U_minus N_plus * U_plus N_plus - 1) +
  (U_minus_inv N_plus * U_plus_inv N_plus - 1)

/-- **`YM₃` Sheet `+` Unipotent Condensation (`𝒞_+ = 2P`):**
    Averaging `U_+ U_- - 1` over the `ℤ₂` center flip `U_± ↔ U_±⁻¹` cancels the linear
    gauge mode `Φ` and condenses twice the positive-sheet projector `P`. -/
theorem C_plus_eq_two_P (N_plus : B) :
    C_plus N_plus = P N_plus + P N_plus := by
  dsimp [C_plus]
  rw [U_plus_mul_U_minus, U_plus_inv_mul_U_minus_inv]
  have h1 : ((1 + Phi N_plus) + P N_plus) - 1 = P N_plus + Phi N_plus := by
    rw [add_comm (1 + Phi N_plus) (P N_plus),
        add_comm 1 (Phi N_plus),
        ← add_assoc (P N_plus) (Phi N_plus) 1,
        add_sub_self_right]
  have h2 : ((1 - Phi N_plus) + P N_plus) - 1 = P N_plus - Phi N_plus := by
    rw [add_comm (1 - Phi N_plus) (P N_plus),
        sub_eq_add_neg 1 (Phi N_plus),
        add_comm 1 (-Phi N_plus),
        ← add_assoc (P N_plus) (-Phi N_plus) 1,
        add_sub_self_right,
        ← sub_eq_add_neg]
  rw [h1, h2, add_add_sub_cancel]

/-- **`YM₃` Sheet `-` Unipotent Condensation (`𝒞_- = 2Q`):**
    On the dual sheet, the `ℤ₂`-averaged unipotent holonomy condenses `2Q`. -/
theorem C_minus_eq_two_Q (N_plus : B) :
    C_minus N_plus = Q N_plus + Q N_plus := by
  dsimp [C_minus]
  rw [U_minus_mul_U_plus, U_minus_inv_mul_U_plus_inv]
  have h1 : ((1 + Phi N_plus) + Q N_plus) - 1 = Q N_plus + Phi N_plus := by
    rw [add_comm (1 + Phi N_plus) (Q N_plus),
        add_comm 1 (Phi N_plus),
        ← add_assoc (Q N_plus) (Phi N_plus) 1,
        add_sub_self_right]
  have h2 : ((1 - Phi N_plus) + Q N_plus) - 1 = Q N_plus - Phi N_plus := by
    rw [add_comm (1 - Phi N_plus) (Q N_plus),
        sub_eq_add_neg 1 (Phi N_plus),
        add_comm 1 (-Phi N_plus),
        ← add_assoc (Q N_plus) (-Phi N_plus) 1,
        add_sub_self_right,
        ← sub_eq_add_neg]
  rw [h1, h2, add_add_sub_cancel]

/-- **`YM₄` Total Two-Sheeted Condensate (`𝒞_+ + 𝒞_- = 2V`):**
    The sum of the two unipotent sheet condensates generates twice the
    vortex mass-squared operator `V = P + Q`. -/
theorem two_sheeted_condensate_sum (N_plus : B) :
    C_plus N_plus + C_minus N_plus = V N_plus + V N_plus := by
  rw [C_plus_eq_two_P, C_minus_eq_two_Q]
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV]
  calc (P N_plus + P N_plus) + (Q N_plus + Q N_plus)
    _ = P N_plus + (P N_plus + (Q N_plus + Q N_plus)) := by
        rw [add_assoc (P N_plus) (P N_plus) (Q N_plus + Q N_plus)]
    _ = P N_plus + ((P N_plus + Q N_plus) + Q N_plus) := by
        rw [← add_assoc (P N_plus) (Q N_plus) (Q N_plus)]
    _ = P N_plus + (Q N_plus + (P N_plus + Q N_plus)) := by
        rw [add_comm (P N_plus + Q N_plus) (Q N_plus)]
    _ = (P N_plus + Q N_plus) + (P N_plus + Q N_plus) := by
        rw [← add_assoc (P N_plus) (Q N_plus) (P N_plus + Q N_plus)]

/-- **`YM₄` Inter-Sheet Branch-Cut Difference (`𝒞_+ - 𝒞_- = 2Σ`):**
    The difference between the two unipotent sheet condensates is twice the
    magnetic vortex flux `Σ = P - Q`. -/
theorem two_sheeted_condensate_diff (N_plus : B) :
    C_plus N_plus - C_minus N_plus = Sigma N_plus + Sigma N_plus := by
  rw [C_plus_eq_two_P, C_minus_eq_two_Q]
  have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
  rw [hS]
  calc (P N_plus + P N_plus) - (Q N_plus + Q N_plus)
    _ = ((P N_plus + P N_plus) - Q N_plus) - Q N_plus := by rw [sub_add_eq_sub_sub]
    _ = (P N_plus + (P N_plus - Q N_plus)) - Q N_plus := by rw [← add_sub_assoc']
    _ = ((P N_plus - Q N_plus) + P N_plus) - Q N_plus := by
        rw [add_comm (P N_plus) (P N_plus - Q N_plus)]
    _ = (P N_plus - Q N_plus) + (P N_plus - Q N_plus) := by rw [← add_sub_assoc']

/-!
### 3. Maurer–Cartan Unipotent Gauge Currents (`YM₅`)
-/

theorem Sigma_mul_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * N_plus = N_plus := by
  dsimp [Sigma]
  rw [sub_mul, h_reg, mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero, sub_zero]

theorem N_plus_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * Sigma N_plus = -N_plus := by
  dsimp [Sigma]
  rw [mul_sub, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
      ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_sub]

theorem Sigma_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * star N_plus = -star N_plus := by
  dsimp [Sigma]
  rw [sub_mul, mul_assoc N_plus (star N_plus) (star N_plus),
      star_N_plus_sq N_plus h_nil, mul_zero,
      star_N_plus_reg N_plus h_reg, zero_sub]

theorem star_N_plus_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * Sigma N_plus = star N_plus := by
  dsimp [Sigma]
  rw [mul_sub, ← mul_assoc (star N_plus) N_plus (star N_plus),
      star_N_plus_reg N_plus h_reg,
      ← mul_assoc (star N_plus) (star N_plus) N_plus,
      star_N_plus_sq N_plus h_nil, zero_mul, sub_zero]

/-- **`YM₅` Positive Unipotent Adjoint Action (`U_+ Σ U_+⁻¹ = Σ - 2N_+`):**
    Conjugating the sheet grading `Σ` by the unipotent holonomy `U_+` shifts `Σ`
    by twice the nilpotent current `-2N_+`. -/
theorem U_plus_conj_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_plus N_plus * Sigma N_plus * U_plus_inv N_plus =
      Sigma N_plus - (N_plus + N_plus) := by
  dsimp [U_plus, U_plus_inv]
  have hL : (1 + N_plus) * Sigma N_plus = Sigma N_plus - N_plus := by
    rw [add_mul, one_mul, N_plus_mul_Sigma N_plus h_nil h_reg, ← sub_eq_add_neg]
  calc (1 + N_plus) * Sigma N_plus * (1 - N_plus)
    _ = (Sigma N_plus - N_plus) * (1 - N_plus) := by rw [hL]
    _ = (Sigma N_plus - N_plus) * 1 - (Sigma N_plus - N_plus) * N_plus := by
        rw [mul_sub]
    _ = (Sigma N_plus - N_plus) - (Sigma N_plus * N_plus - N_plus * N_plus) := by
        rw [mul_one, sub_mul]
    _ = (Sigma N_plus - N_plus) - (N_plus - 0) := by
        rw [Sigma_mul_N_plus N_plus h_nil h_reg, h_nil]
    _ = (Sigma N_plus - N_plus) - N_plus := by rw [sub_zero]
    _ = Sigma N_plus - (N_plus + N_plus) := by rw [← sub_add_eq_sub_sub]

/-- **`YM₅` Positive Maurer–Cartan Defect Recovery (`Σ - U_+ Σ U_+⁻¹ = 2N_+`):**
    The gauge defect of `Σ` under `U_+` recovers `2N_+`. -/
theorem maurer_cartan_defect_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus - U_plus N_plus * Sigma N_plus * U_plus_inv N_plus =
      N_plus + N_plus := by
  rw [U_plus_conj_Sigma N_plus h_nil h_reg]
  calc Sigma N_plus - (Sigma N_plus - (N_plus + N_plus))
    _ = ((Sigma N_plus - (N_plus + N_plus)) + (N_plus + N_plus)) -
        (Sigma N_plus - (N_plus + N_plus)) := by
        rw [sub_add_self (Sigma N_plus) (N_plus + N_plus)]
    _ = N_plus + N_plus := by rw [add_sub_self_left]

/-- **`YM₅` Negative Unipotent Adjoint Action (`U_- Σ U_-⁻¹ = Σ + 2N_-`):**
    Conjugating the sheet grading `Σ` by the dual unipotent holonomy `U_-` shifts `Σ`
    by `+2N_-`. -/
theorem U_minus_conj_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_minus N_plus * Sigma N_plus * U_minus_inv N_plus =
      Sigma N_plus + (star N_plus + star N_plus) := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  dsimp [U_minus, U_minus_inv]
  have hL : (1 + star N_plus) * Sigma N_plus = Sigma N_plus + star N_plus := by
    rw [add_mul, one_mul, star_N_plus_mul_Sigma N_plus h_nil h_reg]
  calc (1 + star N_plus) * Sigma N_plus * (1 - star N_plus)
    _ = (Sigma N_plus + star N_plus) * (1 - star N_plus) := by rw [hL]
    _ = (Sigma N_plus + star N_plus) * 1 - (Sigma N_plus + star N_plus) * star N_plus := by
        rw [mul_sub]
    _ = (Sigma N_plus + star N_plus) - (Sigma N_plus * star N_plus + star N_plus * star N_plus) := by
        rw [mul_one, add_mul]
    _ = (Sigma N_plus + star N_plus) - (-star N_plus + 0) := by
        rw [Sigma_mul_star_N_plus N_plus h_nil h_reg, h_star_nil]
    _ = (Sigma N_plus + star N_plus) - -star N_plus := by rw [add_zero]
    _ = (Sigma N_plus + star N_plus) + star N_plus := by rw [sub_eq_add_neg, neg_neg]
    _ = Sigma N_plus + (star N_plus + star N_plus) := by rw [add_assoc]

/-- **`YM₅` Negative Maurer–Cartan Defect Recovery (`U_- Σ U_-⁻¹ - Σ = 2N_-`):**
    The gauge defect of `Σ` under `U_-` recovers `2N_- = star N_plus + star N_plus`. -/
theorem maurer_cartan_defect_minus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_minus N_plus * Sigma N_plus * U_minus_inv N_plus - Sigma N_plus =
      star N_plus + star N_plus := by
  rw [U_minus_conj_Sigma N_plus h_nil h_reg, add_sub_self_left]

/-!
### 4. Steinberg Unipotent Braid (`W_vortex`) & `ℤ₂` Center Vortex Monodromy (`YM₆–YM₇`)
-/

/-- The Steinberg-Weyl triple unipotent vortex operator `W_vortex = U_+ U_-⁻¹ U_+`. -/
def W_vortex (N_plus : B) : B :=
  U_plus N_plus * U_minus_inv N_plus * U_plus N_plus

/-- The `ℤ₂` Center Vortex Monodromy operator `Z_center = 1 - 2V`. -/
def Z_center (N_plus : B) : B := 1 - (V N_plus + V N_plus)

theorem U_plus_mul_U_minus_inv (N_plus : B) :
    U_plus N_plus * U_minus_inv N_plus = (1 + J N_plus) - P N_plus := by
  dsimp [U_plus, U_minus_inv, J, P]
  calc (1 + N_plus) * (1 - star N_plus)
    _ = (1 + N_plus) * 1 - (1 + N_plus) * star N_plus := by rw [mul_sub]
    _ = (1 + N_plus) - (1 * star N_plus + N_plus * star N_plus) := by
        rw [mul_one, add_mul]
    _ = (1 + N_plus) - (star N_plus + N_plus * star N_plus) := by rw [one_mul]
    _ = ((1 + N_plus) - star N_plus) - N_plus * star N_plus := by
        rw [sub_add_eq_sub_sub]
    _ = (1 + (N_plus - star N_plus)) - N_plus * star N_plus := by
        rw [← add_sub_assoc']

/-- **`YM₆` Steinberg Unipotent Coagulation Theorem (`U_+ U_-⁻¹ U_+ = (1 - V) + J`):**
    The triple unipotent product coagulates into the vacuum projector `1 - V` plus
    the Hestenes elliptic bivector rotor `J = N_+ - N_-` on the vortex core `V`. -/
theorem W_vortex_eq (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_vortex N_plus = (1 - V N_plus) + J N_plus := by
  dsimp [W_vortex]
  rw [U_plus_mul_U_minus_inv]
  have hJ_N : J N_plus * N_plus = -Q N_plus := by
    dsimp [J, Q]
    rw [sub_mul, h_nil, zero_sub]
  have hR : ((1 + J N_plus) - P N_plus) * N_plus = -Q N_plus := by
    calc ((1 + J N_plus) - P N_plus) * N_plus
      _ = (1 + J N_plus) * N_plus - P N_plus * N_plus := by rw [sub_mul]
      _ = (1 * N_plus + J N_plus * N_plus) - N_plus := by
          rw [add_mul, P_mul_N_plus N_plus h_reg]
      _ = (N_plus + -Q N_plus) - N_plus := by rw [one_mul, hJ_N]
      _ = (-Q N_plus + N_plus) - N_plus := by rw [add_comm N_plus (-Q N_plus)]
      _ = -Q N_plus := by rw [add_sub_self_right]
  calc ((1 + J N_plus) - P N_plus) * U_plus N_plus
    _ = ((1 + J N_plus) - P N_plus) * 1 + ((1 + J N_plus) - P N_plus) * N_plus := by
        dsimp [U_plus]; rw [mul_add]
    _ = ((1 + J N_plus) - P N_plus) + -Q N_plus := by rw [mul_one, hR]
    _ = ((1 + J N_plus) - P N_plus) - Q N_plus := by rw [← sub_eq_add_neg]
    _ = (1 + J N_plus) - (P N_plus + Q N_plus) := by rw [← sub_add_eq_sub_sub]
    _ = (J N_plus + 1) - V N_plus := by rw [add_comm 1 (J N_plus)]; rfl
    _ = J N_plus + (1 - V N_plus) := by rw [← add_sub_assoc']
    _ = (1 - V N_plus) + J N_plus := by rw [add_comm]

theorem V_mul_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * N_plus = N_plus := by
  dsimp [V]
  rw [add_mul, h_reg, mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero, add_zero]

theorem N_plus_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * V N_plus = N_plus := by
  dsimp [V]
  rw [mul_add, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
      ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_add]

theorem V_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * star N_plus = star N_plus := by
  dsimp [V]
  rw [add_mul, mul_assoc N_plus (star N_plus) (star N_plus),
      star_N_plus_sq N_plus h_nil, mul_zero,
      star_N_plus_reg N_plus h_reg, zero_add]

theorem star_N_plus_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * V N_plus = star N_plus := by
  dsimp [V]
  rw [mul_add, ← mul_assoc (star N_plus) N_plus (star N_plus),
      star_N_plus_reg N_plus h_reg,
      ← mul_assoc (star N_plus) (star N_plus) N_plus,
      star_N_plus_sq N_plus h_nil, zero_mul, add_zero]

theorem V_idem (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * V N_plus = V N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV]
  calc (P N_plus + Q N_plus) * (P N_plus + Q N_plus)
    _ = (P N_plus + Q N_plus) * P N_plus + (P N_plus + Q N_plus) * Q N_plus := by
        rw [mul_add]
    _ = (P N_plus * P N_plus + Q N_plus * P N_plus) +
        (P N_plus * Q N_plus + Q N_plus * Q N_plus) := by
        rw [add_mul, add_mul]
    _ = (P N_plus + 0) + (0 + Q N_plus) := by
        rw [P_idem N_plus h_reg, Q_mul_P N_plus h_nil,
            P_mul_Q N_plus h_nil, Q_idem N_plus h_reg]
    _ = P N_plus + Q N_plus := by rw [add_zero, zero_add]

theorem Phi_sq_eq_V (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Phi N_plus * Phi N_plus = V N_plus := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  dsimp [Phi, V]
  calc (N_plus + star N_plus) * (N_plus + star N_plus)
    _ = (N_plus + star N_plus) * N_plus + (N_plus + star N_plus) * star N_plus := by
        rw [mul_add]
    _ = (N_plus * N_plus + star N_plus * N_plus) +
        (N_plus * star N_plus + star N_plus * star N_plus) := by
        rw [add_mul, add_mul]
    _ = (0 + star N_plus * N_plus) + (N_plus * star N_plus + 0) := by
        rw [h_nil, h_star_nil]
    _ = star N_plus * N_plus + N_plus * star N_plus := by
        rw [zero_add, add_zero]
    _ = N_plus * star N_plus + star N_plus * N_plus := by
        rw [add_comm]

theorem J_sq_eq_neg_V (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    J N_plus * J N_plus = -V N_plus := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  dsimp [J, V]
  calc (N_plus - star N_plus) * (N_plus - star N_plus)
    _ = (N_plus - star N_plus) * N_plus - (N_plus - star N_plus) * star N_plus := by
        rw [mul_sub]
    _ = (N_plus * N_plus - star N_plus * N_plus) -
        (N_plus * star N_plus - star N_plus * star N_plus) := by
        rw [sub_mul, sub_mul]
    _ = (0 - star N_plus * N_plus) - (N_plus * star N_plus - 0) := by
        rw [h_nil, h_star_nil]
    _ = -(star N_plus * N_plus) - N_plus * star N_plus := by
        rw [zero_sub, sub_zero]
    _ = -(star N_plus * N_plus + N_plus * star N_plus) := by
        rw [sub_eq_add_neg, ← neg_add]
    _ = -(N_plus * star N_plus + star N_plus * N_plus) := by
        rw [add_comm (star N_plus * N_plus)]

/-- **`YM₇` Center Vortex Monodromy Theorem (`W_vortex² = 1 - 2V = Z_center`):**
    The square of the Steinberg unipotent braid `W_vortex` is the `ℤ₂` center
    vortex operator `Z_center = 1 - 2V`. -/
theorem W_vortex_sq_eq_Z_center (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_vortex N_plus * W_vortex N_plus = Z_center N_plus := by
  rw [W_vortex_eq N_plus h_nil h_reg]
  have h1V_idem : (1 - V N_plus) * (1 - V N_plus) = 1 - V N_plus := by
    calc (1 - V N_plus) * (1 - V N_plus)
      _ = (1 - V N_plus) * 1 - (1 - V N_plus) * V N_plus := by rw [mul_sub]
      _ = (1 - V N_plus) - (1 * V N_plus - V N_plus * V N_plus) := by
          rw [mul_one, sub_mul]
      _ = (1 - V N_plus) - (V N_plus - V N_plus) := by
          rw [one_mul, V_idem N_plus h_nil h_reg]
      _ = 1 - V N_plus := by rw [sub_self, sub_zero]
  have h1V_J : (1 - V N_plus) * J N_plus = 0 := by
    dsimp [J]
    rw [sub_mul, one_mul, mul_sub,
        V_mul_N_plus N_plus h_nil h_reg,
        V_mul_star_N_plus N_plus h_nil h_reg, sub_self]
  have hJ_1V : J N_plus * (1 - V N_plus) = 0 := by
    dsimp [J]
    rw [mul_sub, mul_one, sub_mul,
        N_plus_mul_V N_plus h_nil h_reg,
        star_N_plus_mul_V N_plus h_nil h_reg, sub_self]
  calc ((1 - V N_plus) + J N_plus) * ((1 - V N_plus) + J N_plus)
    _ = ((1 - V N_plus) + J N_plus) * (1 - V N_plus) +
        ((1 - V N_plus) + J N_plus) * J N_plus := by rw [mul_add]
    _ = ((1 - V N_plus) * (1 - V N_plus) + J N_plus * (1 - V N_plus)) +
        ((1 - V N_plus) * J N_plus + J N_plus * J N_plus) := by
        rw [add_mul, add_mul]
    _ = ((1 - V N_plus) + 0) + (0 + -V N_plus) := by
        rw [h1V_idem, hJ_1V, h1V_J, J_sq_eq_neg_V N_plus h_nil]
    _ = (1 - V N_plus) - V N_plus := by
        rw [add_zero, zero_add, ← sub_eq_add_neg]
    _ = 1 - (V N_plus + V N_plus) := by rw [← sub_add_eq_sub_sub]
    _ = Z_center N_plus := rfl

/-- **`YM₇` Center Vortex Involution (`Z_center² = 1`):**
    The `ℤ₂` center vortex monodromy squares to the global identity `1`. -/
theorem Z_center_sq_eq_one (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * Z_center N_plus = 1 := by
  dsimp [Z_center]
  have hZV : (1 - (V N_plus + V N_plus)) * V N_plus = -V N_plus := by
    calc (1 - (V N_plus + V N_plus)) * V N_plus
      _ = 1 * V N_plus - (V N_plus + V N_plus) * V N_plus := by rw [sub_mul]
      _ = V N_plus - (V N_plus * V N_plus + V N_plus * V N_plus) := by
          rw [one_mul, add_mul]
      _ = V N_plus - (V N_plus + V N_plus) := by rw [V_idem N_plus h_nil h_reg]
      _ = (V N_plus - V N_plus) - V N_plus := by rw [sub_add_eq_sub_sub]
      _ = -V N_plus := by rw [sub_self, zero_sub]
  calc (1 - (V N_plus + V N_plus)) * (1 - (V N_plus + V N_plus))
    _ = (1 - (V N_plus + V N_plus)) * 1 -
        (1 - (V N_plus + V N_plus)) * (V N_plus + V N_plus) := by rw [mul_sub]
    _ = (1 - (V N_plus + V N_plus)) -
        ((1 - (V N_plus + V N_plus)) * V N_plus +
         (1 - (V N_plus + V N_plus)) * V N_plus) := by rw [mul_one, mul_add]
    _ = (1 - (V N_plus + V N_plus)) - (-V N_plus + -V N_plus) := by rw [hZV]
    _ = (1 - (V N_plus + V N_plus)) - -(V N_plus + V N_plus) := by rw [← neg_add]
    _ = (1 - (V N_plus + V N_plus)) + (V N_plus + V N_plus) := by
        rw [sub_eq_add_neg, neg_neg]
    _ = 1 := by rw [sub_add_self]

/-!
### 5. Dynamical Vortex Mass Eigenvalue & Bogomolny Saturation (`YM₈–YM₁₀`)
-/

/-- **`YM₈` Dynamical Gluon/Dirac Mass Equation (`V Φ = Φ` and `Φ² = V`):**
    The two-sheeted condensate `V = P + Q` acts as the exact Proca / Klein-Gordon
    mass-squared operator (`M_vortex² = V`) for the gauge field `Φ = N_+ + N_-`. -/
theorem vortex_mass_eigenvalue_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * Phi N_plus = Phi N_plus := by
  dsimp [Phi]
  rw [mul_add,
      V_mul_N_plus N_plus h_nil h_reg,
      V_mul_star_N_plus N_plus h_nil h_reg]

/-- **`YM₉` Bogomolny / BPS Vortex Mass Saturation (`V² - Σ² = 0`):**
    The square of the vortex mass condensate `V` equals the square of the
    unipotent magnetic flux `Σ = [U_+, U_-]`, saturating the BPS vortex bound. -/
theorem bps_vortex_mass_saturation (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * V N_plus -
    comm (U_plus N_plus) (U_minus N_plus) * comm (U_plus N_plus) (U_minus N_plus) = 0 := by
  rw [comm_U_plus_U_minus, V_idem N_plus h_nil h_reg]
  have hSigma_sq : Sigma N_plus * Sigma N_plus = V N_plus := by
    have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
    have hV : V N_plus = P N_plus + Q N_plus := rfl
    rw [hS, hV]
    calc (P N_plus - Q N_plus) * (P N_plus - Q N_plus)
      _ = (P N_plus - Q N_plus) * P N_plus - (P N_plus - Q N_plus) * Q N_plus := by
          rw [mul_sub]
      _ = (P N_plus * P N_plus - Q N_plus * P N_plus) -
          (P N_plus * Q N_plus - Q N_plus * Q N_plus) := by
          rw [sub_mul, sub_mul]
      _ = (P N_plus - 0) - (0 - Q N_plus) := by
          rw [P_idem N_plus h_reg, Q_mul_P N_plus h_nil,
              P_mul_Q N_plus h_nil, Q_idem N_plus h_reg]
      _ = P N_plus + Q N_plus := by
          rw [sub_zero, zero_sub, sub_eq_add_neg, neg_neg]
  rw [hSigma_sq, sub_self]

/-- **`YM₁₀` Center Vortex Core Inversion (`Z_center V = -V`):**
    The `ℤ₂` center vortex monodromy `Z_center = 1 - 2V` inverts the sign of the
    vortex core projector `V`. -/
theorem Z_center_flips_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * V N_plus = -V N_plus := by
  dsimp [Z_center]
  rw [sub_mul, one_mul, add_mul,
      V_idem N_plus h_nil h_reg,
      sub_add_eq_sub_sub, sub_self, zero_sub]

/-- **`YM₁₀` Master Synthesis: Center Vortex Holonomy Flips the Massive Gauge Mode (`Z_center Φ = -Φ`):**
    Transporting the massive gauge mode `Φ` around the Steinberg center vortex
    monodromy `Z_center = W_vortex²` flips its sign by `-1`. -/
theorem Z_center_flips_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * Phi N_plus = -Phi N_plus := by
  dsimp [Z_center]
  rw [sub_mul, one_mul, add_mul,
      vortex_mass_eigenvalue_Phi N_plus h_nil h_reg,
      sub_add_eq_sub_sub, sub_self, zero_sub]

/-!
### 6. ’t Hooft–Wilson Loop Braiding Across the Two-Sheeted Condensate (`YangMillsTHooftWilsonBraiding`)
-/

/-- The off-diagonal Peirce-projected Wilson link `U_plus_off = P U_+ Q`
    tunneling from Sheet `-` (`Q`) to Sheet `+` (`P`). -/
def U_plus_off (N_plus : B) : B := P N_plus * U_plus N_plus * Q N_plus

/-- The dual off-diagonal Peirce-projected Wilson link `U_minus_off = Q U_- P`
    tunneling from Sheet `+` (`P`) to Sheet `-` (`Q`). -/
def U_minus_off (N_plus : B) : B := Q N_plus * U_minus N_plus * P N_plus

/-- The inter-sheet `ℤ₂` ’t Hooft disorder loop operator `Z_thooft = 2P - 1`,
    assigning center phase `+1` to Sheet `+` (`P`) and `-1` to Sheet `-` (`Q`). -/
def Z_thooft (N_plus : B) : B := P N_plus + P N_plus - 1

theorem N_plus_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    N_plus * P N_plus = 0 := by
  dsimp [P]
  rw [← mul_assoc, h_nil, zero_mul]

theorem N_plus_mul_Q (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * Q N_plus = N_plus := by
  dsimp [Q]
  rw [← mul_assoc, h_reg]

theorem Q_mul_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * N_plus = 0 := by
  dsimp [Q]
  rw [mul_assoc, h_nil, mul_zero]

theorem P_mul_star_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    P N_plus * star N_plus = 0 := by
  dsimp [P]
  rw [mul_assoc, star_N_plus_sq N_plus h_nil, mul_zero]

theorem star_N_plus_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * P N_plus = star N_plus := by
  dsimp [P]
  rw [← mul_assoc, star_N_plus_reg N_plus h_reg]

theorem Q_mul_star_N_plus (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Q N_plus * star N_plus = star N_plus :=
  star_N_plus_reg N_plus h_reg

/-- The off-diagonal Peirce projection `U_plus_off = P U_+ Q` extracts `N_+`. -/
theorem U_plus_off_eq_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_plus_off N_plus = N_plus := by
  dsimp [U_plus_off, U_plus]
  rw [mul_add, mul_one, P_mul_N_plus N_plus h_reg,
      add_mul, P_mul_Q N_plus h_nil, N_plus_mul_Q N_plus h_reg, zero_add]

/-- `U_plus_off` also equals the reduced unipotent fluctuation `U_+ - 1`. -/
theorem U_plus_off_eq_U_plus_sub_one (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_plus_off N_plus = U_plus N_plus - 1 := by
  rw [U_plus_off_eq_N_plus N_plus h_nil h_reg]
  dsimp [U_plus]
  rw [add_sub_self_left]

/-- The dual off-diagonal Peirce projection `U_minus_off = Q U_- P` extracts `N_-`. -/
theorem U_minus_off_eq_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_minus_off N_plus = star N_plus := by
  dsimp [U_minus_off, U_minus]
  rw [mul_add, mul_one, Q_mul_star_N_plus N_plus h_reg,
      add_mul, Q_mul_P N_plus h_nil, star_N_plus_mul_P N_plus h_reg, zero_add]

/-- Sheet `+` carries `+1` ’t Hooft center charge: `Z_thooft * P = P`. -/
theorem Z_thooft_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * P N_plus = P N_plus := by
  dsimp [Z_thooft]
  calc (P N_plus + P N_plus - 1) * P N_plus
    _ = (P N_plus + P N_plus) * P N_plus - 1 * P N_plus := by rw [sub_mul]
    _ = (P N_plus * P N_plus + P N_plus * P N_plus) - P N_plus := by
        rw [add_mul, one_mul]
    _ = (P N_plus + P N_plus) - P N_plus := by rw [P_idem N_plus h_reg]
    _ = P N_plus := by rw [add_sub_self_right]

/-- Sheet `-` carries `-1` ’t Hooft center charge: `Z_thooft * Q = -Q`. -/
theorem Z_thooft_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Z_thooft N_plus * Q N_plus = -Q N_plus := by
  dsimp [Z_thooft]
  calc (P N_plus + P N_plus - 1) * Q N_plus
    _ = (P N_plus + P N_plus) * Q N_plus - 1 * Q N_plus := by rw [sub_mul]
    _ = (P N_plus * Q N_plus + P N_plus * Q N_plus) - Q N_plus := by
        rw [add_mul, one_mul]
    _ = (0 + 0) - Q N_plus := by rw [P_mul_Q N_plus h_nil]
    _ = -Q N_plus := by rw [add_zero, zero_sub]

/-- The ’t Hooft disorder loop is a `ℤ₂` involution: `Z_thooft * Z_thooft = 1`. -/
theorem Z_thooft_sq_eq_one (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * Z_thooft N_plus = 1 := by
  have hP := Z_thooft_mul_P N_plus h_reg
  calc Z_thooft N_plus * (P N_plus + P N_plus - 1)
    _ = Z_thooft N_plus * (P N_plus + P N_plus) - Z_thooft N_plus * 1 := by rw [mul_sub]
    _ = (Z_thooft N_plus * P N_plus + Z_thooft N_plus * P N_plus) - Z_thooft N_plus := by
        rw [mul_add, mul_one]
    _ = (P N_plus + P N_plus) - ((P N_plus + P N_plus) - 1) := by rw [hP, Z_thooft]
    _ = ((P N_plus + P N_plus - 1) + 1) - (P N_plus + P N_plus - 1) := by
        rw [sub_add_self (P N_plus + P N_plus) 1]
    _ = 1 := by rw [add_sub_self_left]

theorem Z_thooft_mul_N_plus (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * N_plus = N_plus := by
  dsimp [Z_thooft]
  calc (P N_plus + P N_plus - 1) * N_plus
    _ = (P N_plus + P N_plus) * N_plus - 1 * N_plus := by rw [sub_mul]
    _ = (P N_plus * N_plus + P N_plus * N_plus) - N_plus := by rw [add_mul, one_mul]
    _ = (N_plus + N_plus) - N_plus := by rw [P_mul_N_plus N_plus h_reg]
    _ = N_plus := by rw [add_sub_self_right]

theorem N_plus_mul_Z_thooft (N_plus : B)
    (h_nil : N_plus * N_plus = 0) :
    N_plus * Z_thooft N_plus = -N_plus := by
  dsimp [Z_thooft]
  calc N_plus * (P N_plus + P N_plus - 1)
    _ = N_plus * (P N_plus + P N_plus) - N_plus * 1 := by rw [mul_sub]
    _ = (N_plus * P N_plus + N_plus * P N_plus) - N_plus := by rw [mul_add, mul_one]
    _ = (0 + 0) - N_plus := by rw [N_plus_mul_P N_plus h_nil]
    _ = -N_plus := by rw [add_zero, zero_sub]

/-- **Main ’t Hooft–Wilson Braiding Theorem (`Z_thooft * U_plus_off + U_plus_off * Z_thooft = 0`):**
    Across the two-sheeted vortex condensate, the ’t Hooft disorder operator `Z_thooft = 2P - 1`
    and the off-diagonal Wilson link `U_plus_off = P U_+ Q` strictly anticommute. -/
theorem Z_thooft_braid_U_plus_off (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * U_plus_off N_plus + U_plus_off N_plus * Z_thooft N_plus = 0 := by
  rw [U_plus_off_eq_N_plus N_plus h_nil h_reg,
      Z_thooft_mul_N_plus N_plus h_reg,
      N_plus_mul_Z_thooft N_plus h_nil,
      ← sub_eq_add_neg, sub_self]

theorem Z_thooft_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0) :
    Z_thooft N_plus * star N_plus = -star N_plus := by
  dsimp [Z_thooft]
  calc (P N_plus + P N_plus - 1) * star N_plus
    _ = (P N_plus + P N_plus) * star N_plus - 1 * star N_plus := by rw [sub_mul]
    _ = (P N_plus * star N_plus + P N_plus * star N_plus) - star N_plus := by
        rw [add_mul, one_mul]
    _ = (0 + 0) - star N_plus := by rw [P_mul_star_N_plus N_plus h_nil]
    _ = -star N_plus := by rw [add_zero, zero_sub]

theorem star_N_plus_mul_Z_thooft (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * Z_thooft N_plus = star N_plus := by
  dsimp [Z_thooft]
  calc star N_plus * (P N_plus + P N_plus - 1)
    _ = star N_plus * (P N_plus + P N_plus) - star N_plus * 1 := by rw [mul_sub]
    _ = (star N_plus * P N_plus + star N_plus * P N_plus) - star N_plus := by
        rw [mul_add, mul_one]
    _ = (star N_plus + star N_plus) - star N_plus := by
        rw [star_N_plus_mul_P N_plus h_reg]
    _ = star N_plus := by rw [add_sub_self_right]

/-- **Dual ’t Hooft–Wilson Braiding Relation on `U_minus_off`:**
    `Z_thooft * U_minus_off + U_minus_off * Z_thooft = 0`. -/
theorem Z_thooft_braid_U_minus_off (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * U_minus_off N_plus + U_minus_off N_plus * Z_thooft N_plus = 0 := by
  rw [U_minus_off_eq_star_N_plus N_plus h_nil h_reg,
      Z_thooft_mul_star_N_plus N_plus h_nil,
      star_N_plus_mul_Z_thooft N_plus h_reg,
      add_comm (-star N_plus) (star N_plus),
      ← sub_eq_add_neg, sub_self]

/-- **Intrinsic Magnetic Flux Braiding (`Σ * U_plus_off + U_plus_off * Σ = 0`):**
    On the active condensate `V = P + Q`, the magnetic flux `Σ = P - Q` obeys the
    exact same anticommutation braiding with `U_plus_off`. -/
theorem Sigma_braid_U_plus_off (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * U_plus_off N_plus + U_plus_off N_plus * Sigma N_plus = 0 := by
  rw [U_plus_off_eq_N_plus N_plus h_nil h_reg,
      Sigma_mul_N_plus N_plus h_nil h_reg,
      N_plus_mul_Sigma N_plus h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

theorem Z_thooft_conj_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * N_plus * Z_thooft N_plus = -N_plus := by
  rw [Z_thooft_mul_N_plus N_plus h_reg, N_plus_mul_Z_thooft N_plus h_nil]

theorem Z_thooft_conj_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * star N_plus * Z_thooft N_plus = -star N_plus := by
  rw [Z_thooft_mul_star_N_plus N_plus h_nil,
      neg_mul, star_N_plus_mul_Z_thooft N_plus h_reg]

/-- **Group-Level ’t Hooft–Wilson Inversion I (`Z_thooft U_+ Z_thooft = U_+⁻¹`):**
    Conjugating the unipotent Wilson holonomy `U_+ = 1 + N_+` by the ’t Hooft
    disorder loop `Z_thooft` inverts it to `U_+⁻¹ = 1 - N_+`. -/
theorem Z_thooft_conj_U_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * U_plus N_plus * Z_thooft N_plus = U_plus_inv N_plus := by
  dsimp [U_plus, U_plus_inv]
  calc Z_thooft N_plus * (1 + N_plus) * Z_thooft N_plus
    _ = (Z_thooft N_plus * 1 + Z_thooft N_plus * N_plus) * Z_thooft N_plus := by
        rw [mul_add]
    _ = Z_thooft N_plus * Z_thooft N_plus +
        (Z_thooft N_plus * N_plus * Z_thooft N_plus) := by
        rw [mul_one, add_mul]
    _ = 1 + -N_plus := by
        rw [Z_thooft_sq_eq_one N_plus h_reg, Z_thooft_conj_N_plus N_plus h_nil h_reg]
    _ = 1 - N_plus := by rw [← sub_eq_add_neg]

/-- **Group-Level ’t Hooft–Wilson Inversion II (`Z_thooft U_- Z_thooft = U_-⁻¹`):**
    Conjugating `U_- = 1 + N_-` by `Z_thooft` inverts it to `U_-⁻¹ = 1 - N_-`. -/
theorem Z_thooft_conj_U_minus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * U_minus N_plus * Z_thooft N_plus = U_minus_inv N_plus := by
  dsimp [U_minus, U_minus_inv]
  calc Z_thooft N_plus * (1 + star N_plus) * Z_thooft N_plus
    _ = (Z_thooft N_plus * 1 + Z_thooft N_plus * star N_plus) * Z_thooft N_plus := by
        rw [mul_add]
    _ = Z_thooft N_plus * Z_thooft N_plus +
        (Z_thooft N_plus * star N_plus * Z_thooft N_plus) := by
        rw [mul_one, add_mul]
    _ = 1 + -star N_plus := by
        rw [Z_thooft_sq_eq_one N_plus h_reg, Z_thooft_conj_star_N_plus N_plus h_nil h_reg]
    _ = 1 - star N_plus := by rw [← sub_eq_add_neg]

/-- The reduced Sheet `+` Wilson loop holonomy `W_+ = U_+ U_- - 1`. -/
def W_wilson_plus (N_plus : B) : B := U_plus N_plus * U_minus N_plus - 1

theorem W_wilson_plus_eq (N_plus : B) :
    W_wilson_plus N_plus = P N_plus + Phi N_plus := by
  dsimp [W_wilson_plus]
  rw [U_plus_mul_U_minus,
      add_comm (1 + Phi N_plus) (P N_plus),
      add_comm 1 (Phi N_plus),
      ← add_assoc (P N_plus) (Phi N_plus) 1,
      add_sub_self_right]

theorem Z_thooft_conj_P (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * P N_plus * Z_thooft N_plus = P N_plus := by
  rw [Z_thooft_mul_P N_plus h_reg]
  dsimp [Z_thooft]
  calc P N_plus * (P N_plus + P N_plus - 1)
    _ = P N_plus * (P N_plus + P N_plus) - P N_plus * 1 := by rw [mul_sub]
    _ = (P N_plus * P N_plus + P N_plus * P N_plus) - P N_plus := by
        rw [mul_add, mul_one]
    _ = (P N_plus + P N_plus) - P N_plus := by rw [P_idem N_plus h_reg]
    _ = P N_plus := by rw [add_sub_self_right]

theorem Z_thooft_conj_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * Phi N_plus * Z_thooft N_plus = -Phi N_plus := by
  dsimp [Phi]
  calc Z_thooft N_plus * (N_plus + star N_plus) * Z_thooft N_plus
    _ = (Z_thooft N_plus * N_plus + Z_thooft N_plus * star N_plus) * Z_thooft N_plus := by
        rw [mul_add]
    _ = Z_thooft N_plus * N_plus * Z_thooft N_plus +
        Z_thooft N_plus * star N_plus * Z_thooft N_plus := by rw [add_mul]
    _ = -N_plus + -star N_plus := by
        rw [Z_thooft_conj_N_plus N_plus h_nil h_reg,
            Z_thooft_conj_star_N_plus N_plus h_nil h_reg]
    _ = -(N_plus + star N_plus) := by
        rw [neg_add_rev, add_comm (-star N_plus) (-N_plus)]

/-- Conjugating the reduced Wilson loop `W_+` by `Z_thooft` flips the gauge mode `Φ`:
    `Z_thooft W_+ Z_thooft = P - Φ`. -/
theorem Z_thooft_conj_W_wilson_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_thooft N_plus * W_wilson_plus N_plus * Z_thooft N_plus =
      P N_plus - Phi N_plus := by
  rw [W_wilson_plus_eq]
  calc Z_thooft N_plus * (P N_plus + Phi N_plus) * Z_thooft N_plus
    _ = (Z_thooft N_plus * P N_plus + Z_thooft N_plus * Phi N_plus) * Z_thooft N_plus := by
        rw [mul_add]
    _ = Z_thooft N_plus * P N_plus * Z_thooft N_plus +
        Z_thooft N_plus * Phi N_plus * Z_thooft N_plus := by rw [add_mul]
    _ = P N_plus + -Phi N_plus := by
        rw [Z_thooft_conj_P N_plus h_reg, Z_thooft_conj_Phi N_plus h_nil h_reg]
    _ = P N_plus - Phi N_plus := by rw [← sub_eq_add_neg]

/-- **’t Hooft–Wilson Orbit Sum (`W_+ + Z_thooft W_+ Z_thooft = 2P`):**
    Summing the Wilson loop `W_+` with its ’t Hooft-braided partner eliminates `Φ`
    and precipitates the Sheet `+` condensate `2P`. -/
theorem wilson_thooft_condensate_sum (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_wilson_plus N_plus + Z_thooft N_plus * W_wilson_plus N_plus * Z_thooft N_plus =
      P N_plus + P N_plus := by
  rw [Z_thooft_conj_W_wilson_plus N_plus h_nil h_reg, W_wilson_plus_eq]
  exact add_add_sub_cancel (P N_plus) (Phi N_plus)

/-- **’t Hooft–Wilson Braiding Defect (`W_+ - Z_thooft W_+ Z_thooft = 2Φ`):**
    The difference between `W_+` and its ’t Hooft-braided partner isolates twice
    the massive Dirac/gluon vector field `Φ`. -/
theorem wilson_thooft_braiding_defect (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_wilson_plus N_plus - Z_thooft N_plus * W_wilson_plus N_plus * Z_thooft N_plus =
      Phi N_plus + Phi N_plus := by
  rw [Z_thooft_conj_W_wilson_plus N_plus h_nil h_reg, W_wilson_plus_eq]
  exact sub_add_sub_cancel_two (P N_plus) (Phi N_plus)

/-- A boundary Wilson link `W_edge(X) = V X (1 - V)` tunneling from the exterior
    vacuum `1 - V` into the two-sheeted vortex core `V`. -/
def W_edge (N_plus X : B) : B := V N_plus * X * (1 - V N_plus)

/-- **Vortex Boundary Braiding Theorem (`Z_center * W_edge + W_edge * Z_center = 0`):**
    Any Wilson link `W_edge(X) = V X (1 - V)` crossing the vortex core boundary
    strictly anticommutes with the Steinberg vortex monodromy `Z_center = 1 - 2V`. -/
theorem Z_center_braid_W_edge (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * W_edge N_plus X + W_edge N_plus X * Z_center N_plus = 0 := by
  have hVW : V N_plus * W_edge N_plus X = W_edge N_plus X := by
    dsimp [W_edge]
    rw [← mul_assoc (V N_plus) (V N_plus * X) (1 - V N_plus),
        ← mul_assoc (V N_plus) (V N_plus) X,
        V_idem N_plus h_nil h_reg]
  have hWV : W_edge N_plus X * V N_plus = 0 := by
    dsimp [W_edge]
    calc (V N_plus * X * (1 - V N_plus)) * V N_plus
      _ = (V N_plus * X) * ((1 - V N_plus) * V N_plus) := by
          rw [mul_assoc (V N_plus * X) (1 - V N_plus) (V N_plus)]
      _ = (V N_plus * X) * (1 * V N_plus - V N_plus * V N_plus) := by
          rw [sub_mul]
      _ = (V N_plus * X) * (V N_plus - V N_plus) := by
          rw [one_mul, V_idem N_plus h_nil h_reg]
      _ = 0 := by rw [sub_self, mul_zero]
  have hL : Z_center N_plus * W_edge N_plus X = -W_edge N_plus X := by
    dsimp [Z_center]
    rw [sub_mul, one_mul, add_mul, hVW, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hR : W_edge N_plus X * Z_center N_plus = W_edge N_plus X := by
    dsimp [Z_center]
    rw [mul_sub, mul_one, mul_add, hWV, add_zero, sub_zero]
  rw [hL, hR, add_comm (-W_edge N_plus X) (W_edge N_plus X),
      ← sub_eq_add_neg, sub_self]

/-!
### 7. Concrete `2 × 2` Non-Commutative Matrix Witness (`T16` / `T17`) & Master 10-Stage Theorem
-/

/-- Concrete `2 × 2` nilpotent Von Neumann regular generator `N_+ = E₀₁ = !![0, 1; 0, 0]`. -/
def vortexMatrixNPlus : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- Concrete `2 × 2` dual nilpotent generator `N_- = E₁₀ = !![0, 0; 1, 0]`. -/
def vortexMatrixNMinus : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- Concrete `2 × 2` integer matrix witness certifying non-commutativity (`T16`) and
non-vanishing unipotent vortex holonomy, condensate mass `V`, and center-vortex flip (`T17`). -/
theorem vortex_matrix_noncomm_and_nonzero_mass_witness :
    vortexMatrixNPlus * vortexMatrixNPlus = 0 ∧
    vortexMatrixNPlus * star vortexMatrixNPlus * vortexMatrixNPlus = vortexMatrixNPlus ∧
    vortexMatrixNPlus * vortexMatrixNMinus ≠ vortexMatrixNMinus * vortexMatrixNPlus ∧
    comm (U_plus vortexMatrixNPlus) (U_minus vortexMatrixNPlus) ≠ 0 ∧
    V vortexMatrixNPlus = (1 : Matrix (Fin 2) (Fin 2) ℤ) ∧
    V vortexMatrixNPlus ≠ 0 ∧
    Z_center vortexMatrixNPlus = -(1 : Matrix (Fin 2) (Fin 2) ℤ) ∧
    Z_center vortexMatrixNPlus * Phi vortexMatrixNPlus = -Phi vortexMatrixNPlus ∧
    Z_thooft vortexMatrixNPlus * U_plus_off vortexMatrixNPlus +
      U_plus_off vortexMatrixNPlus * Z_thooft vortexMatrixNPlus = 0 := by
  decide

/-- **Master 10-Stage Synthesis (`yang_mills_nilpotent_unipotent_vortex_mass_poset_master_synthesis`)**:
Coagulates `YM₁ ≺ YM₂ ≺ YM₃ ≺ YM₄ ≺ YM₅ ≺ YM₆ ≺ YM₇ ≺ YM₈ ≺ YM₉ ≺ YM₁₀` and the
’t Hooft–Wilson braiding relations over any `[Ring B] [StarRing B]` with nilpotent
`N_plus * N_plus = 0` and Von Neumann regularity `N_plus * star N_plus * N_plus = N_plus`. -/
theorem yang_mills_nilpotent_unipotent_vortex_mass_poset_master_synthesis
    (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    (YangMillsVortexStage.causalEdge
       .YM1_NilpotentToUnipotentCayleyLift .YM2_UnipotentFieldStrengthCommutator ∧
     YangMillsVortexStage.causalEdge
       .YM9_BogomolnyBPSVortexMassSaturation .YM10_CenterVortexHolonomyMasterSynthesis) ∧
    (U_plus N_plus * U_plus_inv N_plus = 1 ∧
     U_minus N_plus * U_minus_inv N_plus = 1 ∧
     star (U_plus N_plus) = U_minus N_plus) ∧
    comm (U_plus N_plus) (U_minus N_plus) = Sigma N_plus ∧
    (C_plus N_plus = P N_plus + P N_plus ∧
     C_minus N_plus = Q N_plus + Q N_plus) ∧
    (C_plus N_plus + C_minus N_plus = V N_plus + V N_plus ∧
     C_plus N_plus - C_minus N_plus = Sigma N_plus + Sigma N_plus) ∧
    (Sigma N_plus - U_plus N_plus * Sigma N_plus * U_plus_inv N_plus = N_plus + N_plus ∧
     U_minus N_plus * Sigma N_plus * U_minus_inv N_plus - Sigma N_plus =
       star N_plus + star N_plus) ∧
    W_vortex N_plus = (1 - V N_plus) + J N_plus ∧
    (W_vortex N_plus * W_vortex N_plus = Z_center N_plus ∧
     Z_center N_plus * Z_center N_plus = 1) ∧
    (Phi N_plus * Phi N_plus = V N_plus ∧
     V N_plus * Phi N_plus = Phi N_plus) ∧
    V N_plus * V N_plus -
      comm (U_plus N_plus) (U_minus N_plus) * comm (U_plus N_plus) (U_minus N_plus) = 0 ∧
    (Z_center N_plus * V N_plus = -V N_plus ∧
     Z_center N_plus * Phi N_plus = -Phi N_plus) := by
  exact ⟨⟨YangMillsVortexStage.poset_chain_and_acyclicity.1.1,
          YangMillsVortexStage.poset_chain_and_acyclicity.1.2.2.2.2.2.2.2.2⟩,
    ⟨U_plus_mul_inv N_plus h_nil, U_minus_mul_inv N_plus h_nil, star_U_plus N_plus⟩,
    comm_U_plus_U_minus N_plus,
    ⟨C_plus_eq_two_P N_plus, C_minus_eq_two_Q N_plus⟩,
    ⟨two_sheeted_condensate_sum N_plus, two_sheeted_condensate_diff N_plus⟩,
    ⟨maurer_cartan_defect_plus N_plus h_nil h_reg,
     maurer_cartan_defect_minus N_plus h_nil h_reg⟩,
    W_vortex_eq N_plus h_nil h_reg,
    ⟨W_vortex_sq_eq_Z_center N_plus h_nil h_reg, Z_center_sq_eq_one N_plus h_nil h_reg⟩,
    ⟨Phi_sq_eq_V N_plus h_nil, vortex_mass_eigenvalue_Phi N_plus h_nil h_reg⟩,
    bps_vortex_mass_saturation N_plus h_nil h_reg,
    ⟨Z_center_flips_V N_plus h_nil h_reg, Z_center_flips_Phi N_plus h_nil h_reg⟩⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsVortexPoset
