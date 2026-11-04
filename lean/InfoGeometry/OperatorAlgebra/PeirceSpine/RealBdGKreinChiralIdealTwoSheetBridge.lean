/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Abel

/-!
# Background-Free Real BdG / Krein Chiral Ideal Two-Sheet Bridge (`BDG₁ ≺ BDG₂ ≺ ⋯ ≺ BDG₁₀`)

In `[Ring B] [StarRing B]`, without assuming any pre-existing spacetime manifold or continuum
field equations, the two-sheeted Peirce structure, the Bogoliubov–de Gennes (BdG) / Krein spectral
gap, and the emergent causal lightcone are derived strictly downstream from a nilpotent Von Neumann
regular pair `(N_+, N_- = star N_+)` (`N_+ * N_+ = 0`, `N_+ * star N_+ * N_+ = N_+`) and its
chiral ideals:

1. **Chiral Ideal Owners & Mutual Reconstruction (`BDG₁`–`BDG₂`)**:
   `(X * N_+) * N_- = X * P`, `(X * P) * N_+ = X * N_+`,
   `(X * N_-) * N_+ = X * Q`, `(X * Q) * N_- = X * N_-`.
2. **Real BdG Particle–Hole Symmetry & Emergent Krein Gap (`BDG₃`–`BDG₅`)**:
   On the global Krein fundamental involution `S_P = 2P - 1` (`S_P² = 1`, `star S_P = S_P`),
   `S_P * Φ = J`, `Φ * S_P = -J`, `{S_P, Φ} = 0`, `S_P * Φ * S_P = -Φ`, and the emergent gap
   support `V = P + Q` satisfies `Φ² = V`, `-J² = V`, `Σ² = V`, and `S_P * Σ = V`.
3. **Unipotent Bogoliubov Automorphisms & Steinberg Sheet Exchange (`BDG₆`–`BDG₈`)**:
   `W_Bog = U_+ U_-⁻¹ U_+ = (1 - V) + J` is strictly unitary (`W_Bog * star W_Bog = 1` and
   `star W_Bog * W_Bog = 1`) and exchanges the two Peirce ideal sheets:
   `W_Bog * P * star W_Bog = Q`, `W_Bog * Q * star W_Bog = P`,
   `W_Bog * Σ * star W_Bog = -Σ`, and `W_Bog * V * star W_Bog = V`.
4. **Emergent Two-Sheeted Peirce Decomposition & Causal Null Cone as Output (`BDG₉`–`BDG₁₀`)**:
   `V * X * V = D_diag N_plus X + D_off N_plus X`, `[S_P, D_diag(X)] = 0`,
   `{S_P, D_off(X)} = 0`, and `(V + Σ) * (V - Σ) = 0`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealBridge

open scoped Matrix

/-!
### 0. The 10-Stage Acyclic Causal Poset (`BDG₁ ≺ BDG₂ ≺ ⋯ ≺ BDG₁₀`) & Ring Helpers
-/

/-- The 10 stages of the Background-Free Real BdG / Krein Chiral Ideal Bridge (`BDG₁`–`BDG₁₀`). -/
inductive RealBdGKreinChiralStage : Type
  | BDG1_ChiralNilpotentLeftIdealCarriers
  | BDG2_OrthogonalPeirceSheetIdempotents
  | BDG3_KreinFundamentalInvolutionAndRotorBridge
  | BDG4_RealBdGParticleHoleAnticommutation
  | BDG5_EmergentKreinBdGSpectralGap
  | BDG6_SteinbergBogoliubovUnipotentCoagulation
  | BDG7_ExactSteinbergBogoliubovUnitarity
  | BDG8_NonPerturbativeSheetExchangeAndGapInvariance
  | BDG9_EmergentTwoSheetPeirceDecomposition
  | BDG10_EmergentCausalGradingAndLightconeOutput
  deriving DecidableEq, Repr

namespace RealBdGKreinChiralStage

/-- Numerical causal depth (`0` through `9`) of each stage in `RealBdGKreinChiralStage`. -/
def rank : RealBdGKreinChiralStage → ℕ
  | .BDG1_ChiralNilpotentLeftIdealCarriers            => 0
  | .BDG2_OrthogonalPeirceSheetIdempotents            => 1
  | .BDG3_KreinFundamentalInvolutionAndRotorBridge    => 2
  | .BDG4_RealBdGParticleHoleAnticommutation          => 3
  | .BDG5_EmergentKreinBdGSpectralGap                 => 4
  | .BDG6_SteinbergBogoliubovUnipotentCoagulation     => 5
  | .BDG7_ExactSteinbergBogoliubovUnitarity           => 6
  | .BDG8_NonPerturbativeSheetExchangeAndGapInvariance => 7
  | .BDG9_EmergentTwoSheetPeirceDecomposition         => 8
  | .BDG10_EmergentCausalGradingAndLightconeOutput    => 9

/-- Strict causal precedence `s₁ ≺ s₂` in the 10-stage Real BdG / Krein Chiral Ideal Bridge. -/
abbrev causalEdge (s₁ s₂ : RealBdGKreinChiralStage) : Prop :=
  s₁.rank < s₂.rank

/-- Reflexive-transitive causal order `s₁ ≼ s₂`. -/
abbrev causalLe (s₁ s₂ : RealBdGKreinChiralStage) : Prop :=
  s₁.rank ≤ s₂.rank

instance instLT : LT RealBdGKreinChiralStage := ⟨causalEdge⟩
instance instLE : LE RealBdGKreinChiralStage := ⟨causalLe⟩

/-- `RealBdGKreinChiralStage` forms a strict 10-element `LinearOrder`. -/
instance instLinearOrder : LinearOrder RealBdGKreinChiralStage where
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

/-- **Strict 10-Stage Poset Chain & Acyclicity (`BDG₁ ≺ BDG₂ ≺ ⋯ ≺ BDG₁₀`)**. -/
theorem poset_chain_and_acyclicity :
    (causalEdge .BDG1_ChiralNilpotentLeftIdealCarriers .BDG2_OrthogonalPeirceSheetIdempotents ∧
     causalEdge .BDG2_OrthogonalPeirceSheetIdempotents .BDG3_KreinFundamentalInvolutionAndRotorBridge ∧
     causalEdge .BDG3_KreinFundamentalInvolutionAndRotorBridge .BDG4_RealBdGParticleHoleAnticommutation ∧
     causalEdge .BDG4_RealBdGParticleHoleAnticommutation .BDG5_EmergentKreinBdGSpectralGap ∧
     causalEdge .BDG5_EmergentKreinBdGSpectralGap .BDG6_SteinbergBogoliubovUnipotentCoagulation ∧
     causalEdge .BDG6_SteinbergBogoliubovUnipotentCoagulation .BDG7_ExactSteinbergBogoliubovUnitarity ∧
     causalEdge .BDG7_ExactSteinbergBogoliubovUnitarity .BDG8_NonPerturbativeSheetExchangeAndGapInvariance ∧
     causalEdge .BDG8_NonPerturbativeSheetExchangeAndGapInvariance .BDG9_EmergentTwoSheetPeirceDecomposition ∧
     causalEdge .BDG9_EmergentTwoSheetPeirceDecomposition .BDG10_EmergentCausalGradingAndLightconeOutput) ∧
    (∀ s : RealBdGKreinChiralStage, ¬ causalEdge s s) ∧
    (∀ s₁ s₂ : RealBdGKreinChiralStage, causalEdge s₁ s₂ → ¬ causalEdge s₂ s₁) ∧
    (∀ s₁ s₂ s₃ : RealBdGKreinChiralStage,
      causalEdge s₁ s₂ → causalEdge s₂ s₃ → causalEdge s₁ s₃) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro s; exact Nat.lt_irrefl s.rank
  · intro s₁ s₂ h12 h21; exact Nat.lt_asymm h12 h21
  · intro s₁ s₂ s₃ h12 h23; exact Nat.lt_trans h12 h23

end RealBdGKreinChiralStage

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

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

def U_plus (N_plus : B) : B := 1 + N_plus

end RingHelpers

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 1. Chiral Nilpotent & Peirce Ideal Carriers (`BDG₁–BDG₂`)
-/

/-- Positive chiral Peirce idempotent `P = N_+ N_-` (Sheet `+` carrier). -/
def P (N_plus : B) : B := N_plus * star N_plus

/-- Negative chiral Peirce idempotent `Q = N_- N_+` (Sheet `-` carrier). -/
def Q (N_plus : B) : B := star N_plus * N_plus

/-- Emergent Real BdG / Krein gap support `V = {N_+, N_-} = P + Q`. -/
def V (N_plus : B) : B := N_plus * star N_plus + star N_plus * N_plus

/-- Intrinsic chiral / particle-hole grading `Σ = [N_+, N_-] = P - Q`. -/
def Sigma (N_plus : B) : B := N_plus * star N_plus - star N_plus * N_plus

/-- Global Krein fundamental involution `S_P = 2P - 1`. -/
def S_P (N_plus : B) : B := P N_plus + P N_plus - 1

/-- Real BdG symmetric pairing operator `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Real BdG skew-symmetric rotor `J = N_+ - N_-`. -/
def J (N_plus : B) : B := N_plus - star N_plus

theorem star_N_plus_sq (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * star N_plus = 0 := by
  rw [← star_mul, h_nil, star_zero]

theorem star_N_plus_reg (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * N_plus * star N_plus = star N_plus := by
  have h := congrArg star h_reg
  rw [star_mul, star_mul, star_star, ← mul_assoc] at h
  exact h

/-- `BDG₁` Mutual Left-Ideal Carrier Equivalence (Sheet `+`):
    Right-multiplying any element `X * N_+` of the nilpotent left ideal `B N_+` by `N_-`
    projects onto `X * P`, and right-multiplying `X * P` by `N_+` recovers `X * N_+`. -/
theorem left_ideal_carrier_plus_to_P (N_plus X : B) :
    (X * N_plus) * star N_plus = X * P N_plus := by
  dsimp [P]
  rw [mul_assoc]

theorem left_ideal_carrier_P_to_plus (N_plus X : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    (X * P N_plus) * N_plus = X * N_plus := by
  dsimp [P]
  rw [mul_assoc X (N_plus * star N_plus) N_plus, h_reg]

/-- `BDG₁` Mutual Left-Ideal Carrier Equivalence (Sheet `-`):
    Right-multiplying `X * N_-` by `N_+` projects onto `X * Q`, and right-multiplying
    `X * Q` by `N_-` recovers `X * N_-`. -/
theorem left_ideal_carrier_minus_to_Q (N_plus X : B) :
    (X * star N_plus) * N_plus = X * Q N_plus := by
  dsimp [Q]
  rw [mul_assoc]

theorem left_ideal_carrier_Q_to_minus (N_plus X : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    (X * Q N_plus) * star N_plus = X * star N_plus := by
  dsimp [Q]
  rw [mul_assoc X (star N_plus * N_plus) (star N_plus), star_N_plus_reg N_plus h_reg]

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

theorem P_star (N_plus : B) : star (P N_plus) = P N_plus := by
  dsimp [P]; rw [star_mul, star_star]

theorem Q_star (N_plus : B) : star (Q N_plus) = Q N_plus := by
  dsimp [Q]; rw [star_mul, star_star]

theorem V_star (N_plus : B) : star (V N_plus) = V N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, star_add, P_star, Q_star]

theorem J_star (N_plus : B) : star (J N_plus) = -J N_plus := by
  dsimp [J]; rw [star_sub, star_star, neg_sub]

theorem P_mul_N_plus (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * N_plus = N_plus := h_reg

theorem N_plus_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    N_plus * P N_plus = 0 := by
  dsimp [P]; rw [← mul_assoc, h_nil, zero_mul]

theorem N_plus_mul_Q (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * Q N_plus = N_plus := by
  dsimp [Q]; rw [← mul_assoc, h_reg]

theorem Q_mul_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * N_plus = 0 := by
  dsimp [Q]; rw [mul_assoc, h_nil, mul_zero]

theorem P_mul_star_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    P N_plus * star N_plus = 0 := by
  dsimp [P]; rw [mul_assoc, star_N_plus_sq N_plus h_nil, mul_zero]

theorem star_N_plus_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * P N_plus = star N_plus := by
  dsimp [P]; rw [← mul_assoc, star_N_plus_reg N_plus h_reg]

theorem Q_mul_star_N_plus (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Q N_plus * star N_plus = star N_plus :=
  star_N_plus_reg N_plus h_reg

theorem star_N_plus_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * Q N_plus = 0 := by
  dsimp [Q]; rw [← mul_assoc, star_N_plus_sq N_plus h_nil, zero_mul]

/-!
### 2. Real BdG / Krein Particle–Hole Algebra & Emergent Spectral Gap (`BDG₃–BDG₅`)
-/

theorem S_P_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * P N_plus = P N_plus := by
  dsimp [S_P]
  calc (P N_plus + P N_plus - 1) * P N_plus
    _ = (P N_plus + P N_plus) * P N_plus - 1 * P N_plus := by rw [sub_mul]
    _ = (P N_plus * P N_plus + P N_plus * P N_plus) - P N_plus := by
        rw [add_mul, one_mul]
    _ = (P N_plus + P N_plus) - P N_plus := by rw [P_idem N_plus h_reg]
    _ = P N_plus := by rw [add_sub_self_right]

theorem P_mul_S_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * S_P N_plus = P N_plus := by
  dsimp [S_P]
  calc P N_plus * (P N_plus + P N_plus - 1)
    _ = P N_plus * (P N_plus + P N_plus) - P N_plus * 1 := by rw [mul_sub]
    _ = (P N_plus * P N_plus + P N_plus * P N_plus) - P N_plus := by
        rw [mul_add, mul_one]
    _ = (P N_plus + P N_plus) - P N_plus := by rw [P_idem N_plus h_reg]
    _ = P N_plus := by rw [add_sub_self_right]

theorem S_P_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    S_P N_plus * Q N_plus = -Q N_plus := by
  dsimp [S_P]
  calc (P N_plus + P N_plus - 1) * Q N_plus
    _ = (P N_plus + P N_plus) * Q N_plus - 1 * Q N_plus := by rw [sub_mul]
    _ = (P N_plus * Q N_plus + P N_plus * Q N_plus) - Q N_plus := by
        rw [add_mul, one_mul]
    _ = (0 + 0) - Q N_plus := by rw [P_mul_Q N_plus h_nil]
    _ = -Q N_plus := by rw [add_zero, zero_sub]

theorem Q_mul_S_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * S_P N_plus = -Q N_plus := by
  dsimp [S_P]
  calc Q N_plus * (P N_plus + P N_plus - 1)
    _ = Q N_plus * (P N_plus + P N_plus) - Q N_plus * 1 := by rw [mul_sub]
    _ = (Q N_plus * P N_plus + Q N_plus * P N_plus) - Q N_plus := by
        rw [mul_add, mul_one]
    _ = (0 + 0) - Q N_plus := by rw [Q_mul_P N_plus h_nil]
    _ = -Q N_plus := by rw [add_zero, zero_sub]

theorem S_P_sq_eq_one (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * S_P N_plus = 1 := by
  have hP := S_P_mul_P N_plus h_reg
  calc S_P N_plus * (P N_plus + P N_plus - 1)
    _ = S_P N_plus * (P N_plus + P N_plus) - S_P N_plus * 1 := by rw [mul_sub]
    _ = (S_P N_plus * P N_plus + S_P N_plus * P N_plus) - S_P N_plus := by
        rw [mul_add, mul_one]
    _ = (P N_plus + P N_plus) - ((P N_plus + P N_plus) - 1) := by rw [hP, S_P]
    _ = ((P N_plus + P N_plus - 1) + 1) - (P N_plus + P N_plus - 1) := by
        rw [sub_add_self (P N_plus + P N_plus) 1]
    _ = 1 := by rw [add_sub_self_left]

theorem S_P_mul_N_plus (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * N_plus = N_plus := by
  dsimp [S_P]
  rw [sub_mul, add_mul, one_mul, P_mul_N_plus N_plus h_reg, add_sub_self_right]

theorem N_plus_mul_S_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    N_plus * S_P N_plus = -N_plus := by
  dsimp [S_P]
  rw [mul_sub, mul_add, mul_one, N_plus_mul_P N_plus h_nil, add_zero, zero_sub]

theorem S_P_mul_star_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    S_P N_plus * star N_plus = -star N_plus := by
  dsimp [S_P]
  rw [sub_mul, add_mul, one_mul, P_mul_star_N_plus N_plus h_nil, add_zero, zero_sub]

theorem star_N_plus_mul_S_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * S_P N_plus = star N_plus := by
  dsimp [S_P]
  rw [mul_sub, mul_add, mul_one, star_N_plus_mul_P N_plus h_reg, add_sub_self_right]

/-- **`BDG₃` Krein Rotor Bridge (`S_P * Φ = J` and `Φ * S_P = -J`):**
    Left-multiplying the symmetric BdG pairing `Φ` by the Krein fundamental symmetry `S_P`
    produces the skew-adjoint rotor `J = N_+ - N_-`. -/
theorem S_P_mul_Phi_eq_J (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * Phi N_plus = J N_plus := by
  dsimp [Phi, J]
  rw [mul_add, S_P_mul_N_plus N_plus h_reg, S_P_mul_star_N_plus N_plus h_nil,
      ← sub_eq_add_neg]

theorem Phi_mul_S_P_eq_neg_J (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * S_P N_plus = -J N_plus := by
  dsimp [Phi, J]
  rw [add_mul, N_plus_mul_S_P N_plus h_nil, star_N_plus_mul_S_P N_plus h_reg,
      add_comm (-N_plus) (star N_plus), ← sub_eq_add_neg, neg_sub]

/-- **`BDG₄` Real BdG Particle–Hole Anticommutation (`{S_P, Φ} = 0`):**
    The BdG pairing operator `Φ` strictly anticommutes with the Krein grading `S_P`. -/
theorem anticomm_S_P_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (S_P N_plus) (Phi N_plus) = 0 := by
  dsimp [anticomm]
  rw [S_P_mul_Phi_eq_J N_plus h_nil h_reg,
      Phi_mul_S_P_eq_neg_J N_plus h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

/-- **`BDG₅` Emergent Krein / BdG Gap Identity (`S_P * Σ = V` and `Φ² = V`):**
    The Krein gap `V = P + Q` emerges identically from `S_P * Σ` and from `Φ * Φ`. -/
theorem S_P_mul_Sigma_eq_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * Sigma N_plus = V N_plus := by
  have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hS, hV, mul_sub,
      S_P_mul_P N_plus h_reg, S_P_mul_Q N_plus h_nil,
      sub_eq_add_neg, neg_neg]

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
    _ = star N_plus * N_plus + N_plus * star N_plus := by rw [zero_add, add_zero]
    _ = N_plus * star N_plus + star N_plus * N_plus := by rw [add_comm]

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
    _ = -(star N_plus * N_plus) - N_plus * star N_plus := by rw [zero_sub, sub_zero]
    _ = -(star N_plus * N_plus + N_plus * star N_plus) := by
        rw [sub_eq_add_neg, ← neg_add]
    _ = -(N_plus * star N_plus + star N_plus * N_plus) := by
        rw [add_comm (star N_plus * N_plus)]

theorem Sigma_sq_eq_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * Sigma N_plus = V N_plus := by
  have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hS, hV]
  calc (P N_plus - Q N_plus) * (P N_plus - Q N_plus)
    _ = (P N_plus - Q N_plus) * P N_plus - (P N_plus - Q N_plus) * Q N_plus := by rw [mul_sub]
    _ = (P N_plus * P N_plus - Q N_plus * P N_plus) -
        (P N_plus * Q N_plus - Q N_plus * Q N_plus) := by rw [sub_mul, sub_mul]
    _ = (P N_plus - 0) - (0 - Q N_plus) := by
        rw [P_idem N_plus h_reg, Q_mul_P N_plus h_nil, P_mul_Q N_plus h_nil, Q_idem N_plus h_reg]
    _ = P N_plus + Q N_plus := by rw [sub_zero, zero_sub, sub_eq_add_neg, neg_neg]

/-!
### 3. Steinberg–Bogoliubov Unitary & Two-Sheeted Peirce Exchange (`BDG₆–BDG₈`)
-/

def U_minus_inv (N_plus : B) : B := 1 - star N_plus

/-- The Steinberg–Bogoliubov triple unipotent operator `W_Bog = U_+ U_-⁻¹ U_+`. -/
def W_Bog (N_plus : B) : B :=
  U_plus N_plus * U_minus_inv N_plus * U_plus N_plus

theorem V_mul_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * P N_plus = P N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, add_mul, P_idem N_plus h_reg, Q_mul_P N_plus h_nil, add_zero]

theorem P_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * V N_plus = P N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, P_idem N_plus h_reg, P_mul_Q N_plus h_nil, add_zero]

theorem V_mul_Q (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * Q N_plus = Q N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, add_mul, P_mul_Q N_plus h_nil, Q_idem N_plus h_reg, zero_add]

theorem Q_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Q N_plus * V N_plus = Q N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, Q_mul_P N_plus h_nil, Q_idem N_plus h_reg, zero_add]

theorem V_idem (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * V N_plus = V N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, add_mul, add_mul,
      P_idem N_plus h_reg, Q_mul_P N_plus h_nil,
      P_mul_Q N_plus h_nil, Q_idem N_plus h_reg,
      add_zero, zero_add]

theorem V_mul_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * N_plus = N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, add_mul, P_mul_N_plus N_plus h_reg, Q_mul_N_plus N_plus h_nil, add_zero]

theorem N_plus_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * V N_plus = N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, N_plus_mul_P N_plus h_nil, N_plus_mul_Q N_plus h_reg, zero_add]

theorem V_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * star N_plus = star N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, add_mul, P_mul_star_N_plus N_plus h_nil, Q_mul_star_N_plus N_plus h_reg, zero_add]

theorem star_N_plus_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * V N_plus = star N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, star_N_plus_mul_P N_plus h_reg, star_N_plus_mul_Q N_plus h_nil, add_zero]

/-- `BDG₆` Algebraic Coagulation of the Steinberg–Bogoliubov Operator:
    `W_Bog = (1 - V) + J`. -/
theorem W_Bog_eq (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus = (1 - V N_plus) + J N_plus := by
  dsimp [W_Bog, U_plus, U_minus_inv, J]
  have h1 : (1 + N_plus) * (1 - star N_plus) =
            (1 + (N_plus - star N_plus)) - P N_plus := by
    dsimp [P]
    calc (1 + N_plus) * (1 - star N_plus)
      _ = (1 + N_plus) * 1 - (1 + N_plus) * star N_plus := by rw [mul_sub]
      _ = (1 + N_plus) - (1 * star N_plus + N_plus * star N_plus) := by
          rw [mul_one, add_mul]
      _ = (1 + N_plus) - (star N_plus + N_plus * star N_plus) := by rw [one_mul]
      _ = ((1 + N_plus) - star N_plus) - N_plus * star N_plus := by
          rw [sub_add_eq_sub_sub]
      _ = (1 + (N_plus - star N_plus)) - N_plus * star N_plus := by
          rw [← add_sub_assoc']
  have hJ_N : (N_plus - star N_plus) * N_plus = -Q N_plus := by
    dsimp [Q]; rw [sub_mul, h_nil, zero_sub]
  have hR : ((1 + (N_plus - star N_plus)) - P N_plus) * N_plus = -Q N_plus := by
    calc ((1 + (N_plus - star N_plus)) - P N_plus) * N_plus
      _ = (1 + (N_plus - star N_plus)) * N_plus - P N_plus * N_plus := by rw [sub_mul]
      _ = (1 * N_plus + (N_plus - star N_plus) * N_plus) - N_plus := by
          rw [add_mul, P_mul_N_plus N_plus h_reg]
      _ = (N_plus + -Q N_plus) - N_plus := by rw [one_mul, hJ_N]
      _ = (-Q N_plus + N_plus) - N_plus := by rw [add_comm N_plus (-Q N_plus)]
      _ = -Q N_plus := by rw [add_sub_self_right]
  rw [h1]
  calc ((1 + (N_plus - star N_plus)) - P N_plus) * (1 + N_plus)
    _ = ((1 + (N_plus - star N_plus)) - P N_plus) * 1 +
        ((1 + (N_plus - star N_plus)) - P N_plus) * N_plus := by rw [mul_add]
    _ = ((1 + (N_plus - star N_plus)) - P N_plus) - Q N_plus := by
        rw [mul_one, hR, ← sub_eq_add_neg]
    _ = (1 + (N_plus - star N_plus)) - (P N_plus + Q N_plus) := by
        rw [← sub_add_eq_sub_sub]
    _ = ((N_plus - star N_plus) + 1) - V N_plus := by
        rw [add_comm 1 (N_plus - star N_plus)]; rfl
    _ = (N_plus - star N_plus) + (1 - V N_plus) := by rw [← add_sub_assoc']
    _ = (1 - V N_plus) + (N_plus - star N_plus) := by rw [add_comm]

theorem star_W_Bog_eq (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star (W_Bog N_plus) = (1 - V N_plus) - J N_plus := by
  rw [W_Bog_eq N_plus h_nil h_reg, star_add, star_sub, star_one,
      V_star, J_star, ← sub_eq_add_neg]

/-- **`BDG₇` Exact Unitarity of the Steinberg–Bogoliubov Operator (`W_Bog * W_Bog* = 1`):**
    The unipotent Bogoliubov braid is strictly unitary in `B`. -/
theorem W_Bog_mul_star_self (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * star (W_Bog N_plus) = 1 := by
  rw [star_W_Bog_eq N_plus h_nil h_reg, W_Bog_eq N_plus h_nil h_reg]
  have h1V_idem : (1 - V N_plus) * (1 - V N_plus) = 1 - V N_plus := by
    rw [mul_sub, mul_one, sub_mul, one_mul, V_idem N_plus h_nil h_reg, sub_self, sub_zero]
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
  calc ((1 - V N_plus) + J N_plus) * ((1 - V N_plus) - J N_plus)
    _ = ((1 - V N_plus) + J N_plus) * (1 - V N_plus) -
        ((1 - V N_plus) + J N_plus) * J N_plus := by rw [mul_sub]
    _ = ((1 - V N_plus) * (1 - V N_plus) + J N_plus * (1 - V N_plus)) -
        ((1 - V N_plus) * J N_plus + J N_plus * J N_plus) := by rw [add_mul, add_mul]
    _ = ((1 - V N_plus) + 0) - (0 + -V N_plus) := by
        rw [h1V_idem, hJ_1V, h1V_J, J_sq_eq_neg_V N_plus h_nil]
    _ = (1 - V N_plus) + V N_plus := by
        rw [add_zero, zero_add, sub_eq_add_neg, neg_neg]
    _ = 1 := by rw [sub_add_self]

theorem W_Bog_mul_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * P N_plus = -star N_plus := by
  rw [W_Bog_eq N_plus h_nil h_reg, add_mul]
  have h1 : (1 - V N_plus) * P N_plus = 0 := by
    rw [sub_mul, one_mul, V_mul_P N_plus h_nil h_reg, sub_self]
  have h2 : J N_plus * P N_plus = -star N_plus := by
    dsimp [J]
    rw [sub_mul, N_plus_mul_P N_plus h_nil, star_N_plus_mul_P N_plus h_reg, zero_sub]
  rw [h1, h2, zero_add]

theorem W_Bog_mul_Q (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * Q N_plus = N_plus := by
  rw [W_Bog_eq N_plus h_nil h_reg, add_mul]
  have h1 : (1 - V N_plus) * Q N_plus = 0 := by
    rw [sub_mul, one_mul, V_mul_Q N_plus h_nil h_reg, sub_self]
  have h2 : J N_plus * Q N_plus = N_plus := by
    dsimp [J]
    rw [sub_mul, N_plus_mul_Q N_plus h_reg, star_N_plus_mul_Q N_plus h_nil, sub_zero]
  rw [h1, h2, zero_add]

/-- **`BDG₈` Non-Perturbative Sheet Exchange I (`W_Bog * P * W_Bog* = Q`):**
    Conjugating Sheet `+` (`P`) by the Steinberg–Bogoliubov unitary maps it onto Sheet `-` (`Q`). -/
theorem W_Bog_conj_P_eq_Q (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * P N_plus * star (W_Bog N_plus) = Q N_plus := by
  rw [W_Bog_mul_P N_plus h_nil h_reg, star_W_Bog_eq N_plus h_nil h_reg, neg_mul]
  have h1 : star N_plus * (1 - V N_plus) = 0 := by
    rw [mul_sub, mul_one, star_N_plus_mul_V N_plus h_nil h_reg, sub_self]
  have h2 : star N_plus * J N_plus = Q N_plus := by
    dsimp [J, Q]
    rw [mul_sub, star_N_plus_sq N_plus h_nil, sub_zero]
  rw [mul_sub, h1, h2, zero_sub, neg_neg]

/-- **`BDG₈` Non-Perturbative Sheet Exchange II (`W_Bog * Q * W_Bog* = P`):**
    Conjugating Sheet `-` (`Q`) by `W_Bog` maps it onto Sheet `+` (`P`). -/
theorem W_Bog_conj_Q_eq_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * Q N_plus * star (W_Bog N_plus) = P N_plus := by
  rw [W_Bog_mul_Q N_plus h_nil h_reg, star_W_Bog_eq N_plus h_nil h_reg]
  have h1 : N_plus * (1 - V N_plus) = 0 := by
    rw [mul_sub, mul_one, N_plus_mul_V N_plus h_nil h_reg, sub_self]
  have h2 : N_plus * J N_plus = -P N_plus := by
    dsimp [J, P]
    rw [mul_sub, h_nil, zero_sub]
  rw [mul_sub, h1, h2, zero_sub, neg_neg]

/-- **`BDG₈` Bogoliubov Inversion of the Chiral Grading (`W_Bog * Σ * W_Bog* = -Σ`):**
    Conjugation by `W_Bog` flips the Krein/chiral grading `Σ = P - Q` to `-Σ = Q - P`. -/
theorem W_Bog_conj_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * Sigma N_plus * star (W_Bog N_plus) = -Sigma N_plus := by
  have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
  rw [hS, mul_sub, sub_mul,
      W_Bog_conj_P_eq_Q N_plus h_nil h_reg,
      W_Bog_conj_Q_eq_P N_plus h_nil h_reg,
      neg_sub]

/-- **`BDG₈` Bogoliubov Invariance of the Spectral Gap (`W_Bog * V * W_Bog* = V`):**
    The emergent BdG/Krein gap `V = P + Q` is invariant under the sheet-exchange unitary. -/
theorem W_Bog_conj_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * V N_plus * star (W_Bog N_plus) = V N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, add_mul,
      W_Bog_conj_P_eq_Q N_plus h_nil h_reg,
      W_Bog_conj_Q_eq_P N_plus h_nil h_reg,
      add_comm (Q N_plus) (P N_plus)]

/-!
### 4. Emergent Two-Sheeted Peirce Decomposition & Causal Grading as Output (`BDG₉–BDG₁₀`)
-/

/-- The diagonal intra-sheet Peirce projection `D_diag(X) = P X P + Q X Q`. -/
def D_diag (N_plus X : B) : B :=
  P N_plus * X * P N_plus + Q N_plus * X * Q N_plus

/-- The off-diagonal inter-sheet Peirce projection `D_off(X) = P X Q + Q X P`. -/
def D_off (N_plus X : B) : B :=
  P N_plus * X * Q N_plus + Q N_plus * X * P N_plus

/-- **`BDG₉` Emergent Two-Sheeted Peirce Completeness on the Gap Support:**
    Every operator `V X V` on the emergent gap support splits into the intra-sheet
    diagonal sector `D_diag(X)` plus the inter-sheet pairing sector `D_off(X)`. -/
theorem two_sheet_peirce_decomp (N_plus X : B) :
    V N_plus * X * V N_plus = D_diag N_plus X + D_off N_plus X := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  dsimp [D_diag, D_off]
  rw [hV, mul_add, add_mul, add_mul, add_mul]
  abel

/-- **`BDG₁₀` Emergent Intra-Sheet Stabilizer (`[S_P, D_diag(X)] = 0`):**
    The diagonal two-sheeted sector commutes with the Krein grading `S_P`. -/
theorem comm_S_P_D_diag (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (S_P N_plus) (D_diag N_plus X) = 0 := by
  dsimp [comm, D_diag]
  have hLP : S_P N_plus * (P N_plus * X * P N_plus) = P N_plus * X * P N_plus := by
    rw [← mul_assoc (S_P N_plus) (P N_plus * X) (P N_plus),
        ← mul_assoc (S_P N_plus) (P N_plus) X,
        S_P_mul_P N_plus h_reg]
  have hRP : (P N_plus * X * P N_plus) * S_P N_plus = P N_plus * X * P N_plus := by
    rw [mul_assoc (P N_plus * X) (P N_plus) (S_P N_plus),
        P_mul_S_P N_plus h_reg]
  have hLQ : S_P N_plus * (Q N_plus * X * Q N_plus) = -(Q N_plus * X * Q N_plus) := by
    rw [← mul_assoc (S_P N_plus) (Q N_plus * X) (Q N_plus),
        ← mul_assoc (S_P N_plus) (Q N_plus) X,
        S_P_mul_Q N_plus h_nil, neg_mul, neg_mul]
  have hRQ : (Q N_plus * X * Q N_plus) * S_P N_plus = -(Q N_plus * X * Q N_plus) := by
    rw [mul_assoc (Q N_plus * X) (Q N_plus) (S_P N_plus),
        Q_mul_S_P N_plus h_nil, mul_neg]
  rw [mul_add, add_mul, hLP, hLQ, hRP, hRQ, sub_self]

/-- **`BDG₁₀` Emergent Inter-Sheet Null Transition (`{S_P, D_off(X)} = 0`):**
    The off-diagonal pairing sector strictly anticommutes with `S_P`. -/
theorem anticomm_S_P_D_off (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (S_P N_plus) (D_off N_plus X) = 0 := by
  dsimp [anticomm, D_off]
  have hLPQ : S_P N_plus * (P N_plus * X * Q N_plus) = P N_plus * X * Q N_plus := by
    rw [← mul_assoc (S_P N_plus) (P N_plus * X) (Q N_plus),
        ← mul_assoc (S_P N_plus) (P N_plus) X,
        S_P_mul_P N_plus h_reg]
  have hRPQ : (P N_plus * X * Q N_plus) * S_P N_plus = -(P N_plus * X * Q N_plus) := by
    rw [mul_assoc (P N_plus * X) (Q N_plus) (S_P N_plus),
        Q_mul_S_P N_plus h_nil, mul_neg]
  have hLQP : S_P N_plus * (Q N_plus * X * P N_plus) = -(Q N_plus * X * P N_plus) := by
    rw [← mul_assoc (S_P N_plus) (Q N_plus * X) (P N_plus),
        ← mul_assoc (S_P N_plus) (Q N_plus) X,
        S_P_mul_Q N_plus h_nil, neg_mul, neg_mul]
  have hRQP : (Q N_plus * X * P N_plus) * S_P N_plus = Q N_plus * X * P N_plus := by
    rw [mul_assoc (Q N_plus * X) (P N_plus) (S_P N_plus),
        P_mul_S_P N_plus h_reg]
  rw [mul_add, add_mul, hLPQ, hLQP, hRPQ, hRQP]
  abel

/-- **`BDG₁₀` Emergent Lightcone Null Saturation (`(V + Σ) * (V - Σ) = 0`):**
    The chiral lightcone combinations `V + Σ = 2P` and `V - Σ = 2Q` mutually annihilate. -/
theorem emergent_lightcone_null_saturation (N_plus : B)
    (h_nil : N_plus * N_plus = 0) :
    (V N_plus + Sigma N_plus) * (V N_plus - Sigma N_plus) = 0 := by
  have hVP : V N_plus + Sigma N_plus = P N_plus + P N_plus := by
    have hV : V N_plus = P N_plus + Q N_plus := rfl
    have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
    rw [hV, hS]; abel
  have hVQ : V N_plus - Sigma N_plus = Q N_plus + Q N_plus := by
    have hV : V N_plus = P N_plus + Q N_plus := rfl
    have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
    rw [hV, hS]; abel
  rw [hVP, hVQ, mul_add, add_mul, P_mul_Q N_plus h_nil, add_zero, add_zero]

/-!
### 5. Concrete `2 × 2` Non-Commutative Matrix Witness (`T16` / `T17`) & Master 10-Stage Synthesis
-/

/-- Concrete `2 × 2` nilpotent generator `N_+ = E₀₁ = !![0, 1; 0, 0]`. -/
def bdgMatrixNPlus : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- Concrete `2 × 2` dual nilpotent generator `N_- = E₁₀ = !![0, 0; 1, 0]`. -/
def bdgMatrixNMinus : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- Concrete `2 × 2` integer matrix witness certifying non-commutativity (`T16`) and
non-vanishing BdG/Krein gap `V`, sheet exchange `W_Bog P W_Bog* = Q`, and particle-hole grading (`T17`). -/
theorem bdg_matrix_noncomm_and_nonzero_gap_witness :
    bdgMatrixNPlus * bdgMatrixNPlus = 0 ∧
    bdgMatrixNPlus * star bdgMatrixNPlus * bdgMatrixNPlus = bdgMatrixNPlus ∧
    bdgMatrixNPlus * bdgMatrixNMinus ≠ bdgMatrixNMinus * bdgMatrixNPlus ∧
    V bdgMatrixNPlus ≠ 0 ∧
    W_Bog bdgMatrixNPlus * P bdgMatrixNPlus * star (W_Bog bdgMatrixNPlus) = Q bdgMatrixNPlus ∧
    W_Bog bdgMatrixNPlus * Sigma bdgMatrixNPlus * star (W_Bog bdgMatrixNPlus) =
      -Sigma bdgMatrixNPlus := by
  decide

/-- **Master 10-Stage Synthesis (`real_bdg_krein_chiral_ideal_two_sheet_bridge_master_synthesis`)**:
Coagulates `BDG₁ ≺ BDG₂ ≺ ⋯ ≺ BDG₁₀` over `[Ring B] [StarRing B]` with nilpotent
`N_plus * N_plus = 0` and Von Neumann regularity `N_plus * star N_plus * N_plus = N_plus`. -/
theorem real_bdg_krein_chiral_ideal_two_sheet_bridge_master_synthesis
    (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    (RealBdGKreinChiralStage.causalEdge
       .BDG1_ChiralNilpotentLeftIdealCarriers .BDG2_OrthogonalPeirceSheetIdempotents ∧
     RealBdGKreinChiralStage.causalEdge
       .BDG9_EmergentTwoSheetPeirceDecomposition .BDG10_EmergentCausalGradingAndLightconeOutput) ∧
    ((X * N_plus) * star N_plus = X * P N_plus ∧
     (X * P N_plus) * N_plus = X * N_plus ∧
     (X * star N_plus) * N_plus = X * Q N_plus ∧
     (X * Q N_plus) * star N_plus = X * star N_plus) ∧
    (S_P N_plus * Phi N_plus = J N_plus ∧
     Phi N_plus * S_P N_plus = -J N_plus ∧
     anticomm (S_P N_plus) (Phi N_plus) = 0 ∧
     S_P N_plus * Sigma N_plus = V N_plus ∧
     Phi N_plus * Phi N_plus = V N_plus) ∧
    (W_Bog N_plus = (1 - V N_plus) + J N_plus ∧
     W_Bog N_plus * star (W_Bog N_plus) = 1 ∧
     W_Bog N_plus * P N_plus * star (W_Bog N_plus) = Q N_plus ∧
     W_Bog N_plus * Q N_plus * star (W_Bog N_plus) = P N_plus ∧
     W_Bog N_plus * Sigma N_plus * star (W_Bog N_plus) = -Sigma N_plus ∧
     W_Bog N_plus * V N_plus * star (W_Bog N_plus) = V N_plus) ∧
    (V N_plus * X * V N_plus = D_diag N_plus X + D_off N_plus X ∧
     comm (S_P N_plus) (D_diag N_plus X) = 0 ∧
     anticomm (S_P N_plus) (D_off N_plus X) = 0 ∧
     (V N_plus + Sigma N_plus) * (V N_plus - Sigma N_plus) = 0) := by
  exact ⟨⟨RealBdGKreinChiralStage.poset_chain_and_acyclicity.1.1,
          RealBdGKreinChiralStage.poset_chain_and_acyclicity.1.2.2.2.2.2.2.2.2⟩,
    ⟨left_ideal_carrier_plus_to_P N_plus X,
     left_ideal_carrier_P_to_plus N_plus X h_reg,
     left_ideal_carrier_minus_to_Q N_plus X,
     left_ideal_carrier_Q_to_minus N_plus X h_reg⟩,
    ⟨S_P_mul_Phi_eq_J N_plus h_nil h_reg,
     Phi_mul_S_P_eq_neg_J N_plus h_nil h_reg,
     anticomm_S_P_Phi N_plus h_nil h_reg,
     S_P_mul_Sigma_eq_V N_plus h_nil h_reg,
     Phi_sq_eq_V N_plus h_nil⟩,
    ⟨W_Bog_eq N_plus h_nil h_reg,
     W_Bog_mul_star_self N_plus h_nil h_reg,
     W_Bog_conj_P_eq_Q N_plus h_nil h_reg,
     W_Bog_conj_Q_eq_P N_plus h_nil h_reg,
     W_Bog_conj_Sigma N_plus h_nil h_reg,
     W_Bog_conj_V N_plus h_nil h_reg⟩,
    ⟨two_sheet_peirce_decomp N_plus X,
     comm_S_P_D_diag N_plus X h_nil h_reg,
     anticomm_S_P_D_off N_plus X h_nil h_reg,
     emergent_lightcone_null_saturation N_plus h_nil⟩⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealBridge

/-!
## Part II: Higgs Frame-Dragging, Cyclotomic Minima, & Supercolor Poincaré Emergence (`HFD₁`–`HFD₁₀`)
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.HiggsFrameDraggingSupercolorPoset

section RingHelpers

variable {B : Type*} [Ring B]

theorem sub_add_self (x y : B) : (x - y) + y = x := by
  abel

theorem add_sub_self_right (x y : B) : (x + y) - y = x := by
  abel

theorem add_sub_self_left (x y : B) : (x + y) - x = y := by
  abel

theorem sub_add_sub_cancel_two (a b : B) : (a + b) - (a - b) = b + b := by
  abel

theorem add_add_sub_cancel (a b : B) : (a + b) + (a - b) = a + a := by
  abel

theorem inner_four_cancel (b c e f : B) :
    (e + f) + ((c - e) - (f - b)) = b + c := by
  abel

/-- Universal noncommutative 2-sheet linear difference identity:
    `(a * p + b * q) - (b * p + a * q) = (a - b) * (p - q)`. -/
theorem two_sheet_linear_diff (a b p q : B) :
    (a * p + b * q) - (b * p + a * q) = (a - b) * (p - q) := by
  have h1 : (a * p + b * q) - (b * p + a * q) =
            (a * p - b * p) - (a * q - b * q) := by
    abel
  rw [h1, ← sub_mul, ← sub_mul, ← mul_sub]

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

end RingHelpers

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 1. Core Operators: Condensate Bandgap `V`, Spin Cranking `Σ`, Higgs `Φ`, Goldstone `J`
-/

/-- Sheet `+` Higgs vacuum projector `P = N_+ N_-`. -/
def P (N_plus : B) : B := N_plus * star N_plus

/-- Sheet `-` dual vacuum projector `Q = N_- N_+`. -/
def Q (N_plus : B) : B := star N_plus * N_plus

/-- Condensate Spectral Bandgap / Emergent Poincaré Translation `V = {N_+, N_-} = P + Q`. -/
def V (N_plus : B) : B := N_plus * star N_plus + star N_plus * N_plus

/-- Magnetogravity / Frame-Dragging Spin-Cranking Generator `Σ = [N_+, N_-] = P - Q`. -/
def Sigma (N_plus : B) : B := N_plus * star N_plus - star N_plus * N_plus

/-- Massive Higgs Amplitude Mode `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Nambu–Goldstone Phase Rotor `J = N_+ - N_-`. -/
def J (N_plus : B) : B := N_plus - star N_plus

/-- Negative-cranked Frame-Dragging Potential `H_crank⁻ = V - Σ` (selects vacuum `P`). -/
def H_crank_minus (N_plus : B) : B := V N_plus - Sigma N_plus

/-- Positive-cranked Frame-Dragging Potential `H_crank⁺ = V + Σ` (selects vacuum `Q`). -/
def H_crank_plus (N_plus : B) : B := V N_plus + Sigma N_plus

/-- Cyclotomic Chiral Operator `C_cyc(u, N_+) = u P + (1 - u) Q` pairing Galois roots
    `u` and `1 - u` of `Φ₆(u) = u² - u + 1 = 0` with the chiral sheets `P` and `Q`. -/
def C_cyc (u N_plus : B) : B := u * P N_plus + (1 - u) * Q N_plus

/-- Supercolor Chiral Parity Grading Operator `Γ_chiral = 2P - 1`. -/
def Gamma_chiral (N_plus : B) : B := P N_plus + P N_plus - 1

/-- Emergent Poincaré Translation Generator `P_poincare = {Q_+, Q_-} = V`. -/
def P_poincare (N_plus : B) : B := anticomm N_plus (star N_plus)

/-!
### 2. Foundational Nilpotent & Projector Identities (`HFD₁`)
-/

theorem star_N_plus_sq (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * star N_plus = 0 := by
  rw [← star_mul, h_nil, star_zero]

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

theorem N_plus_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    N_plus * P N_plus = 0 := by
  dsimp [P]; rw [← mul_assoc, h_nil, zero_mul]

theorem P_mul_star_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    P N_plus * star N_plus = 0 := by
  dsimp [P]; rw [mul_assoc, star_N_plus_sq N_plus h_nil, mul_zero]

theorem star_N_plus_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * P N_plus = star N_plus := by
  dsimp [P]; rw [← mul_assoc, star_N_plus_reg N_plus h_reg]

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

/-- **`HFD₁` The Higgs Square Equals the Condensate Bandgap (`Φ² = V`):** -/
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
    _ = star N_plus * N_plus + N_plus * star N_plus := by rw [zero_add, add_zero]
    _ = N_plus * star N_plus + star N_plus * N_plus := by rw [add_comm]

/-- **`HFD₁` Landau–Ginzburg / Mexican-Hat Operator Stationarity (`Φ⁴ - Φ² = 0`):**
    The Higgs amplitude operator `Φ` identically satisfies the quartic Mexican-hat
    stationarity polynomial `(Φ²)² - Φ² = V² - V = 0`. -/
theorem higgs_quartic_stationarity (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    (Phi N_plus * Phi N_plus) * (Phi N_plus * Phi N_plus) -
    (Phi N_plus * Phi N_plus) = 0 := by
  rw [Phi_sq_eq_V N_plus h_nil, V_idem N_plus h_nil h_reg, sub_self]

/-!
### 3. Frame-Dragging / Magnetogravity Spin-Cranking & Cyclotomic Minima (`HFD₂–HFD₅`)
-/

theorem H_crank_plus_eq_two_P (N_plus : B) :
    H_crank_plus N_plus = P N_plus + P N_plus := by
  dsimp [H_crank_plus, V, Sigma, P]
  exact add_add_sub_cancel (N_plus * star N_plus) (star N_plus * N_plus)

theorem H_crank_minus_eq_two_Q (N_plus : B) :
    H_crank_minus N_plus = Q N_plus + Q N_plus := by
  dsimp [H_crank_minus, V, Sigma, Q]
  exact sub_add_sub_cancel_two (N_plus * star N_plus) (star N_plus * N_plus)

/-- **`HFD₃` Frame-Dragging Vacuum Selection I (`H_crank⁻ * P = 0`):**
    The cranked potential `H_crank⁻ = V - Σ` selects Sheet `+` (`P`) as its
    exact zero-energy Higgs vacuum minimum. -/
theorem H_crank_minus_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    H_crank_minus N_plus * P N_plus = 0 := by
  rw [H_crank_minus_eq_two_Q, add_mul, Q_mul_P N_plus h_nil, add_zero]

/-- **`HFD₃` Frame-Dragging Bandgap Excitation (`H_crank⁻ * Q = 2Q`):**
    While `P` is a zero-energy minimum of `H_crank⁻`, the opposite sheet `Q`
    is lifted across the condensate bandgap to `2Q`. -/
theorem H_crank_minus_mul_Q (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    H_crank_minus N_plus * Q N_plus = Q N_plus + Q N_plus := by
  rw [H_crank_minus_eq_two_Q, add_mul, Q_idem N_plus h_reg]

/-- **`HFD₃` Opposite Frame-Dragging Vacuum Selection (`H_crank⁺ * Q = 0`):**
    Reversing the frame-dragging cranking sign (`V + Σ`) selects Sheet `-` (`Q`)
    as the zero-energy vacuum minimum. -/
theorem H_crank_plus_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    H_crank_plus N_plus * Q N_plus = 0 := by
  rw [H_crank_plus_eq_two_P, add_mul, P_mul_Q N_plus h_nil, add_zero]

/-- **`HFD₃` Secular Factorization of the Cranked Potentials (`H_crank⁺ * H_crank⁻ = 0`):** -/
theorem H_crank_secular_product (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    H_crank_plus N_plus * H_crank_minus N_plus = 0 := by
  rw [H_crank_plus_eq_two_P, H_crank_minus_eq_two_Q,
      mul_add, add_mul, P_mul_Q N_plus h_nil, add_zero, add_zero]

/-- **`HFD₄` Cyclotomic Minimum Projection on Sheet `+` (`C_cyc(u) * P = u P`):** -/
theorem C_cyc_mul_P (u N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    C_cyc u N_plus * P N_plus = u * P N_plus := by
  dsimp [C_cyc]
  rw [add_mul,
      mul_assoc u (P N_plus) (P N_plus), P_idem N_plus h_reg,
      mul_assoc (1 - u) (Q N_plus) (P N_plus), Q_mul_P N_plus h_nil,
      mul_zero, add_zero]

/-- **`HFD₄` Cyclotomic Minimum Projection on Sheet `-` (`C_cyc(u) * Q = (1 - u) Q`):** -/
theorem C_cyc_mul_Q (u N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    C_cyc u N_plus * Q N_plus = (1 - u) * Q N_plus := by
  dsimp [C_cyc]
  rw [add_mul,
      mul_assoc u (P N_plus) (Q N_plus), P_mul_Q N_plus h_nil,
      mul_assoc (1 - u) (Q N_plus) (Q N_plus), Q_idem N_plus h_reg,
      mul_zero, zero_add]

/-- **`HFD₄` Cranked Condensate Selects Cyclotomic Eigenvalue `u` (`C_cyc(u) H_crank⁺ = u H_crank⁺`):** -/
theorem C_cyc_mul_H_crank_plus (u N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    C_cyc u N_plus * H_crank_plus N_plus = u * H_crank_plus N_plus := by
  rw [H_crank_plus_eq_two_P, mul_add, C_cyc_mul_P u N_plus h_nil h_reg, ← mul_add]

/-- **`HFD₄` Dual Cranked Condensate Selects Galois Conjugate `1 - u` (`C_cyc(u) H_crank⁻ = (1 - u) H_crank⁻`):** -/
theorem C_cyc_mul_H_crank_minus (u N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    C_cyc u N_plus * H_crank_minus N_plus = (1 - u) * H_crank_minus N_plus := by
  rw [H_crank_minus_eq_two_Q, mul_add, C_cyc_mul_Q u N_plus h_nil h_reg, ← mul_add]

/-- **`HFD₅` Galois–Spin Locking Identity (`C_cyc(u) - C_cyc(1 - u) = (u - (1 - u)) Σ`):**
    The asymmetry between the cyclotomic operator `C_cyc(u)` and its Galois-conjugate
    partner `C_cyc(1 - u)` is driven directly by the magnetogravity spin-cranking field `Σ`. -/
theorem C_cyc_galois_spin_locking (u N_plus : B) :
    C_cyc u N_plus - C_cyc (1 - u) N_plus =
      (u - (1 - u)) * Sigma N_plus := by
  have h1_sub : 1 - (1 - u) = u := by abel
  dsimp [C_cyc]
  rw [h1_sub]
  exact two_sheet_linear_diff u (1 - u) (P N_plus) (Q N_plus)

/-!
### 4. Higgs Amplitude (`Φ`) vs. Nambu–Goldstone Rotor (`J`) Splitting (`HFD₆–HFD₇`)
-/

theorem P_mul_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * Phi N_plus = N_plus := by
  dsimp [Phi]
  rw [mul_add, P_mul_N_plus N_plus h_reg, P_mul_star_N_plus N_plus h_nil, add_zero]

theorem Phi_mul_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * P N_plus = star N_plus := by
  dsimp [Phi]
  rw [add_mul, N_plus_mul_P N_plus h_nil, star_N_plus_mul_P N_plus h_reg, zero_add]

/-- **`HFD₆` Massive Higgs Amplitude Projection (`{P, Φ} = Φ`):**
    The anticommutator of the selected vacuum minimum `P` with `Φ` preserves the
    massive Higgs amplitude mode `Φ = N_+ + N_-`. -/
theorem anticomm_P_Phi_eq_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (P N_plus) (Phi N_plus) = Phi N_plus := by
  dsimp [anticomm]
  rw [P_mul_Phi N_plus h_nil h_reg, Phi_mul_P N_plus h_nil h_reg]
  rfl

/-- **`HFD₆` Nambu–Goldstone Rotor Generation (`[P, Φ] = J`):**
    The commutator of the broken-symmetry vacuum minimum `P` with `Φ` generates
    the Nambu–Goldstone rotor `J = N_+ - N_-`. -/
theorem comm_P_Phi_eq_J (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (P N_plus) (Phi N_plus) = J N_plus := by
  dsimp [comm]
  rw [P_mul_Phi N_plus h_nil h_reg, Phi_mul_P N_plus h_nil h_reg]
  rfl

/-- **`HFD₇` Goldstone–Higgs Feedback into Spin Curvature (`[J, Φ] = 2Σ`):**
    The commutator of the Goldstone rotor `J` and the Higgs amplitude mode `Φ`
    regenerates twice the magnetogravity spin-cranking field `Σ`. -/
theorem comm_J_Phi_eq_two_Sigma (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    comm (J N_plus) (Phi N_plus) = Sigma N_plus + Sigma N_plus := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  have hJPhi : J N_plus * Phi N_plus = Sigma N_plus := by
    dsimp [J, Phi, Sigma]
    calc (N_plus - star N_plus) * (N_plus + star N_plus)
      _ = (N_plus - star N_plus) * N_plus + (N_plus - star N_plus) * star N_plus := by
          rw [mul_add]
      _ = (N_plus * N_plus - star N_plus * N_plus) +
          (N_plus * star N_plus - star N_plus * star N_plus) := by rw [sub_mul, sub_mul]
      _ = (0 - star N_plus * N_plus) + (N_plus * star N_plus - 0) := by
          rw [h_nil, h_star_nil]
      _ = -(star N_plus * N_plus) + N_plus * star N_plus := by rw [zero_sub, sub_zero]
      _ = N_plus * star N_plus + -(star N_plus * N_plus) := by rw [add_comm]
      _ = N_plus * star N_plus - star N_plus * N_plus := by rw [← sub_eq_add_neg]
  have hPhiJ : Phi N_plus * J N_plus = -Sigma N_plus := by
    dsimp [J, Phi, Sigma]
    calc (N_plus + star N_plus) * (N_plus - star N_plus)
      _ = (N_plus + star N_plus) * N_plus - (N_plus + star N_plus) * star N_plus := by
          rw [mul_sub]
      _ = (N_plus * N_plus + star N_plus * N_plus) -
          (N_plus * star N_plus + star N_plus * star N_plus) := by rw [add_mul, add_mul]
      _ = (0 + star N_plus * N_plus) - (N_plus * star N_plus + 0) := by
          rw [h_nil, h_star_nil]
      _ = star N_plus * N_plus - N_plus * star N_plus := by rw [zero_add, add_zero]
      _ = -(N_plus * star N_plus - star N_plus * N_plus) := by rw [neg_sub]
  dsimp [comm]
  rw [hJPhi, hPhiJ, sub_eq_add_neg, neg_neg]

/-!
### 5. Supercolor Chiral Parity Supercharges & Emergent Poincaré Spacetime (`HFD₈–HFD₁₀`)
-/

theorem Gamma_chiral_mul_N_plus (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gamma_chiral N_plus * N_plus = N_plus := by
  dsimp [Gamma_chiral]
  rw [sub_mul, add_mul, one_mul, P_mul_N_plus N_plus h_reg, add_sub_self_right]

theorem N_plus_mul_Gamma_chiral (N_plus : B)
    (h_nil : N_plus * N_plus = 0) :
    N_plus * Gamma_chiral N_plus = -N_plus := by
  dsimp [Gamma_chiral]
  rw [mul_sub, mul_add, mul_one, N_plus_mul_P N_plus h_nil, add_zero, zero_sub]

/-- **`HFD₈` Odd Chiral Parity of Supercharge `Q_+ = N_+` (`{Γ_chiral, N_+} = 0`):** -/
theorem anticomm_Gamma_chiral_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Gamma_chiral N_plus) N_plus = 0 := by
  dsimp [anticomm]
  rw [Gamma_chiral_mul_N_plus N_plus h_reg,
      N_plus_mul_Gamma_chiral N_plus h_nil,
      ← sub_eq_add_neg, sub_self]

/-- **`HFD₈` Odd Chiral Parity of Dual Supercharge `Q_- = N_-` (`{Γ_chiral, N_-} = 0`):** -/
theorem anticomm_Gamma_chiral_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Gamma_chiral N_plus) (star N_plus) = 0 := by
  have hL : Gamma_chiral N_plus * star N_plus = -star N_plus := by
    dsimp [Gamma_chiral]
    rw [sub_mul, add_mul, one_mul, P_mul_star_N_plus N_plus h_nil, add_zero, zero_sub]
  have hR : star N_plus * Gamma_chiral N_plus = star N_plus := by
    dsimp [Gamma_chiral]
    rw [mul_sub, mul_add, mul_one, star_N_plus_mul_P N_plus h_reg, add_sub_self_right]
  dsimp [anticomm]
  rw [hL, hR, add_comm (-star N_plus) (star N_plus), ← sub_eq_add_neg, sub_self]

/-- **`HFD₉` Emergent Poincaré Translation Equals the Higgs Bandgap (`P_poincare = V`):** -/
theorem P_poincare_eq_V (N_plus : B) : P_poincare N_plus = V N_plus := rfl

/-- **`HFD₉` SUSY Translation Invariance (`[P_poincare, Q_+] = 0`):**
    The emergent Poincaré translation generator commutes with the chiral supercharge `N_+`. -/
theorem comm_P_poincare_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (P_poincare N_plus) N_plus = 0 := by
  dsimp [comm, P_poincare, anticomm]
  have hL : (N_plus * star N_plus + star N_plus * N_plus) * N_plus = N_plus := by
    rw [add_mul, h_reg, mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero, add_zero]
  have hR : N_plus * (N_plus * star N_plus + star N_plus * N_plus) = N_plus := by
    rw [mul_add, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
        ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_add]
  rw [hL, hR, sub_self]

/-- **`HFD₁₀` Multi-Channel Supercolor Translation Closure (`[P_poincare(N_a), P_poincare(N_b)] = 0`):**
    For any two supercolor nilpotent channels `N_a, N_b` with commuting bandgap supports,
    their emergent Poincaré translation generators commute identically. -/
theorem supercolor_poincare_comm (N_a N_b : B)
    (h_comm : V N_a * V N_b = V N_b * V N_a) :
    comm (P_poincare N_a) (P_poincare N_b) = 0 := by
  dsimp [comm]
  rw [P_poincare_eq_V, P_poincare_eq_V, h_comm, sub_self]

end InfoGeometry.OperatorAlgebra.PeirceSpine.HiggsFrameDraggingSupercolorPoset

/-!
## Part III: Emergent Two-Sheet BdG / Krein / Cartan Bridge Without Ambient `1` (`E₁`–`E₆`)
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.EmergentTwoSheetBridge

section RingHelpers

variable {B : Type*} [Ring B]

theorem sub_add_self (x y : B) : (x - y) + y = x := by
  abel

theorem add_sub_self_right (x y : B) : (x + y) - y = x := by
  abel

theorem add_sub_add_mid (a m b : B) : (a + m) - (m + b) = a - b := by
  abel

theorem neg_sub_eq_neg_add (a b : B) : -b - a = -(a + b) := by
  abel

theorem add_Four_swap (a b c d : B) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  abel

theorem sub_Four_swap (a b c d : B) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  abel

def anticomm (X Y : B) : B := X * Y + Y * X
def comm (X Y : B) : B := X * Y - Y * X

end RingHelpers

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 1. Emergent Two-Sheet Carrier `(P, Q, V, Σ)` from a Single Nilpotent `N_+` (Zero Ambient `1`)
-/

/-- Emergent Sheet-1 projector `P = N_+ N_-`. -/
def P (N_plus : B) : B := N_plus * star N_plus

/-- Emergent Sheet-2 projector `Q = N_- N_+`. -/
def Q (N_plus : B) : B := star N_plus * N_plus

/-- Emergent two-sheet identity / translation support `V = {N_+, N_-} = P + Q`. -/
def V (N_plus : B) : B := P N_plus + Q N_plus

/-- Intrinsic BdG / Krein fundamental symmetry & uncertainty 2-form `Σ = [N_+, N_-] = P - Q`. -/
def Sigma (N_plus : B) : B := P N_plus - Q N_plus

/-- Seed Grade-1 vector `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Seed Grade-2 elliptic bivector `J = N_+ - N_-`. -/
def J (N_plus : B) : B := N_plus - star N_plus

theorem star_N_plus_sq (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * star N_plus = 0 := by
  rw [← star_mul, h_nil, star_zero]

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
    _ = N_plus * (star N_plus * (star N_plus * N_plus)) := by rw [mul_assoc]
    _ = N_plus * ((star N_plus * star N_plus) * N_plus) := by
        rw [← mul_assoc (star N_plus) (star N_plus) N_plus]
    _ = N_plus * (0 * N_plus) := by rw [star_N_plus_sq N_plus h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

theorem Q_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * P N_plus = 0 := by
  dsimp [P, Q]
  calc (star N_plus * N_plus) * (N_plus * star N_plus)
    _ = star N_plus * (N_plus * (N_plus * star N_plus)) := by rw [mul_assoc]
    _ = star N_plus * ((N_plus * N_plus) * star N_plus) := by
        rw [← mul_assoc N_plus N_plus (star N_plus)]
    _ = star N_plus * (0 * star N_plus) := by rw [h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

/-- **Intrinsic Krein Action on Sheet 1 (`Σ P = P` and `P Σ = P`, No Ambient `1`):** -/
theorem Sigma_mul_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * P N_plus = P N_plus := by
  dsimp [Sigma]
  rw [sub_mul, P_idem N_plus h_reg, Q_mul_P N_plus h_nil, sub_zero]

theorem P_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * Sigma N_plus = P N_plus := by
  dsimp [Sigma]
  rw [mul_sub, P_idem N_plus h_reg, P_mul_Q N_plus h_nil, sub_zero]

/-- **Intrinsic Krein Action on Sheet 2 (`Σ Q = -Q` and `Q Σ = -Q`, No Ambient `1`):** -/
theorem Sigma_mul_Q (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * Q N_plus = -Q N_plus := by
  dsimp [Sigma]
  rw [sub_mul, P_mul_Q N_plus h_nil, Q_idem N_plus h_reg, zero_sub]

theorem Q_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Q N_plus * Sigma N_plus = -Q N_plus := by
  dsimp [Sigma]
  rw [mul_sub, Q_mul_P N_plus h_nil, Q_idem N_plus h_reg, zero_sub]

/-- **Intrinsic Para-Kähler / Krein Involution Law (`Σ² = V` and `Σ V = V Σ = Σ`):** -/
theorem Sigma_sq_eq_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * Sigma N_plus = V N_plus := by
  calc Sigma N_plus * (P N_plus - Q N_plus)
    _ = Sigma N_plus * P N_plus - Sigma N_plus * Q N_plus := by rw [mul_sub]
    _ = P N_plus - (-Q N_plus) := by
        rw [Sigma_mul_P N_plus h_nil h_reg, Sigma_mul_Q N_plus h_nil h_reg]
    _ = P N_plus + Q N_plus := by rw [sub_eq_add_neg, neg_neg]

theorem Sigma_mul_V_eq_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * V N_plus = Sigma N_plus := by
  dsimp [V]
  rw [mul_add, Sigma_mul_P N_plus h_nil h_reg, Sigma_mul_Q N_plus h_nil h_reg, ← sub_eq_add_neg]
  rfl

/-!
### 2. Deriving the Two-Sheet Peirce Filtration, Spin Connection & Solder Frame from `N_+`
-/

/-- Restriction of any operator `X : B` to the emergent two-sheet universe `V X V`. -/
def restrictV (N_plus X : B) : B := V N_plus * X * V N_plus

/-- Emergent intra-sheet spin-connection projection `Ω_V(W) = P W P + Q W Q ∈ g_0`. -/
def spinConnV (N_plus W : B) : B :=
  P N_plus * W * P N_plus + Q N_plus * W * Q N_plus

/-- Emergent outward chiral bridge `E_+(X) = P X Q` (`Sheet 2 → Sheet 1`). -/
def wingPlus (N_plus X : B) : B := P N_plus * X * Q N_plus

/-- Emergent inward chiral bridge `E_-(X) = Q X P` (`Sheet 1 → Sheet 2`). -/
def wingMinus (N_plus X : B) : B := Q N_plus * X * P N_plus

/-- Emergent symmetric inter-sheet frame / solder form `Φ_V(X) = P X Q + Q X P ∈ g_{±1}`. -/
def framePhiV (N_plus X : B) : B := wingPlus N_plus X + wingMinus N_plus X

/-- Emergent skew inter-sheet frame / bivector `J_V(X) = P X Q - Q X P ∈ g_{±1}`. -/
def frameJV (N_plus X : B) : B := wingPlus N_plus X - wingMinus N_plus X

/-- **Theorem E₁ (Emergent Two-Sheet Decomposition of `V X V`):**
    Any operator `X` restricted to the emergent universe `V X V` splits canonically into the
    intra-sheet spin connection `Ω_V(X)` and the inter-sheet solder frame `Φ_V(X)`. -/
theorem restrictV_decomp (N_plus X : B) :
    restrictV N_plus X = spinConnV N_plus X + framePhiV N_plus X := by
  dsimp [restrictV, spinConnV, framePhiV, wingPlus, wingMinus, V]
  rw [add_mul, mul_add, add_mul, add_mul]
  abel

/-- **Theorem E₂ (Vacuum Seed Recovery):**
    Evaluating `wingPlus` and `wingMinus` on the seed `Φ = N_+ + N_-` recovers `N_+` and `N_-`. -/
theorem wingPlus_Phi_eq_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    wingPlus N_plus (Phi N_plus) = N_plus := by
  have hPN : P N_plus * N_plus = N_plus := h_reg
  have hPsN : P N_plus * star N_plus = 0 := by
    dsimp [P]
    rw [mul_assoc N_plus (star N_plus) (star N_plus), star_N_plus_sq N_plus h_nil, mul_zero]
  have hNQ : N_plus * Q N_plus = N_plus := by
    dsimp [Q]
    rw [← mul_assoc N_plus (star N_plus) N_plus, h_reg]
  dsimp [wingPlus, Phi]
  rw [mul_add, hPN, hPsN, add_zero, hNQ]

theorem wingMinus_Phi_eq_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    wingMinus N_plus (Phi N_plus) = star N_plus := by
  have hQN : Q N_plus * N_plus = 0 := by
    dsimp [Q]
    rw [mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero]
  have hQsN : Q N_plus * star N_plus = star N_plus := star_N_plus_reg N_plus h_reg
  have hsNP : star N_plus * P N_plus = star N_plus := by
    dsimp [P]
    rw [← mul_assoc (star N_plus) N_plus (star N_plus), star_N_plus_reg N_plus h_reg]
  dsimp [wingMinus, Phi]
  rw [mul_add, hQN, hQsN, zero_add, hsNP]

/-- **Theorem E₃ (Universal Nilpotency of Inter-Sheet Chiral Wings for Any `X : B`):** -/
theorem wingPlus_sq_zero (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    wingPlus N_plus X * wingPlus N_plus X = 0 := by
  dsimp [wingPlus]
  calc (P N_plus * X * Q N_plus) * (P N_plus * X * Q N_plus)
    _ = P N_plus * X * (Q N_plus * (P N_plus * X * Q N_plus)) := by rw [mul_assoc]
    _ = P N_plus * X * (Q N_plus * (P N_plus * (X * Q N_plus))) := by
        rw [mul_assoc (P N_plus) X (Q N_plus)]
    _ = P N_plus * X * ((Q N_plus * P N_plus) * (X * Q N_plus)) := by
        rw [← mul_assoc (Q N_plus) (P N_plus) (X * Q N_plus)]
    _ = P N_plus * X * (0 * (X * Q N_plus)) := by rw [Q_mul_P N_plus h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

theorem wingMinus_sq_zero (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    wingMinus N_plus X * wingMinus N_plus X = 0 := by
  dsimp [wingMinus]
  calc (Q N_plus * X * P N_plus) * (Q N_plus * X * P N_plus)
    _ = Q N_plus * X * (P N_plus * (Q N_plus * X * P N_plus)) := by rw [mul_assoc]
    _ = Q N_plus * X * (P N_plus * (Q N_plus * (X * P N_plus))) := by
        rw [mul_assoc (Q N_plus) X (P N_plus)]
    _ = Q N_plus * X * ((P N_plus * Q N_plus) * (X * P N_plus)) := by
        rw [← mul_assoc (P N_plus) (Q N_plus) (X * P N_plus)]
    _ = Q N_plus * X * (0 * (X * P N_plus)) := by rw [P_mul_Q N_plus h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

/-- **Theorem E₄ (Intrinsic Krein Grading of Spin Connection vs. Solder Frame):**
    Without using `1`, the intrinsic Krein symmetry `Σ = P - Q` commutes with `Ω_V(W)`
    and anticommutes with `Φ_V(X)` and `J_V(X)`, with `Σ * Φ_V(X) = J_V(X)`. -/
theorem Sigma_mul_wingPlus (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * wingPlus N_plus X = wingPlus N_plus X := by
  dsimp [wingPlus]
  rw [← mul_assoc (Sigma N_plus) (P N_plus * X) (Q N_plus),
      ← mul_assoc (Sigma N_plus) (P N_plus) X,
      Sigma_mul_P N_plus h_nil h_reg]

theorem wingPlus_mul_Sigma (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    wingPlus N_plus X * Sigma N_plus = -wingPlus N_plus X := by
  dsimp [wingPlus]
  rw [mul_assoc (P N_plus * X) (Q N_plus) (Sigma N_plus),
      Q_mul_Sigma N_plus h_nil h_reg, mul_neg]

theorem Sigma_mul_wingMinus (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * wingMinus N_plus X = -wingMinus N_plus X := by
  dsimp [wingMinus]
  rw [← mul_assoc (Sigma N_plus) (Q N_plus * X) (P N_plus),
      ← mul_assoc (Sigma N_plus) (Q N_plus) X,
      Sigma_mul_Q N_plus h_nil h_reg, neg_mul, neg_mul]

theorem wingMinus_mul_Sigma (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    wingMinus N_plus X * Sigma N_plus = wingMinus N_plus X := by
  dsimp [wingMinus]
  rw [mul_assoc (Q N_plus * X) (P N_plus) (Sigma N_plus),
      P_mul_Sigma N_plus h_nil h_reg]

theorem comm_Sigma_spinConnV (N_plus W : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (Sigma N_plus) (spinConnV N_plus W) = 0 := by
  have hL : Sigma N_plus * spinConnV N_plus W =
            P N_plus * W * P N_plus - Q N_plus * W * Q N_plus := by
    dsimp [spinConnV]
    rw [mul_add,
        ← mul_assoc (Sigma N_plus) (P N_plus * W) (P N_plus),
        ← mul_assoc (Sigma N_plus) (P N_plus) W,
        Sigma_mul_P N_plus h_nil h_reg,
        ← mul_assoc (Sigma N_plus) (Q N_plus * W) (Q N_plus),
        ← mul_assoc (Sigma N_plus) (Q N_plus) W,
        Sigma_mul_Q N_plus h_nil h_reg,
        neg_mul, neg_mul, ← sub_eq_add_neg]
  have hR : spinConnV N_plus W * Sigma N_plus =
            P N_plus * W * P N_plus - Q N_plus * W * Q N_plus := by
    dsimp [spinConnV]
    rw [add_mul,
        mul_assoc (P N_plus * W) (P N_plus) (Sigma N_plus),
        P_mul_Sigma N_plus h_nil h_reg,
        mul_assoc (Q N_plus * W) (Q N_plus) (Sigma N_plus),
        Q_mul_Sigma N_plus h_nil h_reg,
        mul_neg, ← sub_eq_add_neg]
  dsimp [comm]
  rw [hL, hR, sub_self]

theorem Sigma_mul_framePhiV (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * framePhiV N_plus X = frameJV N_plus X := by
  dsimp [framePhiV, frameJV]
  rw [mul_add,
      Sigma_mul_wingPlus N_plus X h_nil h_reg,
      Sigma_mul_wingMinus N_plus X h_nil h_reg,
      ← sub_eq_add_neg]

theorem framePhiV_mul_Sigma (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    framePhiV N_plus X * Sigma N_plus = -frameJV N_plus X := by
  dsimp [framePhiV, frameJV]
  rw [add_mul,
      wingPlus_mul_Sigma N_plus X h_nil h_reg,
      wingMinus_mul_Sigma N_plus X h_nil h_reg,
      add_comm (-wingPlus N_plus X) (wingMinus N_plus X),
      ← sub_eq_add_neg, neg_sub]

theorem anticomm_Sigma_framePhiV (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Sigma N_plus) (framePhiV N_plus X) = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_framePhiV N_plus X h_nil h_reg,
      framePhiV_mul_Sigma N_plus X h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

/-!
### 3. Mode-Specific BdG Metric `G_V(X)`, Curvature Dipole `Σ_V(X)` & Universal Null Squeezing
-/

/-- Mode-specific emergent metric `G_V(X) = {E_+(X), E_-(X)} = P X Q X P + Q X P X Q`. -/
def metricGV (N_plus X : B) : B :=
  wingPlus N_plus X * wingMinus N_plus X + wingMinus N_plus X * wingPlus N_plus X

/-- Mode-specific emergent curvature dipole `Σ_V(X) = [E_+(X), E_-(X)] = P X Q X P - Q X P X Q`. -/
def curvSigmaV (N_plus X : B) : B :=
  wingPlus N_plus X * wingMinus N_plus X - wingMinus N_plus X * wingPlus N_plus X

theorem framePhiV_sq_eq_metricGV (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    framePhiV N_plus X * framePhiV N_plus X = metricGV N_plus X := by
  dsimp [framePhiV, metricGV]
  rw [mul_add, add_mul, add_mul,
      wingPlus_sq_zero N_plus X h_nil, wingMinus_sq_zero N_plus X h_nil,
      zero_add, add_zero, add_comm (wingMinus N_plus X * wingPlus N_plus X)]

theorem frameJV_sq_eq_neg_metricGV (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    frameJV N_plus X * frameJV N_plus X = -metricGV N_plus X := by
  dsimp [frameJV, metricGV]
  rw [mul_sub, sub_mul, sub_mul,
      wingPlus_sq_zero N_plus X h_nil, wingMinus_sq_zero N_plus X h_nil,
      zero_sub, sub_zero, neg_sub_eq_neg_add]

theorem frameJV_mul_framePhiV (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    frameJV N_plus X * framePhiV N_plus X = curvSigmaV N_plus X := by
  dsimp [frameJV, framePhiV, curvSigmaV]
  rw [mul_add, sub_mul, sub_mul,
      wingPlus_sq_zero N_plus X h_nil, wingMinus_sq_zero N_plus X h_nil,
      zero_sub, sub_zero, add_comm (-(wingMinus N_plus X * wingPlus N_plus X)),
      ← sub_eq_add_neg]

theorem Sigma_mul_metricGV_eq_curvSigmaV (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * metricGV N_plus X = curvSigmaV N_plus X := by
  dsimp [metricGV, curvSigmaV]
  rw [mul_add,
      ← mul_assoc (Sigma N_plus) (wingPlus N_plus X) (wingMinus N_plus X),
      Sigma_mul_wingPlus N_plus X h_nil h_reg,
      ← mul_assoc (Sigma N_plus) (wingMinus N_plus X) (wingPlus N_plus X),
      Sigma_mul_wingMinus N_plus X h_nil h_reg,
      neg_mul, ← sub_eq_add_neg]

/-- **Theorem E₅ (Universal Hyperbolic Null Lightcone Squeezing for Every Fluctuation `X : B`):**
    For EVERY operator `X : B`, the mode-specific geometric tensor `G_V(X) + Σ_V(X)` and its
    Krein reversion `G_V(X) - Σ_V(X)` satisfy `(G_V(X) + Σ_V(X))(G_V(X) - Σ_V(X)) = 0`! -/
theorem universal_mode_hyperbolic_null_squeezing (N_plus X : B)
    (h_nil : N_plus * N_plus = 0) :
    (metricGV N_plus X + curvSigmaV N_plus X) *
    (metricGV N_plus X - curvSigmaV N_plus X) = 0 := by
  let A := wingPlus N_plus X * wingMinus N_plus X
  let D := wingMinus N_plus X * wingPlus N_plus X
  have hAD : A * D = 0 := by
    dsimp [A, D]
    rw [mul_assoc (wingPlus N_plus X) (wingMinus N_plus X) (wingMinus N_plus X * wingPlus N_plus X),
        ← mul_assoc (wingMinus N_plus X) (wingMinus N_plus X) (wingPlus N_plus X),
        wingMinus_sq_zero N_plus X h_nil, zero_mul, mul_zero]
  have hSum : metricGV N_plus X + curvSigmaV N_plus X = A + A := by
    dsimp [metricGV, curvSigmaV, A, D]
    abel
  have hDiff : metricGV N_plus X - curvSigmaV N_plus X = D + D := by
    dsimp [metricGV, curvSigmaV, A, D]
    abel
  rw [hSum, hDiff, mul_add, add_mul, hAD, add_zero, add_zero]

/-!
### 4. Emergent Élie Cartan Curvature & Torsion Strictly Inside the Two-Sheet Support `V`
-/

/-- Intrinsic Cartan connection `𝓓_V(W, X) = Ω_V(W) + Φ_V(X)` inside `V B V`. -/
def cartanConnV (N_plus W X : B) : B :=
  spinConnV N_plus W + framePhiV N_plus X

/-- Emergent Riemann–Cartan Curvature `𝓡_V = [Ω_V(W₁), Ω_V(W₂)] + [Φ_V(X₁), Φ_V(X₂)]`. -/
def riemannCurvV (N_plus W₁ X₁ W₂ X₂ : B) : B :=
  comm (spinConnV N_plus W₁) (spinConnV N_plus W₂) +
  comm (framePhiV N_plus X₁) (framePhiV N_plus X₂)

/-- Emergent Élie Cartan Torsion `𝓣_V = [Ω_V(W₁), Φ_V(X₂)] - [Ω_V(W₂), Φ_V(X₁)]`. -/
def cartanTorsionV (N_plus W₁ X₁ W₂ X₂ : B) : B :=
  comm (spinConnV N_plus W₁) (framePhiV N_plus X₂) -
  comm (spinConnV N_plus W₂) (framePhiV N_plus X₁)

/-- **Master Theorem E₆ (Emergent Cartan Curvature–Torsion Split from Pure Nilpotent Data):**
    The commutator `[𝓓_V(W₁, X₁), 𝓓_V(W₂, X₂)]` of two emergent Cartan connections splits
    exactly into `𝓡_V + 𝓣_V` without assuming any background manifold! -/
theorem emergent_cartan_curvature_torsion_split (N_plus W₁ X₁ W₂ X₂ : B) :
    comm (cartanConnV N_plus W₁ X₁) (cartanConnV N_plus W₂ X₂) =
      riemannCurvV N_plus W₁ X₁ W₂ X₂ + cartanTorsionV N_plus W₁ X₁ W₂ X₂ := by
  dsimp [cartanConnV, riemannCurvV, cartanTorsionV, comm]
  rw [mul_add, add_mul, add_mul, mul_add, add_mul, add_mul]
  abel

end InfoGeometry.OperatorAlgebra.PeirceSpine.EmergentTwoSheetBridge

/-!
## Part IV: Nilpotent Pairing Anomaly `Σ = [N_+, N_-]` to Chiral Block Gap `Gap = Σ²` (`NPA₁`–`NPA₈`)
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset

section RingHelpers

variable {B : Type*} [Ring B]

theorem sub_add_self (x y : B) : (x - y) + y = x := by
  abel

theorem add_sub_self_right (x y : B) : (x + y) - y = x := by
  abel

theorem neg_sub_eq_neg_add (a b : B) : -a - b = -(a + b) := by
  abel

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

end RingHelpers

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 1. Stage I (`NPA₁–NPA₂`): Non-Commuting Nilpotent Pairing & Parity Anomaly `Σ`
-/

/-- **Foundational Object (`NPA₁`):**
    The non-commuting nilpotent pairing / parity anomaly `Σ = [N_+, N_-]`. -/
def Sigma (N_plus : B) : B := comm N_plus (star N_plus)

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

/-- `NPA₁` Left chiral parity `+1` of `N_+` under `Σ`: `Σ * N_+ = N_+`. -/
theorem Sigma_mul_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * N_plus = N_plus := by
  dsimp [Sigma, comm]
  rw [sub_mul, h_reg, mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero, sub_zero]

/-- `NPA₁` Right chiral parity `-1` of `N_+` under `Σ`: `N_+ * Σ = -N_+`. -/
theorem N_plus_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * Sigma N_plus = -N_plus := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
      ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_sub]

/-- `NPA₁` Left chiral parity `-1` of `N_-` under `Σ`: `Σ * N_- = -N_-`. -/
theorem Sigma_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * star N_plus = -star N_plus := by
  dsimp [Sigma, comm]
  rw [sub_mul, mul_assoc N_plus (star N_plus) (star N_plus),
      star_N_plus_sq N_plus h_nil, mul_zero,
      star_N_plus_reg N_plus h_reg, zero_sub]

/-- `NPA₁` Right chiral parity `+1` of `N_-` under `Σ`: `N_- * Σ = N_-`. -/
theorem star_N_plus_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * Sigma N_plus = star N_plus := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc (star N_plus) N_plus (star N_plus),
      star_N_plus_reg N_plus h_reg,
      ← mul_assoc (star N_plus) (star N_plus) N_plus,
      star_N_plus_sq N_plus h_nil, zero_mul, sub_zero]

/-- **`NPA₂` Chiral Parity Anticommutation Anomaly (`{Σ, N_+} = 0` and `{Σ, N_-} = 0`):** -/
theorem anticomm_Sigma_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Sigma N_plus) N_plus = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_N_plus N_plus h_nil h_reg,
      N_plus_mul_Sigma N_plus h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

theorem anticomm_Sigma_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Sigma N_plus) (star N_plus) = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_star_N_plus N_plus h_nil h_reg,
      star_N_plus_mul_Sigma N_plus h_nil h_reg,
      add_comm (-star N_plus) (star N_plus),
      ← sub_eq_add_neg, sub_self]

/-!
### 2. Stage II (`NPA₃–NPA₄`): Chiral Block Operators `Φ`, `J` & Parity Anomaly Action
-/

/-- Self-adjoint chiral block pairing operator `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Skew-adjoint chiral block rotor `J = N_+ - N_-`. -/
def J (N_plus : B) : B := N_plus - star N_plus

/-- `NPA₃` The parity anomaly `Σ` rotates `Φ` into `J`: `Σ * Φ = J`. -/
theorem Sigma_mul_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * Phi N_plus = J N_plus := by
  dsimp [Phi, J]
  rw [mul_add,
      Sigma_mul_N_plus N_plus h_nil h_reg,
      Sigma_mul_star_N_plus N_plus h_nil h_reg,
      ← sub_eq_add_neg]

/-- `NPA₃` Right-multiplying `Φ` by `Σ` produces `-J`: `Φ * Σ = -J`. -/
theorem Phi_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * Sigma N_plus = -J N_plus := by
  dsimp [Phi, J]
  rw [add_mul,
      N_plus_mul_Sigma N_plus h_nil h_reg,
      star_N_plus_mul_Sigma N_plus h_nil h_reg,
      add_comm (-N_plus) (star N_plus),
      ← sub_eq_add_neg, neg_sub]

/-- `NPA₃` The parity anomaly `Σ` rotates `J` back into `Φ`: `Σ * J = Φ`. -/
theorem Sigma_mul_J (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * J N_plus = Phi N_plus := by
  dsimp [Phi, J]
  rw [mul_sub,
      Sigma_mul_N_plus N_plus h_nil h_reg,
      Sigma_mul_star_N_plus N_plus h_nil h_reg,
      sub_eq_add_neg, neg_neg]

/-- `NPA₃` Right-multiplying `J` by `Σ` produces `-Φ`: `J * Σ = -Φ`. -/
theorem J_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    J N_plus * Sigma N_plus = -Phi N_plus := by
  dsimp [Phi, J]
  rw [sub_mul,
      N_plus_mul_Sigma N_plus h_nil h_reg,
      star_N_plus_mul_Sigma N_plus h_nil h_reg,
      neg_sub_eq_neg_add]

/-- `NPA₄` The product of the chiral block operators `J` and `Φ` is the anomaly `Σ`:
    `J * Φ = Σ`. -/
theorem J_mul_Phi (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    J N_plus * Phi N_plus = Sigma N_plus := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  dsimp [J, Phi, Sigma, comm]
  calc (N_plus - star N_plus) * (N_plus + star N_plus)
    _ = (N_plus - star N_plus) * N_plus + (N_plus - star N_plus) * star N_plus := by
        rw [mul_add]
    _ = (N_plus * N_plus - star N_plus * N_plus) +
        (N_plus * star N_plus - star N_plus * star N_plus) := by
        rw [sub_mul, sub_mul]
    _ = (0 - star N_plus * N_plus) + (N_plus * star N_plus - 0) := by
        rw [h_nil, h_star_nil]
    _ = -(star N_plus * N_plus) + N_plus * star N_plus := by rw [zero_sub, sub_zero]
    _ = N_plus * star N_plus + -(star N_plus * N_plus) := by rw [add_comm]
    _ = N_plus * star N_plus - star N_plus * N_plus := by rw [← sub_eq_add_neg]

/-- **`NPA₄` Block Parity Anomaly (`{Σ, Φ} = 0` and `[Σ, Φ] = 2J`):** -/
theorem anticomm_Sigma_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Sigma N_plus) (Phi N_plus) = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_Phi N_plus h_nil h_reg,
      Phi_mul_Sigma N_plus h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

theorem comm_Sigma_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (Sigma N_plus) (Phi N_plus) = J N_plus + J N_plus := by
  dsimp [comm]
  rw [Sigma_mul_Phi N_plus h_nil h_reg,
      Phi_mul_Sigma N_plus h_nil h_reg,
      sub_eq_add_neg, neg_neg]

/-!
### 3. Stage III (`NPA₅–NPA₈`): Support & Spectral Gap as Downstream Output of `Σ` and `Φ`
-/

/-- **Downstream Support / Spectral Gap (`NPA₅`):**
    Defined directly as the square of the parity anomaly `Gap := Σ * Σ`. -/
def Gap (N_plus : B) : B := Sigma N_plus * Sigma N_plus

/-- Positive and negative chiral block projectors `P_+ = N_+ N_-` and `P_- = N_- N_+`. -/
def P_pos (N_plus : B) : B := N_plus * star N_plus
def P_neg (N_plus : B) : B := star N_plus * N_plus

/-- Global chiral parity reflection `S_P = 2P_+ - 1`. -/
def S_P (N_plus : B) : B := P_pos N_plus + P_pos N_plus - 1

/-- `NPA₅` `Gap` acts as the identity on `N_+`: `Gap * N_+ = N_+`. -/
theorem Gap_mul_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * N_plus = N_plus := by
  dsimp [Gap]
  rw [mul_assoc,
      Sigma_mul_N_plus N_plus h_nil h_reg,
      Sigma_mul_N_plus N_plus h_nil h_reg]

/-- `NPA₅` `Gap` acts as the identity on `N_-`: `Gap * N_- = N_-`. -/
theorem Gap_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * star N_plus = star N_plus := by
  dsimp [Gap]
  rw [mul_assoc,
      Sigma_mul_star_N_plus N_plus h_nil h_reg,
      mul_neg,
      Sigma_mul_star_N_plus N_plus h_nil h_reg,
      neg_neg]

/-- `NPA₅` `Gap` absorbs the anomaly `Σ`: `Gap * Σ = Σ`. -/
theorem Gap_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * Sigma N_plus = Sigma N_plus := by
  dsimp [Sigma, comm]
  rw [mul_sub,
      ← mul_assoc (Gap N_plus) N_plus (star N_plus),
      Gap_mul_N_plus N_plus h_nil h_reg,
      ← mul_assoc (Gap N_plus) (star N_plus) N_plus,
      Gap_mul_star_N_plus N_plus h_nil h_reg]

/-- **`NPA₆` Idempotency of the Anomaly Support (`Gap * Gap = Gap`):** -/
theorem Gap_idem (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * Gap N_plus = Gap N_plus := by
  calc Gap N_plus * Gap N_plus
    _ = Gap N_plus * (Sigma N_plus * Sigma N_plus) := rfl
    _ = (Gap N_plus * Sigma N_plus) * Sigma N_plus := by rw [← mul_assoc]
    _ = Sigma N_plus * Sigma N_plus := by rw [Gap_mul_Sigma N_plus h_nil h_reg]
    _ = Gap N_plus := rfl

/-- **`NPA₆` The Chiral Block Operator Turns the Anomaly into a Gap (`Φ² = Gap`):**
    Proved directly through the chiral block chain `Φ² = (Σ J) Φ = Σ (J Φ) = Σ² = Gap`. -/
theorem Phi_sq_eq_Gap (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * Phi N_plus = Gap N_plus := by
  calc Phi N_plus * Phi N_plus
    _ = (Sigma N_plus * J N_plus) * Phi N_plus := by
        rw [Sigma_mul_J N_plus h_nil h_reg]
    _ = Sigma N_plus * (J N_plus * Phi N_plus) := by rw [mul_assoc]
    _ = Sigma N_plus * Sigma N_plus := by rw [J_mul_Phi N_plus h_nil]
    _ = Gap N_plus := rfl

/-- **`NPA₇` Decomposition of `Gap` into the Chiral Block Support `P_+ + P_-` (`{N_+, N_-}`):**
    The symmetric anticommutator `{N_+, N_-}` emerges as a derived consequence of `Gap = Σ²`. -/
theorem Gap_eq_anticomm (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus = anticomm N_plus (star N_plus) := by
  dsimp [Gap, anticomm]
  calc Sigma N_plus * (N_plus * star N_plus - star N_plus * N_plus)
    _ = Sigma N_plus * (N_plus * star N_plus) -
        Sigma N_plus * (star N_plus * N_plus) := by rw [mul_sub]
    _ = (Sigma N_plus * N_plus) * star N_plus -
        (Sigma N_plus * star N_plus) * N_plus := by rw [← mul_assoc, ← mul_assoc]
    _ = N_plus * star N_plus - (-star N_plus) * N_plus := by
        rw [Sigma_mul_N_plus N_plus h_nil h_reg,
            Sigma_mul_star_N_plus N_plus h_nil h_reg]
    _ = N_plus * star N_plus + star N_plus * N_plus := by
        rw [neg_mul, sub_eq_add_neg, neg_neg]

/-- **`NPA₇` Chiral Parity Reflection Turns Anomaly into Gap (`S_P * Σ = Gap`):** -/
theorem S_P_mul_Sigma_eq_Gap (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * Sigma N_plus = Gap N_plus := by
  rw [Gap_eq_anticomm N_plus h_nil h_reg]
  dsimp [S_P, P_pos, Sigma, comm, anticomm]
  have hP_N : (N_plus * star N_plus) * (N_plus * star N_plus) = N_plus * star N_plus := by
    rw [← mul_assoc, h_reg]
  have hP_sN : (N_plus * star N_plus) * (star N_plus * N_plus) = 0 := by
    rw [mul_assoc N_plus (star N_plus) (star N_plus * N_plus),
        ← mul_assoc (star N_plus) (star N_plus) N_plus,
        star_N_plus_sq N_plus h_nil, zero_mul, mul_zero]
  calc (N_plus * star N_plus + N_plus * star N_plus - 1) *
       (N_plus * star N_plus - star N_plus * N_plus)
    _ = (N_plus * star N_plus + N_plus * star N_plus - 1) * (N_plus * star N_plus) -
        (N_plus * star N_plus + N_plus * star N_plus - 1) * (star N_plus * N_plus) := by
        rw [mul_sub]
    _ = ((N_plus * star N_plus + N_plus * star N_plus) * (N_plus * star N_plus) -
         1 * (N_plus * star N_plus)) -
        ((N_plus * star N_plus + N_plus * star N_plus) * (star N_plus * N_plus) -
         1 * (star N_plus * N_plus)) := by rw [sub_mul, sub_mul]
    _ = ((N_plus * star N_plus + N_plus * star N_plus) - N_plus * star N_plus) -
        ((0 + 0) - star N_plus * N_plus) := by
        rw [add_mul, add_mul, hP_N, hP_sN, one_mul, one_mul]
    _ = N_plus * star N_plus - -(star N_plus * N_plus) := by
        rw [add_sub_self_right, add_zero, zero_sub]
    _ = N_plus * star N_plus + star N_plus * N_plus := by
        rw [sub_eq_add_neg, neg_neg]

/-- **`NPA₈` The Chiral Block Operator Is Gapped on Its Support (`Gap * Φ = Φ` and `Φ³ = Φ`):** -/
theorem Gap_mul_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * Phi N_plus = Phi N_plus := by
  calc Gap N_plus * Phi N_plus
    _ = Sigma N_plus * (Sigma N_plus * Phi N_plus) := by dsimp [Gap]; rw [mul_assoc]
    _ = Sigma N_plus * J N_plus := by rw [Sigma_mul_Phi N_plus h_nil h_reg]
    _ = Phi N_plus := Sigma_mul_J N_plus h_nil h_reg

theorem Phi_cube_eq_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * Phi N_plus * Phi N_plus = Phi N_plus := by
  rw [Phi_sq_eq_Gap N_plus h_nil h_reg, Gap_mul_Phi N_plus h_nil h_reg]

/-- **`NPA₈` Exact Spectral Gap Equation of the Chiral Block Operator (`Φ (Φ² - 1) = 0`):**
    On its support `Gap = Φ²`, `Φ` has strictly gapped eigenvalues `±1` (`Φ² = 1` on `im Φ`)
    and `0` on the kernel, with no gapless modes. -/
theorem chiral_block_spectral_gap_eq (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * (Phi N_plus * Phi N_plus - 1) = 0 := by
  rw [mul_sub, mul_one, ← mul_assoc, Phi_cube_eq_Phi N_plus h_nil h_reg, sub_self]

end InfoGeometry.OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset
