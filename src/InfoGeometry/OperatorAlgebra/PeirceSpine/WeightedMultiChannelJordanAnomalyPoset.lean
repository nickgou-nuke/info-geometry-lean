/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Order.Basic
import InfoGeometry.Core.JordanAssociatorRing

/-!
# Grade-3 Weighted Multi-Channel Jordan Associator Anomaly Poset (`WJA₁`–`WJA₁₀`)

In a background-free associative `[Ring B] [StarRing B]`, evaluating the Grade-3 Jordan
associator anomaly
`JordanAssoc X Y Z := {{X, Y}, Z} - {X, {Y, Z}}`
on the weighted multi-channel chiral blocks `Φ_w₂ = c_a Φ(N_a) + c_b Φ(N_b)` and
`J_w₂ = c_a J(N_a) + c_b J(N_b)` reveals an exact algebraic progression across Grades 1, 2, and 3:
1. **Grade-1 Chiral Block Anticommutation & Grade-2 Quadratic Gap (`WJA₁`–`WJA₃`)**:
   `{Φ_w₂, J_w₂} = 0`, `[J_w₂, Φ_w₂] = 2 Σ_w₂`, `Φ_w₂² = +Gap_w₂`, and `J_w₂² = -Gap_w₂`.
2. **Grade-3 Cubic Scaling of the Weighted Jordan Associator (`WJA₄`–`WJA₆`)**:
   `JordanAssoc Φ_w₂ Φ_w₂ J_w₂ = 4 J_w₂⁽³⁾`,
   `JordanAssoc J_w₂ Φ_w₂ Φ_w₂ = -4 J_w₂⁽³⁾`,
   `JordanAssoc J_w₂ J_w₂ Φ_w₂ = -4 Φ_w₂⁽³⁾`, and
   `JordanAssoc Φ_w₂ J_w₂ J_w₂ = +4 Φ_w₂⁽³⁾`.
3. **Channel Additivity, Double-Commutator Curvature Bridge, & Projective Filtering (`WJA₇`–`WJA₉`)**:
   `JordanAssoc Φ_w₂ Φ_w₂ J_w₂ = JordanAssoc (c_a Φ N_a) (c_a Φ N_a) (c_a J N_a) + JordanAssoc (c_b Φ N_b) (c_b Φ N_b) (c_b J N_b)`,
   `JordanAssoc Φ_w₂ Φ_w₂ J_w₂ = [[J_w₂, Φ_w₂], Φ_w₂]`, and
   `Gap N_a * JordanAssoc Φ_w₂ Φ_w₂ J_w₂ = JordanAssoc (c_a Φ N_a) (c_a Φ N_a) (c_a J N_a)`.
4. **Cyclotomic Galois Synchronization at Grade 3 (`WJA₁₀`)**:
   When weighted by conjugate roots `(u, 1 - u)` of `Φ₆(u) = u² - u + 1 = 0`, both cubes satisfy
   `u³ = -1` and `(1 - u)³ = -1`, synchronizing the Grade-3 Jordan associator into the phase-free
   singlet `-4 (J N_a + J N_b)`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.WeightedMultiChannelJordanAnomalyPoset

/-- The 10-stage causal poset of the Grade-3 Weighted Multi-Channel Jordan Associator Anomaly (`WJA₁`–`WJA₁₀`). -/
inductive WeightedMultiChannelJordanAnomalyStage : Type
  | WJA1_SingleChannelJordanAssociatorBaseline
  | WJA2_WeightedSingleChannelCubicScaling
  | WJA3_Grade1AnticommutationAndGrade2QuadraticGap
  | WJA4_Grade3CubicActionOfGapAndSigma
  | WJA5_WeightedMultiChannelJordanAssocPhiPhiJ
  | WJA6_DualRotorWeightedJordanAssocJJPhi
  | WJA7_MultiChannelJordanAssociatorAdditivity
  | WJA8_CurvatureDoubleCommutatorBridge
  | WJA9_ChannelSelectiveProjectiveFiltering
  | WJA10_CyclotomicGrade3GaloisSynchronization
  deriving DecidableEq, Repr

namespace WeightedMultiChannelJordanAnomalyStage

/-- Integer rank of each stage in `WJA₁ ≺ ⋯ ≺ WJA₁₀`. -/
@[reducible] def rank : WeightedMultiChannelJordanAnomalyStage → Nat
  | .WJA1_SingleChannelJordanAssociatorBaseline => 0
  | .WJA2_WeightedSingleChannelCubicScaling => 1
  | .WJA3_Grade1AnticommutationAndGrade2QuadraticGap => 2
  | .WJA4_Grade3CubicActionOfGapAndSigma => 3
  | .WJA5_WeightedMultiChannelJordanAssocPhiPhiJ => 4
  | .WJA6_DualRotorWeightedJordanAssocJJPhi => 5
  | .WJA7_MultiChannelJordanAssociatorAdditivity => 6
  | .WJA8_CurvatureDoubleCommutatorBridge => 7
  | .WJA9_ChannelSelectiveProjectiveFiltering => 8
  | .WJA10_CyclotomicGrade3GaloisSynchronization => 9

/-- Strict causal precedence relation `s₁ ≺ s₂`. -/
@[reducible] def causalEdge (s₁ s₂ : WeightedMultiChannelJordanAnomalyStage) : Prop :=
  s₁.rank < s₂.rank

/-- Reflexive-transitive causal order `s₁ ≼ s₂`. -/
@[reducible] def causalLe (s₁ s₂ : WeightedMultiChannelJordanAnomalyStage) : Prop :=
  s₁.rank ≤ s₂.rank

instance instLT : LT WeightedMultiChannelJordanAnomalyStage := ⟨causalEdge⟩
instance instLE : LE WeightedMultiChannelJordanAnomalyStage := ⟨causalLe⟩

instance instLinearOrder : LinearOrder WeightedMultiChannelJordanAnomalyStage where
  le := causalLe
  lt := causalEdge
  le_refl a := Nat.le_refl a.rank
  le_trans _ _ _ hab hbc := Nat.le_trans hab hbc
  lt_iff_le_not_ge a b := Nat.lt_iff_le_not_le
  le_antisymm a b hab hba := by
    cases a <;> cases b <;> first | rfl | cases (Nat.le_antisymm hab hba)
  le_total a b := Nat.le_total a.rank b.rank
  toDecidableLE a b := Nat.decLe a.rank b.rank
  toDecidableLT a b := Nat.decLt a.rank b.rank
  toDecidableEq := inferInstance

theorem poset_chain_and_acyclicity :
    (causalEdge .WJA1_SingleChannelJordanAssociatorBaseline .WJA2_WeightedSingleChannelCubicScaling ∧
     causalEdge .WJA2_WeightedSingleChannelCubicScaling .WJA3_Grade1AnticommutationAndGrade2QuadraticGap ∧
     causalEdge .WJA3_Grade1AnticommutationAndGrade2QuadraticGap .WJA4_Grade3CubicActionOfGapAndSigma ∧
     causalEdge .WJA4_Grade3CubicActionOfGapAndSigma .WJA5_WeightedMultiChannelJordanAssocPhiPhiJ ∧
     causalEdge .WJA5_WeightedMultiChannelJordanAssocPhiPhiJ .WJA6_DualRotorWeightedJordanAssocJJPhi ∧
     causalEdge .WJA6_DualRotorWeightedJordanAssocJJPhi .WJA7_MultiChannelJordanAssociatorAdditivity ∧
     causalEdge .WJA7_MultiChannelJordanAssociatorAdditivity .WJA8_CurvatureDoubleCommutatorBridge ∧
     causalEdge .WJA8_CurvatureDoubleCommutatorBridge .WJA9_ChannelSelectiveProjectiveFiltering ∧
     causalEdge .WJA9_ChannelSelectiveProjectiveFiltering .WJA10_CyclotomicGrade3GaloisSynchronization) ∧
    (∀ s : WeightedMultiChannelJordanAnomalyStage, ¬ causalEdge s s) := by
  refine ⟨by decide, ?_⟩
  intro s
  cases s <;> decide

end WeightedMultiChannelJordanAnomalyStage

/-!
### 0. Universal Additive, Weight-Commutation, and Cross-Orthogonality Helpers
-/

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

theorem add_sub_assoc' (a b c : B) : a + (b - c) = (a + b) - c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]

theorem sub_add_sub_cancel' (a b c : B) : (a - b) + (b - c) = a - c := by
  rw [add_sub_assoc', sub_add_self]

theorem one_sub_sub_one (u : B) : (1 - u) - 1 = -u := by
  calc (1 - u) - 1
    _ = (1 + -u) + -1 := by rw [sub_eq_add_neg, sub_eq_add_neg]
    _ = (-u + 1) + -1 := by rw [add_comm 1 (-u)]
    _ = -u + (1 + -1) := by rw [add_assoc]
    _ = -u + (1 - 1) := by rw [← sub_eq_add_neg]
    _ = -u + 0 := by rw [sub_self]
    _ = -u := by rw [add_zero]

theorem add_add_add_comm' (a b c d : B) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc (a + b) + (c + d)
    _ = a + (b + (c + d)) := by rw [add_assoc a b (c + d)]
    _ = a + ((b + c) + d) := by rw [← add_assoc b c d]
    _ = a + ((c + b) + d) := by rw [add_comm b c]
    _ = a + (c + (b + d)) := by rw [add_assoc c b d]
    _ = (a + c) + (b + d) := by rw [← add_assoc a c (b + d)]

/-- Fourfold additive multiple `4x = (x + x) + (x + x)`. -/
def quad (x : B) : B := (x + x) + (x + x)

/-- Cubic power `c³ = (c * c) * c`. -/
def cube (c : B) : B := (c * c) * c

theorem quad_add (x y : B) : quad (x + y) = quad x + quad y := by
  dsimp [quad]
  rw [add_add_add_comm' x y x y,
      add_add_add_comm' (x + x) (y + y) (x + x) (y + y)]

theorem quad_neg (x : B) : quad (-x) = -quad x := by
  dsimp [quad]
  rw [← neg_add_rev, ← neg_add_rev]

theorem quad_mul_left (c x : B) : c * quad x = quad (c * x) := by
  dsimp [quad]
  rw [mul_add, mul_add]

/-- If `A₁ * B₂ = 0` and `A₂ * B₁ = 0`, then `(A₁ + A₂) * (B₁ + B₂) = A₁ * B₁ + A₂ * B₂`. -/
theorem mul_add_of_cross_orthog (A₁ A₂ B₁ B₂ : B)
    (h12 : A₁ * B₂ = 0) (h21 : A₂ * B₁ = 0) :
    (A₁ + A₂) * (B₁ + B₂) = A₁ * B₁ + A₂ * B₂ := by
  calc (A₁ + A₂) * (B₁ + B₂)
    _ = (A₁ + A₂) * B₁ + (A₁ + A₂) * B₂ := by rw [mul_add]
    _ = (A₁ * B₁ + A₂ * B₁) + (A₁ * B₂ + A₂ * B₂) := by rw [add_mul, add_mul]
    _ = (A₁ * B₁ + 0) + (0 + A₂ * B₂) := by rw [h21, h12]
    _ = A₁ * B₁ + A₂ * B₂ := by rw [add_zero, zero_add]

theorem comm_sq_of_comm (c X : B) (hX : c * X = X * c) :
    (c * c) * X = X * (c * c) := by
  calc (c * c) * X
    _ = c * (c * X) := by rw [mul_assoc]
    _ = c * (X * c) := by rw [hX]
    _ = (c * X) * c := by rw [← mul_assoc]
    _ = (X * c) * c := by rw [hX]
    _ = X * (c * c) := by rw [mul_assoc]

/-- Universal quadratic weight factorization: `(c * X) * (c * Y) = (c * c) * (X * Y)`. -/
theorem weight_mul_weight (c X Y : B) (hX : c * X = X * c) :
    (c * X) * (c * Y) = (c * c) * (X * Y) := by
  calc (c * X) * (c * Y)
    _ = c * (X * (c * Y)) := by rw [mul_assoc]
    _ = c * ((X * c) * Y) := by rw [← mul_assoc X c Y]
    _ = c * ((c * X) * Y) := by rw [← hX]
    _ = (c * c) * (X * Y) := by rw [mul_assoc c X Y, ← mul_assoc c c (X * Y)]

/-- Universal cubic weight factorization (left square): `((c * c) * X) * (c * Y) = c³ * (X * Y)`. -/
theorem sq_weight_mul_right (c X Y : B) (hX : c * X = X * c) :
    ((c * c) * X) * (c * Y) = cube c * (X * Y) := by
  dsimp [cube]
  calc ((c * c) * X) * (c * Y)
    _ = (c * c) * (X * (c * Y)) := by rw [mul_assoc]
    _ = (c * c) * ((X * c) * Y) := by rw [← mul_assoc X c Y]
    _ = (c * c) * ((c * X) * Y) := by rw [← hX]
    _ = ((c * c) * (c * X)) * Y := by rw [← mul_assoc (c * c) (c * X) Y]
    _ = (((c * c) * c) * X) * Y := by rw [← mul_assoc (c * c) c X]
    _ = ((c * c) * c) * (X * Y) := by rw [mul_assoc]

/-- Universal cubic weight factorization (right square): `(c * X) * ((c * c) * Y) = c³ * (X * Y)`. -/
theorem mul_sq_weight_right (c X Y : B) (hX : c * X = X * c) :
    (c * X) * ((c * c) * Y) = cube c * (X * Y) := by
  have hX2 := comm_sq_of_comm c X hX
  dsimp [cube]
  calc (c * X) * ((c * c) * Y)
    _ = ((c * X) * (c * c)) * Y := by rw [← mul_assoc]
    _ = (c * (X * (c * c))) * Y := by rw [mul_assoc c X (c * c)]
    _ = (c * ((c * c) * X)) * Y := by rw [← hX2]
    _ = ((c * (c * c)) * X) * Y := by rw [← mul_assoc c (c * c) X]
    _ = (((c * c) * c) * X) * Y := by rw [← mul_assoc c c c]
    _ = ((c * c) * c) * (X * Y) := by rw [mul_assoc]

/-- Universal weighted cross-channel annihilation: if `X_a * Y_b = 0` and `w_b` commutes
    with `Y_b`, then `(w_a * X_a) * (w_b * Y_b) = 0` for any left weight `w_a`. -/
theorem weighted_cross_zero (w_a X_a w_b Y_b : B)
    (hXY : X_a * Y_b = 0) (hw_b : w_b * Y_b = Y_b * w_b) :
    (w_a * X_a) * (w_b * Y_b) = 0 := by
  calc (w_a * X_a) * (w_b * Y_b)
    _ = (w_a * X_a) * (Y_b * w_b) := by rw [hw_b]
    _ = w_a * (X_a * (Y_b * w_b)) := by rw [mul_assoc]
    _ = w_a * ((X_a * Y_b) * w_b) := by rw [← mul_assoc X_a Y_b w_b]
    _ = w_a * (0 * w_b) := by rw [hXY]
    _ = 0 := by rw [zero_mul, mul_zero]

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- The Grade-3 Jordan Associator Anomaly `JordanAssoc X Y Z = {{X, Y}, Z} - {X, {Y, Z}}`. -/
def JordanAssoc (X Y Z : B) : B :=
  anticomm (anticomm X Y) Z - anticomm X (anticomm Y Z)

/-- The local unnormalized Jordan associator agrees with the shared core
double-commutator formula. This provides the commutator interpretation for
all weighted and unweighted operators in this module. -/
theorem JordanAssoc_eq_double_commutator (X Y Z : B) :
    JordanAssoc X Y Z =
      Y * (X * Z - Z * X) - (X * Z - Z * X) * Y := by
  dsimp [JordanAssoc, anticomm]
  exact InfoGeometry.Core.JordanAssociator.symm_associator_eq_double_commutator
    X Y Z

theorem anticomm_zero_right (X : B) : anticomm X 0 = 0 := by
  dsimp [anticomm]; rw [mul_zero, zero_mul, add_zero]

theorem anticomm_zero_left (X : B) : anticomm 0 X = 0 := by
  dsimp [anticomm]; rw [zero_mul, mul_zero, add_zero]

/-- The 6th cyclotomic polynomial `Φ₆(u) = u² - u + 1` (base of `Φ₁₂` and `Φ₂₄`). -/
def Phi6 (u : B) : B := u * u - u + 1

theorem cube_eq_neg_one_of_Phi6 (u : B) (h_cyc : Phi6 u = 0) :
    cube u = -1 := by
  have h_sum : (u + 1) * Phi6 u = cube u + 1 := by
    dsimp [Phi6, cube]
    calc (u + 1) * (u * u - u + 1)
      _ = (u + 1) * (u * u - u) + (u + 1) * 1 := by rw [mul_add]
      _ = (u * (u * u - u) + 1 * (u * u - u)) + (u + 1) := by
          rw [add_mul, mul_one]
      _ = ((u * (u * u) - u * u) + (u * u - u)) + (u + 1) := by
          rw [mul_sub, one_mul]
      _ = (u * (u * u) - u) + (u + 1) := by rw [sub_add_sub_cancel']
      _ = ((u * (u * u) - u) + u) + 1 := by rw [← add_assoc]
      _ = u * (u * u) + 1 := by rw [sub_add_self]
      _ = (u * u) * u + 1 := by rw [← mul_assoc]
  have h1 : cube u + 1 = 0 := by rw [← h_sum, h_cyc, mul_zero]
  calc cube u
    _ = (cube u + 1) - 1 := by rw [← add_sub_assoc', sub_self, add_zero]
    _ = 0 - 1 := by rw [h1]
    _ = -1 := by rw [zero_sub]

theorem Phi6_galois_conj (u : B) : Phi6 (1 - u) = Phi6 u := by
  dsimp [Phi6]
  have h_step : (1 - u) * (1 - u) - (1 - u) = u * u - u := by
    calc (1 - u) * (1 - u) - (1 - u)
      _ = (1 - u) * (1 - u) - (1 - u) * 1 := by rw [mul_one (1 - u)]
      _ = (1 - u) * ((1 - u) - 1) := by rw [← mul_sub]
      _ = (1 - u) * (-u) := by rw [one_sub_sub_one]
      _ = -((1 - u) * u) := by rw [mul_neg]
      _ = -(1 * u - u * u) := by rw [sub_mul]
      _ = -(u - u * u) := by rw [one_mul]
      _ = u * u - u := by rw [neg_sub]
  rw [h_step]

end RingHelpers

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 1. Single-Channel Operators & Baseline Jordan Associator (`WJA₁–WJA₂`)
-/

/-- Foundational parity anomaly `Σ(N) = [N, N*]`. -/
def Sigma (N : B) : B := comm N (star N)

/-- Self-adjoint chiral block operator `Φ(N) = N + N*`. -/
def Phi (N : B) : B := N + star N

/-- Skew-adjoint chiral rotor `J(N) = N - N*`. -/
def J (N : B) : B := N - star N

/-- Downstream support / spectral gap `Gap(N) = Σ(N)²`. -/
def Gap (N : B) : B := Sigma N * Sigma N

theorem star_N_sq (N : B) (h_nil : N * N = 0) :
    star N * star N = 0 := by
  rw [← star_mul, h_nil, star_zero]

theorem star_N_reg (N : B) (h_reg : N * star N * N = N) :
    star N * N * star N = star N := by
  have h := congrArg star h_reg
  rw [star_mul, star_mul, star_star, ← mul_assoc] at h
  exact h

theorem Sigma_mul_N (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * N = N := by
  dsimp [Sigma, comm]
  rw [sub_mul, h_reg, mul_assoc (star N) N N, h_nil, mul_zero, sub_zero]

theorem N_mul_Sigma (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    N * Sigma N = -N := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc N N (star N), h_nil, zero_mul,
      ← mul_assoc N (star N) N, h_reg, zero_sub]

theorem Sigma_mul_star_N (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * star N = -star N := by
  dsimp [Sigma, comm]
  rw [sub_mul, mul_assoc N (star N) (star N),
      star_N_sq N h_nil, mul_zero,
      star_N_reg N h_reg, zero_sub]

theorem star_N_mul_Sigma (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    star N * Sigma N = star N := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc (star N) N (star N),
      star_N_reg N h_reg,
      ← mul_assoc (star N) (star N) N,
      star_N_sq N h_nil, zero_mul, sub_zero]

theorem Sigma_mul_Phi (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * Phi N = J N := by
  dsimp [Phi, J]
  rw [mul_add, Sigma_mul_N N h_nil h_reg, Sigma_mul_star_N N h_nil h_reg,
      ← sub_eq_add_neg]

theorem Phi_mul_Sigma (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Phi N * Sigma N = -J N := by
  dsimp [Phi, J]
  rw [add_mul, N_mul_Sigma N h_nil h_reg, star_N_mul_Sigma N h_nil h_reg,
      add_comm (-N) (star N), ← sub_eq_add_neg, neg_sub]

theorem Sigma_mul_J (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * J N = Phi N := by
  dsimp [Phi, J]
  rw [mul_sub, Sigma_mul_N N h_nil h_reg, Sigma_mul_star_N N h_nil h_reg,
      sub_eq_add_neg, neg_neg]

theorem J_mul_Sigma (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    J N * Sigma N = -Phi N := by
  dsimp [Phi, J]
  rw [sub_mul, N_mul_Sigma N h_nil h_reg, star_N_mul_Sigma N h_nil h_reg,
      sub_eq_add_neg, ← neg_add_rev, add_comm (star N) N]

theorem J_mul_Phi (N : B) (h_nil : N * N = 0) :
    J N * Phi N = Sigma N := by
  have h_star_nil := star_N_sq N h_nil
  dsimp [J, Phi, Sigma, comm]
  calc (N - star N) * (N + star N)
    _ = (N - star N) * N + (N - star N) * star N := by rw [mul_add]
    _ = (N * N - star N * N) + (N * star N - star N * star N) := by
        rw [sub_mul, sub_mul]
    _ = (0 - star N * N) + (N * star N - 0) := by rw [h_nil, h_star_nil]
    _ = -(star N * N) + N * star N := by rw [zero_sub, sub_zero]
    _ = N * star N + -(star N * N) := by rw [add_comm]
    _ = N * star N - star N * N := by rw [← sub_eq_add_neg]

theorem Phi_mul_J (N : B) (h_nil : N * N = 0) :
    Phi N * J N = -Sigma N := by
  have h_star_nil := star_N_sq N h_nil
  dsimp [J, Phi, Sigma, comm]
  calc (N + star N) * (N - star N)
    _ = (N + star N) * N - (N + star N) * star N := by rw [mul_sub]
    _ = (N * N + star N * N) - (N * star N + star N * star N) := by
        rw [add_mul, add_mul]
    _ = (0 + star N * N) - (N * star N + 0) := by rw [h_nil, h_star_nil]
    _ = star N * N - N * star N := by rw [zero_add, add_zero]
    _ = -(N * star N - star N * N) := by rw [neg_sub]

theorem Phi_sq_eq_Gap (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Phi N * Phi N = Gap N := by
  calc Phi N * Phi N
    _ = (Sigma N * J N) * Phi N := by rw [Sigma_mul_J N h_nil h_reg]
    _ = Sigma N * (J N * Phi N) := by rw [mul_assoc]
    _ = Sigma N * Sigma N := by rw [J_mul_Phi N h_nil]
    _ = Gap N := rfl

theorem J_sq_eq_neg_Gap (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    J N * J N = -Gap N := by
  calc J N * J N
    _ = (Sigma N * Phi N) * J N := by rw [Sigma_mul_Phi N h_nil h_reg]
    _ = Sigma N * (Phi N * J N) := by rw [mul_assoc]
    _ = Sigma N * (-Sigma N) := by rw [Phi_mul_J N h_nil]
    _ = -(Sigma N * Sigma N) := by rw [mul_neg]
    _ = -Gap N := rfl

theorem Gap_mul_Phi (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * Phi N = Phi N := by
  calc Gap N * Phi N
    _ = Sigma N * (Sigma N * Phi N) := by dsimp [Gap]; rw [mul_assoc]
    _ = Sigma N * J N := by rw [Sigma_mul_Phi N h_nil h_reg]
    _ = Phi N := Sigma_mul_J N h_nil h_reg

theorem Phi_mul_Gap (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Phi N * Gap N = Phi N := by
  calc Phi N * Gap N
    _ = (Phi N * Sigma N) * Sigma N := by dsimp [Gap]; rw [← mul_assoc]
    _ = (-J N) * Sigma N := by rw [Phi_mul_Sigma N h_nil h_reg]
    _ = -(J N * Sigma N) := by rw [neg_mul]
    _ = -(-Phi N) := by rw [J_mul_Sigma N h_nil h_reg]
    _ = Phi N := by rw [neg_neg]

theorem Gap_mul_J (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * J N = J N := by
  calc Gap N * J N
    _ = Sigma N * (Sigma N * J N) := by dsimp [Gap]; rw [mul_assoc]
    _ = Sigma N * Phi N := by rw [Sigma_mul_J N h_nil h_reg]
    _ = J N := Sigma_mul_Phi N h_nil h_reg

theorem J_mul_Gap (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    J N * Gap N = J N := by
  calc J N * Gap N
    _ = (J N * Sigma N) * Sigma N := by dsimp [Gap]; rw [← mul_assoc]
    _ = (-Phi N) * Sigma N := by rw [J_mul_Sigma N h_nil h_reg]
    _ = -(Phi N * Sigma N) := by rw [neg_mul]
    _ = -(-J N) := by rw [Phi_mul_Sigma N h_nil h_reg]
    _ = J N := by rw [neg_neg]

theorem anticomm_Phi_J (N : B) (h_nil : N * N = 0) :
    anticomm (Phi N) (J N) = 0 := by
  dsimp [anticomm]
  rw [Phi_mul_J N h_nil, J_mul_Phi N h_nil, add_comm (-Sigma N), ← sub_eq_add_neg, sub_self]

theorem anticomm_J_Phi (N : B) (h_nil : N * N = 0) :
    anticomm (J N) (Phi N) = 0 := by
  dsimp [anticomm]
  rw [J_mul_Phi N h_nil, Phi_mul_J N h_nil, ← sub_eq_add_neg, sub_self]

/-- **`WJA₁` Single-Channel Jordan Associator (`JordanAssoc (Φ N) (Φ N) (J N) = 4 J N`):** -/
theorem JordanAssoc_Phi_Phi_J (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    JordanAssoc (Phi N) (Phi N) (J N) = quad (J N) := by
  have h_self : anticomm (Phi N) (Phi N) = Gap N + Gap N := by
    dsimp [anticomm]; rw [Phi_sq_eq_Gap N h_nil h_reg]
  dsimp [JordanAssoc]
  rw [h_self, anticomm_Phi_J N h_nil, anticomm_zero_right, sub_zero]
  dsimp [anticomm, quad]
  rw [add_mul, mul_add, Gap_mul_J N h_nil h_reg, J_mul_Gap N h_nil h_reg]

/-- **`WJA₁` Dual Single-Channel Jordan Associator (`JordanAssoc (J N) (J N) (Φ N) = -4 Φ N`):** -/
theorem JordanAssoc_J_J_Phi (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    JordanAssoc (J N) (J N) (Phi N) = -quad (Phi N) := by
  have h_self : anticomm (J N) (J N) = -Gap N + -Gap N := by
    dsimp [anticomm]; rw [J_sq_eq_neg_Gap N h_nil h_reg]
  dsimp [JordanAssoc]
  rw [h_self, anticomm_J_Phi N h_nil, anticomm_zero_right, sub_zero]
  dsimp [anticomm]
  rw [add_mul, mul_add, neg_mul, mul_neg,
      Gap_mul_Phi N h_nil h_reg, Phi_mul_Gap N h_nil h_reg]
  exact quad_neg (Phi N)

theorem comm_weight_Phi (c N : B)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    c * Phi N = Phi N * c := by
  dsimp [Phi]; rw [mul_add, add_mul, hc, hcs]

theorem comm_weight_J (c N : B)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    c * J N = J N * c := by
  dsimp [J]; rw [mul_sub, sub_mul, hc, hcs]

theorem comm_weight_Sigma (c N : B)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    c * Sigma N = Sigma N * c := by
  dsimp [Sigma, comm]
  calc c * (N * star N - star N * N)
    _ = c * (N * star N) - c * (star N * N) := by rw [mul_sub]
    _ = (c * N) * star N - (c * star N) * N := by rw [← mul_assoc, ← mul_assoc]
    _ = (N * c) * star N - (star N * c) * N := by rw [hc, hcs]
    _ = N * (c * star N) - star N * (c * N) := by rw [mul_assoc, mul_assoc]
    _ = N * (star N * c) - star N * (N * c) := by rw [hcs, hc]
    _ = (N * star N) * c - (star N * N) * c := by rw [← mul_assoc, ← mul_assoc]
    _ = (N * star N - star N * N) * c := by rw [← sub_mul]

theorem comm_weight_Gap (c N : B)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    c * Gap N = Gap N * c := by
  have hcS := comm_weight_Sigma c N hc hcs
  dsimp [Gap]
  calc c * (Sigma N * Sigma N)
    _ = (c * Sigma N) * Sigma N := by rw [← mul_assoc]
    _ = (Sigma N * c) * Sigma N := by rw [hcS]
    _ = Sigma N * (c * Sigma N) := by rw [mul_assoc]
    _ = Sigma N * (Sigma N * c) := by rw [hcS]
    _ = (Sigma N * Sigma N) * c := by rw [← mul_assoc]

/-- **`WJA₂` Weighted Single-Channel Cubic Scaling of `JordanAssoc`:**
    `JordanAssoc (c Φ N) (c Φ N) (c J N) = 4 (c³ J N) = c³ JordanAssoc (Φ N) (Φ N) (J N)`. -/
theorem JordanAssoc_weighted_single_Phi_Phi_J (c N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    JordanAssoc (c * Phi N) (c * Phi N) (c * J N) = quad (cube c * J N) := by
  have hcPhi := comm_weight_Phi c N hc hcs
  have hcG := comm_weight_Gap c N hc hcs
  have h_self : anticomm (c * Phi N) (c * Phi N) =
      (c * c) * Gap N + (c * c) * Gap N := by
    dsimp [anticomm]
    rw [weight_mul_weight c (Phi N) (Phi N) hcPhi, Phi_sq_eq_Gap N h_nil h_reg]
  have h_anti : anticomm (c * Phi N) (c * J N) = 0 := by
    dsimp [anticomm]
    rw [weight_mul_weight c (Phi N) (J N) hcPhi,
        weight_mul_weight c (J N) (Phi N) (comm_weight_J c N hc hcs),
        Phi_mul_J N h_nil, J_mul_Phi N h_nil, mul_neg,
        add_comm (-((c * c) * Sigma N)), ← sub_eq_add_neg, sub_self]
  dsimp [JordanAssoc]
  rw [h_self, h_anti, anticomm_zero_right, sub_zero]
  dsimp [anticomm, quad]
  rw [add_mul, mul_add,
      sq_weight_mul_right c (Gap N) (J N) hcG,
      mul_sq_weight_right c (J N) (Gap N) (comm_weight_J c N hc hcs),
      Gap_mul_J N h_nil h_reg, J_mul_Gap N h_nil h_reg]

/-- **`WJA₂` Dual Weighted Single-Channel Cubic Scaling of `JordanAssoc`:**
    `JordanAssoc (c J N) (c J N) (c Φ N) = -4 (c³ Φ N)`. -/
theorem JordanAssoc_weighted_single_J_J_Phi (c N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    JordanAssoc (c * J N) (c * J N) (c * Phi N) = -quad (cube c * Phi N) := by
  have hcJ := comm_weight_J c N hc hcs
  have hcG := comm_weight_Gap c N hc hcs
  have h_self : anticomm (c * J N) (c * J N) =
      -((c * c) * Gap N) + -((c * c) * Gap N) := by
    dsimp [anticomm]
    rw [weight_mul_weight c (J N) (J N) hcJ, J_sq_eq_neg_Gap N h_nil h_reg, mul_neg]
  have h_anti : anticomm (c * J N) (c * Phi N) = 0 := by
    dsimp [anticomm]
    rw [weight_mul_weight c (J N) (Phi N) hcJ,
        weight_mul_weight c (Phi N) (J N) (comm_weight_Phi c N hc hcs),
        J_mul_Phi N h_nil, Phi_mul_J N h_nil, mul_neg, ← sub_eq_add_neg, sub_self]
  dsimp [JordanAssoc]
  rw [h_self, h_anti, anticomm_zero_right, sub_zero]
  dsimp [anticomm]
  rw [add_mul, mul_add, neg_mul, mul_neg,
      sq_weight_mul_right c (Gap N) (Phi N) hcG,
      mul_sq_weight_right c (Phi N) (Gap N) (comm_weight_Phi c N hc hcs),
      Gap_mul_Phi N h_nil h_reg, Phi_mul_Gap N h_nil h_reg]
  exact quad_neg (cube c * Phi N)

/-!
### 2. Multi-Channel Cross-Orthogonality & Two-Channel Weighted Definitions (`WJA₃`)
-/

theorem star_N_a_mul_star_N_b (N_a N_b : B) (h_ba : N_b * N_a = 0) :
    star N_a * star N_b = 0 := by
  rw [← star_mul, h_ba, star_zero]

theorem N_b_mul_star_N_a (N_a N_b : B) (h_asb : N_a * star N_b = 0) :
    N_b * star N_a = 0 := by
  have h := congrArg star h_asb
  rw [star_mul, star_star, star_zero] at h
  exact h

theorem star_N_b_mul_N_a (N_a N_b : B) (h_sab : star N_a * N_b = 0) :
    star N_b * N_a = 0 := by
  have h := congrArg star h_sab
  rw [star_mul, star_star, star_zero] at h
  exact h

theorem Phi_mul_Phi_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Phi N_a * Phi N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  dsimp [Phi]
  rw [mul_add, add_mul, add_mul, h_ab, h_sab, h_asb, h_sasb, add_zero, add_zero]

theorem J_mul_Phi_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    J N_a * Phi N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  dsimp [J, Phi]
  rw [mul_add, sub_mul, sub_mul, h_ab, h_sab, h_asb, h_sasb, sub_self, add_zero]

theorem Phi_mul_J_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Phi N_a * J N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  dsimp [Phi, J]
  rw [mul_sub, add_mul, add_mul, h_ab, h_sab, h_asb, h_sasb, add_zero, sub_self]

theorem J_mul_J_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    J N_a * J N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  dsimp [J]
  rw [mul_sub, sub_mul, sub_mul, h_ab, h_sab, h_asb, h_sasb, sub_self]

theorem Sigma_mul_Phi_orthog (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Sigma N_a * Phi N_b = 0 := by
  rw [← J_mul_Phi N_a h_nil_a, mul_assoc,
      Phi_mul_Phi_orthog N_a N_b h_ab h_ba h_asb h_sab, mul_zero]

theorem Phi_mul_Sigma_orthog (N_a N_b : B)
    (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Phi N_a * Sigma N_b = 0 := by
  rw [← J_mul_Phi N_b h_nil_b, ← mul_assoc,
      Phi_mul_J_orthog N_a N_b h_ab h_ba h_asb h_sab, zero_mul]

theorem Sigma_mul_J_orthog (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Sigma N_a * J N_b = 0 := by
  rw [← J_mul_Phi N_a h_nil_a, mul_assoc,
      Phi_mul_J_orthog N_a N_b h_ab h_ba h_asb h_sab, mul_zero]

theorem J_mul_Sigma_orthog (N_a N_b : B)
    (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    J N_a * Sigma N_b = 0 := by
  rw [← J_mul_Phi N_b h_nil_b, ← mul_assoc,
      J_mul_J_orthog N_a N_b h_ab h_ba h_asb h_sab, zero_mul]

theorem Gap_mul_Phi_orthog (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Gap N_a * Phi N_b = 0 := by
  dsimp [Gap]
  rw [mul_assoc, Sigma_mul_Phi_orthog N_a N_b h_nil_a h_ab h_ba h_asb h_sab, mul_zero]

theorem Phi_mul_Gap_orthog (N_a N_b : B)
    (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Phi N_a * Gap N_b = 0 := by
  dsimp [Gap]
  rw [← mul_assoc, Phi_mul_Sigma_orthog N_a N_b h_nil_b h_ab h_ba h_asb h_sab, zero_mul]

theorem Gap_mul_J_orthog (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Gap N_a * J N_b = 0 := by
  dsimp [Gap]
  rw [mul_assoc, Sigma_mul_J_orthog N_a N_b h_nil_a h_ab h_ba h_asb h_sab, mul_zero]

theorem J_mul_Gap_orthog (N_a N_b : B)
    (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    J N_a * Gap N_b = 0 := by
  dsimp [Gap]
  rw [← mul_assoc, J_mul_Sigma_orthog N_a N_b h_nil_b h_ab h_ba h_asb h_sab, zero_mul]

/-- Two-channel weighted chiral block operator `Φ_w₂ = c_a Φ(N_a) + c_b Φ(N_b)`. -/
def Phi_w₂ (c_a N_a c_b N_b : B) : B := c_a * Phi N_a + c_b * Phi N_b

/-- Two-channel weighted chiral rotor `J_w₂ = c_a J(N_a) + c_b J(N_b)`. -/
def J_w₂ (c_a N_a c_b N_b : B) : B := c_a * J N_a + c_b * J N_b

/-- Two-channel quadratic weighted parity anomaly `Σ_w₂ = c_a² Σ(N_a) + c_b² Σ(N_b)`. -/
def Sigma_w₂ (c_a N_a c_b N_b : B) : B :=
  (c_a * c_a) * Sigma N_a + (c_b * c_b) * Sigma N_b

/-- Two-channel quadratic weighted spectral gap `Gap_w₂ = c_a² Gap(N_a) + c_b² Gap(N_b)`. -/
def Gap_w₂ (c_a N_a c_b N_b : B) : B :=
  (c_a * c_a) * Gap N_a + (c_b * c_b) * Gap N_b

/-- Two-channel cubic weighted chiral block `Φ_w₂⁽³⁾ = c_a³ Φ(N_a) + c_b³ Φ(N_b)`. -/
def Phi_w₂_cube (c_a N_a c_b N_b : B) : B :=
  cube c_a * Phi N_a + cube c_b * Phi N_b

/-- Two-channel cubic weighted chiral rotor `J_w₂⁽³⁾ = c_a³ J(N_a) + c_b³ J(N_b)`. -/
def J_w₂_cube (c_a N_a c_b N_b : B) : B :=
  cube c_a * J N_a + cube c_b * J N_b

/-- `WJA₃` Weighted Rotor-Block Product: `J_w₂ * Φ_w₂ = Σ_w₂`. -/
theorem J_w₂_mul_Phi_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    J_w₂ c_a N_a c_b N_b * Phi_w₂ c_a N_a c_b N_b =
      Sigma_w₂ c_a N_a c_b N_b := by
  dsimp [J_w₂, Phi_w₂, Sigma_w₂]
  have h12 := weighted_cross_zero c_a (J N_a) c_b (Phi N_b)
    (J_mul_Phi_orthog N_a N_b h_ab h_ba h_asb h_sab) (comm_weight_Phi c_b N_b hc_b hcs_b)
  have h21 := weighted_cross_zero c_b (J N_b) c_a (Phi N_a)
    (J_mul_Phi_orthog N_b N_a h_ba h_ab (N_b_mul_star_N_a N_a N_b h_asb)
      (star_N_b_mul_N_a N_a N_b h_sab)) (comm_weight_Phi c_a N_a hc_a hcs_a)
  rw [mul_add_of_cross_orthog _ _ _ _ h12 h21,
      weight_mul_weight c_a (J N_a) (Phi N_a) (comm_weight_J c_a N_a hc_a hcs_a),
      weight_mul_weight c_b (J N_b) (Phi N_b) (comm_weight_J c_b N_b hc_b hcs_b),
      J_mul_Phi N_a h_nil_a, J_mul_Phi N_b h_nil_b]

/-- `WJA₃` Reversed Weighted Block-Rotor Product: `Φ_w₂ * J_w₂ = -Σ_w₂`. -/
theorem Phi_w₂_mul_J_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Phi_w₂ c_a N_a c_b N_b * J_w₂ c_a N_a c_b N_b =
      -Sigma_w₂ c_a N_a c_b N_b := by
  dsimp [J_w₂, Phi_w₂, Sigma_w₂]
  have h12 := weighted_cross_zero c_a (Phi N_a) c_b (J N_b)
    (Phi_mul_J_orthog N_a N_b h_ab h_ba h_asb h_sab) (comm_weight_J c_b N_b hc_b hcs_b)
  have h21 := weighted_cross_zero c_b (Phi N_b) c_a (J N_a)
    (Phi_mul_J_orthog N_b N_a h_ba h_ab (N_b_mul_star_N_a N_a N_b h_asb)
      (star_N_b_mul_N_a N_a N_b h_sab)) (comm_weight_J c_a N_a hc_a hcs_a)
  rw [mul_add_of_cross_orthog _ _ _ _ h12 h21,
      weight_mul_weight c_a (Phi N_a) (J N_a) (comm_weight_Phi c_a N_a hc_a hcs_a),
      weight_mul_weight c_b (Phi N_b) (J N_b) (comm_weight_Phi c_b N_b hc_b hcs_b),
      Phi_mul_J N_a h_nil_a, Phi_mul_J N_b h_nil_b,
      mul_neg, mul_neg,
      add_comm (-((c_a * c_a) * Sigma N_a)), ← neg_add_rev]

/-- **`WJA₃` Exact Anticommutation of `Φ_w₂` and `J_w₂` (`{Φ_w₂, J_w₂} = 0` and `{J_w₂, Φ_w₂} = 0`):** -/
theorem anticomm_Phi_w₂_J_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    anticomm (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) = 0 := by
  dsimp [anticomm]
  rw [Phi_w₂_mul_J_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      J_w₂_mul_Phi_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      add_comm (-Sigma_w₂ c_a N_a c_b N_b), ← sub_eq_add_neg, sub_self]

theorem anticomm_J_w₂_Phi_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    anticomm (J_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) = 0 := by
  dsimp [anticomm]
  rw [J_w₂_mul_Phi_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      Phi_w₂_mul_J_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      ← sub_eq_add_neg, sub_self]

/-- **`WJA₃` Commutator of `J_w₂` and `Φ_w₂` (`[J_w₂, Φ_w₂] = 2 Σ_w₂`):** -/
theorem comm_J_w₂_Phi_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    comm (J_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) =
      Sigma_w₂ c_a N_a c_b N_b + Sigma_w₂ c_a N_a c_b N_b := by
  dsimp [comm]
  rw [J_w₂_mul_Phi_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      Phi_w₂_mul_J_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      sub_eq_add_neg, neg_neg]

/-- `WJA₃` Weighted Block Square: `Φ_w₂² = Gap_w₂`. -/
theorem Phi_w₂_sq_eq_Gap_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Phi_w₂ c_a N_a c_b N_b * Phi_w₂ c_a N_a c_b N_b =
      Gap_w₂ c_a N_a c_b N_b := by
  dsimp [Phi_w₂, Gap_w₂]
  have h12 := weighted_cross_zero c_a (Phi N_a) c_b (Phi N_b)
    (Phi_mul_Phi_orthog N_a N_b h_ab h_ba h_asb h_sab) (comm_weight_Phi c_b N_b hc_b hcs_b)
  have h21 := weighted_cross_zero c_b (Phi N_b) c_a (Phi N_a)
    (Phi_mul_Phi_orthog N_b N_a h_ba h_ab (N_b_mul_star_N_a N_a N_b h_asb)
      (star_N_b_mul_N_a N_a N_b h_sab)) (comm_weight_Phi c_a N_a hc_a hcs_a)
  rw [mul_add_of_cross_orthog _ _ _ _ h12 h21,
      weight_mul_weight c_a (Phi N_a) (Phi N_a) (comm_weight_Phi c_a N_a hc_a hcs_a),
      weight_mul_weight c_b (Phi N_b) (Phi N_b) (comm_weight_Phi c_b N_b hc_b hcs_b),
      Phi_sq_eq_Gap N_a h_nil_a h_reg_a, Phi_sq_eq_Gap N_b h_nil_b h_reg_b]

/-- `WJA₃` Weighted Rotor Square: `J_w₂² = -Gap_w₂`. -/
theorem J_w₂_sq_eq_neg_Gap_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    J_w₂ c_a N_a c_b N_b * J_w₂ c_a N_a c_b N_b =
      -Gap_w₂ c_a N_a c_b N_b := by
  dsimp [J_w₂, Gap_w₂]
  have h12 := weighted_cross_zero c_a (J N_a) c_b (J N_b)
    (J_mul_J_orthog N_a N_b h_ab h_ba h_asb h_sab) (comm_weight_J c_b N_b hc_b hcs_b)
  have h21 := weighted_cross_zero c_b (J N_b) c_a (J N_a)
    (J_mul_J_orthog N_b N_a h_ba h_ab (N_b_mul_star_N_a N_a N_b h_asb)
      (star_N_b_mul_N_a N_a N_b h_sab)) (comm_weight_J c_a N_a hc_a hcs_a)
  rw [mul_add_of_cross_orthog _ _ _ _ h12 h21,
      weight_mul_weight c_a (J N_a) (J N_a) (comm_weight_J c_a N_a hc_a hcs_a),
      weight_mul_weight c_b (J N_b) (J N_b) (comm_weight_J c_b N_b hc_b hcs_b),
      J_sq_eq_neg_Gap N_a h_nil_a h_reg_a, J_sq_eq_neg_Gap N_b h_nil_b h_reg_b,
      mul_neg, mul_neg,
      add_comm (-((c_a * c_a) * Gap N_a)), ← neg_add_rev]

/-!
### 3. Grade-3 Cubic Action of `Gap_w₂` and `Σ_w₂` on `Φ_w₂` and `J_w₂` (`WJA₄`)
-/

theorem Gap_w₂_mul_J_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Gap_w₂ c_a N_a c_b N_b * J_w₂ c_a N_a c_b N_b =
      J_w₂_cube c_a N_a c_b N_b := by
  dsimp [Gap_w₂, J_w₂, J_w₂_cube]
  have h12 := weighted_cross_zero (c_a * c_a) (Gap N_a) c_b (J N_b)
    (Gap_mul_J_orthog N_a N_b h_nil_a h_ab h_ba h_asb h_sab) (comm_weight_J c_b N_b hc_b hcs_b)
  have h21 := weighted_cross_zero (c_b * c_b) (Gap N_b) c_a (J N_a)
    (Gap_mul_J_orthog N_b N_a h_nil_b h_ba h_ab (N_b_mul_star_N_a N_a N_b h_asb)
      (star_N_b_mul_N_a N_a N_b h_sab)) (comm_weight_J c_a N_a hc_a hcs_a)
  rw [mul_add_of_cross_orthog _ _ _ _ h12 h21,
      sq_weight_mul_right c_a (Gap N_a) (J N_a) (comm_weight_Gap c_a N_a hc_a hcs_a),
      sq_weight_mul_right c_b (Gap N_b) (J N_b) (comm_weight_Gap c_b N_b hc_b hcs_b),
      Gap_mul_J N_a h_nil_a h_reg_a, Gap_mul_J N_b h_nil_b h_reg_b]

theorem J_w₂_mul_Gap_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    J_w₂ c_a N_a c_b N_b * Gap_w₂ c_a N_a c_b N_b =
      J_w₂_cube c_a N_a c_b N_b := by
  dsimp [Gap_w₂, J_w₂, J_w₂_cube]
  have h12 := weighted_cross_zero c_a (J N_a) (c_b * c_b) (Gap N_b)
    (J_mul_Gap_orthog N_a N_b h_nil_b h_ab h_ba h_asb h_sab)
    (comm_sq_of_comm c_b (Gap N_b) (comm_weight_Gap c_b N_b hc_b hcs_b))
  have h21 := weighted_cross_zero c_b (J N_b) (c_a * c_a) (Gap N_a)
    (J_mul_Gap_orthog N_b N_a h_nil_a h_ba h_ab (N_b_mul_star_N_a N_a N_b h_asb)
      (star_N_b_mul_N_a N_a N_b h_sab))
    (comm_sq_of_comm c_a (Gap N_a) (comm_weight_Gap c_a N_a hc_a hcs_a))
  rw [mul_add_of_cross_orthog _ _ _ _ h12 h21,
      mul_sq_weight_right c_a (J N_a) (Gap N_a) (comm_weight_J c_a N_a hc_a hcs_a),
      mul_sq_weight_right c_b (J N_b) (Gap N_b) (comm_weight_J c_b N_b hc_b hcs_b),
      J_mul_Gap N_a h_nil_a h_reg_a, J_mul_Gap N_b h_nil_b h_reg_b]

theorem Gap_w₂_mul_Phi_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Gap_w₂ c_a N_a c_b N_b * Phi_w₂ c_a N_a c_b N_b =
      Phi_w₂_cube c_a N_a c_b N_b := by
  dsimp [Gap_w₂, Phi_w₂, Phi_w₂_cube]
  have h12 := weighted_cross_zero (c_a * c_a) (Gap N_a) c_b (Phi N_b)
    (Gap_mul_Phi_orthog N_a N_b h_nil_a h_ab h_ba h_asb h_sab) (comm_weight_Phi c_b N_b hc_b hcs_b)
  have h21 := weighted_cross_zero (c_b * c_b) (Gap N_b) c_a (Phi N_a)
    (Gap_mul_Phi_orthog N_b N_a h_nil_b h_ba h_ab (N_b_mul_star_N_a N_a N_b h_asb)
      (star_N_b_mul_N_a N_a N_b h_sab)) (comm_weight_Phi c_a N_a hc_a hcs_a)
  rw [mul_add_of_cross_orthog _ _ _ _ h12 h21,
      sq_weight_mul_right c_a (Gap N_a) (Phi N_a) (comm_weight_Gap c_a N_a hc_a hcs_a),
      sq_weight_mul_right c_b (Gap N_b) (Phi N_b) (comm_weight_Gap c_b N_b hc_b hcs_b),
      Gap_mul_Phi N_a h_nil_a h_reg_a, Gap_mul_Phi N_b h_nil_b h_reg_b]

theorem Phi_w₂_mul_Gap_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Phi_w₂ c_a N_a c_b N_b * Gap_w₂ c_a N_a c_b N_b =
      Phi_w₂_cube c_a N_a c_b N_b := by
  dsimp [Gap_w₂, Phi_w₂, Phi_w₂_cube]
  have h12 := weighted_cross_zero c_a (Phi N_a) (c_b * c_b) (Gap N_b)
    (Phi_mul_Gap_orthog N_a N_b h_nil_b h_ab h_ba h_asb h_sab)
    (comm_sq_of_comm c_b (Gap N_b) (comm_weight_Gap c_b N_b hc_b hcs_b))
  have h21 := weighted_cross_zero c_b (Phi N_b) (c_a * c_a) (Gap N_a)
    (Phi_mul_Gap_orthog N_b N_a h_nil_a h_ba h_ab (N_b_mul_star_N_a N_a N_b h_asb)
      (star_N_b_mul_N_a N_a N_b h_sab))
    (comm_sq_of_comm c_a (Gap N_a) (comm_weight_Gap c_a N_a hc_a hcs_a))
  rw [mul_add_of_cross_orthog _ _ _ _ h12 h21,
      mul_sq_weight_right c_a (Phi N_a) (Gap N_a) (comm_weight_Phi c_a N_a hc_a hcs_a),
      mul_sq_weight_right c_b (Phi N_b) (Gap N_b) (comm_weight_Phi c_b N_b hc_b hcs_b),
      Phi_mul_Gap N_a h_nil_a h_reg_a, Phi_mul_Gap N_b h_nil_b h_reg_b]

theorem Sigma_w₂_mul_Phi_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Sigma_w₂ c_a N_a c_b N_b * Phi_w₂ c_a N_a c_b N_b =
      J_w₂_cube c_a N_a c_b N_b := by
  rw [← J_w₂_mul_Phi_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      mul_assoc,
      Phi_w₂_sq_eq_Gap_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      J_w₂_mul_Gap_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]

theorem Phi_w₂_mul_Sigma_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Phi_w₂ c_a N_a c_b N_b * Sigma_w₂ c_a N_a c_b N_b =
      -J_w₂_cube c_a N_a c_b N_b := by
  have h_neg : Sigma_w₂ c_a N_a c_b N_b =
      -(Phi_w₂ c_a N_a c_b N_b * J_w₂ c_a N_a c_b N_b) := by
    rw [Phi_w₂_mul_J_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
        neg_neg]
  rw [h_neg, mul_neg, ← mul_assoc,
      Phi_w₂_sq_eq_Gap_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      Gap_w₂_mul_J_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]

/-!
### 4. Main Theorems: Weighted Multi-Channel `JordanAssoc` on `Φ_w₂` and `J_w₂` (`WJA₅–WJA₈`)
-/

/-- **`WJA₅` Main Theorem I (Weighted Multi-Channel Jordan Associator on `(Φ_w₂, Φ_w₂, J_w₂)`):**
    `JordanAssoc Φ_w₂ Φ_w₂ J_w₂ = 4 J_w₂⁽³⁾ = 4 (c_a³ J(N_a) + c_b³ J(N_b))`. -/
theorem JordanAssoc_Phi_w₂_Phi_w₂_J_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
      quad (J_w₂_cube c_a N_a c_b N_b) := by
  have h_self : anticomm (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) =
      Gap_w₂ c_a N_a c_b N_b + Gap_w₂ c_a N_a c_b N_b := by
    dsimp [anticomm]
    rw [Phi_w₂_sq_eq_Gap_w₂ c_a N_a c_b N_b
          h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]
  dsimp [JordanAssoc]
  rw [h_self,
      anticomm_Phi_w₂_J_w₂ c_a N_a c_b N_b
        h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      anticomm_zero_right, sub_zero]
  dsimp [anticomm, quad]
  rw [add_mul, mul_add,
      Gap_w₂_mul_J_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      J_w₂_mul_Gap_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]

/-- **`WJA₅` Reversed Weighted Multi-Channel Jordan Associator on `(J_w₂, Φ_w₂, Φ_w₂)`:**
    `JordanAssoc J_w₂ Φ_w₂ Φ_w₂ = -4 J_w₂⁽³⁾`. -/
theorem JordanAssoc_J_w₂_Phi_w₂_Phi_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    JordanAssoc (J_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) =
      -quad (J_w₂_cube c_a N_a c_b N_b) := by
  have h_self : anticomm (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) =
      Gap_w₂ c_a N_a c_b N_b + Gap_w₂ c_a N_a c_b N_b := by
    dsimp [anticomm]
    rw [Phi_w₂_sq_eq_Gap_w₂ c_a N_a c_b N_b
          h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]
  dsimp [JordanAssoc]
  rw [anticomm_J_w₂_Phi_w₂ c_a N_a c_b N_b
        h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      anticomm_zero_left, h_self, zero_sub]
  dsimp [anticomm, quad]
  rw [mul_add, add_mul,
      Gap_w₂_mul_J_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      J_w₂_mul_Gap_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]

/-- **`WJA₆` Main Theorem II (Dual Rotor Jordan Associator on `(J_w₂, J_w₂, Φ_w₂)`):**
    `JordanAssoc J_w₂ J_w₂ Φ_w₂ = -4 Φ_w₂⁽³⁾ = -4 (c_a³ Φ(N_a) + c_b³ Φ(N_b))`. -/
theorem JordanAssoc_J_w₂_J_w₂_Phi_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    JordanAssoc (J_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) =
      -quad (Phi_w₂_cube c_a N_a c_b N_b) := by
  have h_self : anticomm (J_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
      -Gap_w₂ c_a N_a c_b N_b + -Gap_w₂ c_a N_a c_b N_b := by
    dsimp [anticomm]
    rw [J_w₂_sq_eq_neg_Gap_w₂ c_a N_a c_b N_b
          h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]
  dsimp [JordanAssoc]
  rw [h_self,
      anticomm_J_w₂_Phi_w₂ c_a N_a c_b N_b
        h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      anticomm_zero_right, sub_zero]
  dsimp [anticomm]
  rw [add_mul, mul_add, neg_mul, mul_neg,
      Gap_w₂_mul_Phi_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      Phi_w₂_mul_Gap_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]
  exact quad_neg (Phi_w₂_cube c_a N_a c_b N_b)

/-- **`WJA₆` Reversed Dual Rotor Jordan Associator on `(Φ_w₂, J_w₂, J_w₂)`:**
    `JordanAssoc Φ_w₂ J_w₂ J_w₂ = +4 Φ_w₂⁽³⁾`. -/
theorem JordanAssoc_Phi_w₂_J_w₂_J_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
      quad (Phi_w₂_cube c_a N_a c_b N_b) := by
  have h_self : anticomm (J_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
      -Gap_w₂ c_a N_a c_b N_b + -Gap_w₂ c_a N_a c_b N_b := by
    dsimp [anticomm]
    rw [J_w₂_sq_eq_neg_Gap_w₂ c_a N_a c_b N_b
          h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]
  dsimp [JordanAssoc]
  rw [anticomm_Phi_w₂_J_w₂ c_a N_a c_b N_b
        h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      anticomm_zero_left, h_self, zero_sub]
  dsimp [anticomm]
  rw [mul_add, add_mul, mul_neg, neg_mul,
      Gap_w₂_mul_Phi_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      Phi_w₂_mul_Gap_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]
  calc -((-Phi_w₂_cube c_a N_a c_b N_b + -Phi_w₂_cube c_a N_a c_b N_b) +
         (-Phi_w₂_cube c_a N_a c_b N_b + -Phi_w₂_cube c_a N_a c_b N_b))
    _ = -quad (-Phi_w₂_cube c_a N_a c_b N_b) := rfl
    _ = -(-quad (Phi_w₂_cube c_a N_a c_b N_b)) := by rw [quad_neg]
    _ = quad (Phi_w₂_cube c_a N_a c_b N_b) := by rw [neg_neg]

/-- **`WJA₇` Multi-Channel Additivity of the Weighted Jordan Associator:**
    The Jordan associator of the weighted multi-channel blocks decomposes additively
    into the sum of the individual weighted channel Jordan associators. -/
theorem JordanAssoc_weighted_channel_additivity (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
      JordanAssoc (c_a * Phi N_a) (c_a * Phi N_a) (c_a * J N_a) +
      JordanAssoc (c_b * Phi N_b) (c_b * Phi N_b) (c_b * J N_b) := by
  rw [JordanAssoc_Phi_w₂_Phi_w₂_J_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      JordanAssoc_weighted_single_Phi_Phi_J c_a N_a h_nil_a h_reg_a hc_a hcs_a,
      JordanAssoc_weighted_single_Phi_Phi_J c_b N_b h_nil_b h_reg_b hc_b hcs_b]
  exact quad_add (cube c_a * J N_a) (cube c_b * J N_b)

/-- **`WJA₈` Weighted Curvature Double-Commutator Bridge:**
    `JordanAssoc Φ_w₂ Φ_w₂ J_w₂ = [[J_w₂, Φ_w₂], Φ_w₂] = [2 Σ_w₂, Φ_w₂]`. -/
theorem JordanAssoc_eq_comm_two_Sigma_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
      comm (comm (J_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b))
           (Phi_w₂ c_a N_a c_b N_b) := by
  rw [JordanAssoc_Phi_w₂_Phi_w₂_J_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      comm_J_w₂_Phi_w₂ c_a N_a c_b N_b
        h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b]
  dsimp [comm, quad]
  rw [add_mul, mul_add,
      Sigma_w₂_mul_Phi_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      Phi_w₂_mul_Sigma_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      ← neg_add_rev, sub_eq_add_neg, neg_neg]

/-!
### 5. Channel-Selective Projective Filtering & Cyclotomic Grade-3 Synchronization (`WJA₉–WJA₁₀`)
-/

/-- **`WJA₉` Channel-Selective Projective Filtering of the Grade-3 Anomaly:**
    `Gap(N_a) * JordanAssoc Φ_w₂ Φ_w₂ J_w₂ = JordanAssoc (c_a Φ N_a) (c_a Φ N_a) (c_a J N_a)`. -/
theorem Gap_left_filter_JordanAssoc (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Gap N_a *
      JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
      JordanAssoc (c_a * Phi N_a) (c_a * Phi N_a) (c_a * J N_a) := by
  have hGa_cube_a : Gap N_a * (cube c_a * J N_a) = cube c_a * J N_a := by
    have hc_cube_G : Gap N_a * cube c_a = cube c_a * Gap N_a := by
      have hcG := (comm_weight_Gap c_a N_a hc_a hcs_a).symm
      have hc2G := (comm_sq_of_comm c_a (Gap N_a) (comm_weight_Gap c_a N_a hc_a hcs_a)).symm
      dsimp [cube]
      calc Gap N_a * ((c_a * c_a) * c_a)
        _ = (Gap N_a * (c_a * c_a)) * c_a := by rw [← mul_assoc]
        _ = ((c_a * c_a) * Gap N_a) * c_a := by rw [hc2G]
        _ = (c_a * c_a) * (Gap N_a * c_a) := by rw [mul_assoc]
        _ = (c_a * c_a) * (c_a * Gap N_a) := by rw [hcG]
        _ = ((c_a * c_a) * c_a) * Gap N_a := by rw [← mul_assoc]
    calc Gap N_a * (cube c_a * J N_a)
      _ = (Gap N_a * cube c_a) * J N_a := by rw [← mul_assoc]
      _ = (cube c_a * Gap N_a) * J N_a := by rw [hc_cube_G]
      _ = cube c_a * (Gap N_a * J N_a) := by rw [mul_assoc]
      _ = cube c_a * J N_a := by rw [Gap_mul_J N_a h_nil_a h_reg_a]
  have hGa_cube_b : Gap N_a * (cube c_b * J N_b) = 0 := by
    have hc_cube_J : cube c_b * J N_b = J N_b * cube c_b := by
      have hcJ := comm_weight_J c_b N_b hc_b hcs_b
      have hc2J := comm_sq_of_comm c_b (J N_b) hcJ
      dsimp [cube]
      calc ((c_b * c_b) * c_b) * J N_b
        _ = (c_b * c_b) * (c_b * J N_b) := by rw [mul_assoc]
        _ = (c_b * c_b) * (J N_b * c_b) := by rw [hcJ]
        _ = ((c_b * c_b) * J N_b) * c_b := by rw [← mul_assoc]
        _ = (J N_b * (c_b * c_b)) * c_b := by rw [hc2J]
        _ = J N_b * ((c_b * c_b) * c_b) := by rw [mul_assoc]
    calc Gap N_a * (cube c_b * J N_b)
      _ = Gap N_a * (J N_b * cube c_b) := by rw [hc_cube_J]
      _ = (Gap N_a * J N_b) * cube c_b := by rw [← mul_assoc]
      _ = 0 * cube c_b := by rw [Gap_mul_J_orthog N_a N_b h_nil_a h_ab h_ba h_asb h_sab]
      _ = 0 := by rw [zero_mul]
  rw [JordanAssoc_Phi_w₂_Phi_w₂_J_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      JordanAssoc_weighted_single_Phi_Phi_J c_a N_a h_nil_a h_reg_a hc_a hcs_a,
      quad_mul_left]
  dsimp [J_w₂_cube]
  rw [mul_add, hGa_cube_a, hGa_cube_b, add_zero]

/-- **`WJA₁₀` Cyclotomic Grade-3 Galois Synchronization Theorem:**
    For a two-channel system weighted by conjugate cyclotomic roots `(u, 1 - u)`
    satisfying `Φ₆(u) = u² - u + 1 = 0`, both cubes equal `-1`, synchronizing
    the Grade-3 Jordan associator into the phase-free singlet `-4 (J(N_a) + J(N_b))`. -/
theorem cyclotomic_galois_JordanAssoc_synchronization (u N_a N_b : B)
    (h_cyc : Phi6 u = 0)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hu_a : u * N_a = N_a * u) (hus_a : u * star N_a = star N_a * u)
    (hu_b : u * N_b = N_b * u) (hus_b : u * star N_b = star N_b * u) :
    JordanAssoc (Phi_w₂ u N_a (1 - u) N_b)
                (Phi_w₂ u N_a (1 - u) N_b)
                (J_w₂ u N_a (1 - u) N_b) =
      -quad (J N_a + J N_b) := by
  have h1u_b : (1 - u) * N_b = N_b * (1 - u) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hu_b]
  have h1us_b : (1 - u) * star N_b = star N_b * (1 - u) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hus_b]
  have h_cyc_conj : Phi6 (1 - u) = 0 := by rw [Phi6_galois_conj, h_cyc]
  have hu3 := cube_eq_neg_one_of_Phi6 u h_cyc
  have h1u3 := cube_eq_neg_one_of_Phi6 (1 - u) h_cyc_conj
  rw [JordanAssoc_Phi_w₂_Phi_w₂_J_w₂ u N_a (1 - u) N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab
        hu_a hus_a h1u_b h1us_b]
  have h_cube_sync : J_w₂_cube u N_a (1 - u) N_b = -(J N_a + J N_b) := by
    dsimp [J_w₂_cube]
    rw [hu3, h1u3, neg_mul, one_mul, neg_mul, one_mul,
        ← neg_add_rev, add_comm (J N_b) (J N_a)]
  rw [h_cube_sync, quad_neg]

/-- **Master Synthesis (`WJA₁`–`WJA₁₀`)**:
Packages the Grade-3 Weighted Multi-Channel Jordan Associator Anomaly Poset. -/
theorem weighted_multi_channel_jordan_anomaly_poset_master_synthesis
    (c_a N_a c_b N_b u : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b)
    (h_cyc : Phi6 u = 0)
    (hu_a : u * N_a = N_a * u) (hus_a : u * star N_a = star N_a * u)
    (hu_b : u * N_b = N_b * u) (hus_b : u * star N_b = star N_b * u) :
    (WeightedMultiChannelJordanAnomalyStage.causalEdge
       .WJA1_SingleChannelJordanAssociatorBaseline .WJA2_WeightedSingleChannelCubicScaling ∧
     WeightedMultiChannelJordanAnomalyStage.causalEdge
       .WJA9_ChannelSelectiveProjectiveFiltering .WJA10_CyclotomicGrade3GaloisSynchronization) ∧
    (anticomm (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) = 0 ∧
     comm (J_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) =
       Sigma_w₂ c_a N_a c_b N_b + Sigma_w₂ c_a N_a c_b N_b ∧
     Phi_w₂ c_a N_a c_b N_b * Phi_w₂ c_a N_a c_b N_b = Gap_w₂ c_a N_a c_b N_b ∧
     J_w₂ c_a N_a c_b N_b * J_w₂ c_a N_a c_b N_b = -Gap_w₂ c_a N_a c_b N_b) ∧
    (JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
       quad (J_w₂_cube c_a N_a c_b N_b) ∧
     JordanAssoc (J_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) =
       -quad (J_w₂_cube c_a N_a c_b N_b) ∧
     JordanAssoc (J_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) =
       -quad (Phi_w₂_cube c_a N_a c_b N_b) ∧
     JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
       quad (Phi_w₂_cube c_a N_a c_b N_b)) ∧
    (JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
       JordanAssoc (c_a * Phi N_a) (c_a * Phi N_a) (c_a * J N_a) +
       JordanAssoc (c_b * Phi N_b) (c_b * Phi N_b) (c_b * J N_b) ∧
     JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
       comm (comm (J_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b))
            (Phi_w₂ c_a N_a c_b N_b) ∧
     Gap N_a *
       JordanAssoc (Phi_w₂ c_a N_a c_b N_b) (Phi_w₂ c_a N_a c_b N_b) (J_w₂ c_a N_a c_b N_b) =
       JordanAssoc (c_a * Phi N_a) (c_a * Phi N_a) (c_a * J N_a)) ∧
    JordanAssoc (Phi_w₂ u N_a (1 - u) N_b)
                (Phi_w₂ u N_a (1 - u) N_b)
                (J_w₂ u N_a (1 - u) N_b) =
      -quad (J N_a + J N_b) :=
  ⟨⟨WeightedMultiChannelJordanAnomalyStage.poset_chain_and_acyclicity.1.1,
    WeightedMultiChannelJordanAnomalyStage.poset_chain_and_acyclicity.1.2.2.2.2.2.2.2.2⟩,
   ⟨anticomm_Phi_w₂_J_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
    comm_J_w₂_Phi_w₂ c_a N_a c_b N_b h_nil_a h_nil_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
    Phi_w₂_sq_eq_Gap_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
    J_w₂_sq_eq_neg_Gap_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b⟩,
   ⟨JordanAssoc_Phi_w₂_Phi_w₂_J_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
    JordanAssoc_J_w₂_Phi_w₂_Phi_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
    JordanAssoc_J_w₂_J_w₂_Phi_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
    JordanAssoc_Phi_w₂_J_w₂_J_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b⟩,
   ⟨JordanAssoc_weighted_channel_additivity c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
    JordanAssoc_eq_comm_two_Sigma_w₂ c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
    Gap_left_filter_JordanAssoc c_a N_a c_b N_b h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b⟩,
   cyclotomic_galois_JordanAssoc_synchronization u N_a N_b h_cyc h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hu_a hus_a hu_b hus_b⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.WeightedMultiChannelJordanAnomalyPoset
