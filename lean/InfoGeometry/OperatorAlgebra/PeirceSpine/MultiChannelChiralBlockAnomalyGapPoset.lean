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
import Mathlib.Tactic.NoncommRing

/-!
# Multi-Channel & Weighted Chiral Block Anomaly-to-Gap Poset (`MC₁`–`MC₁₀` & `WMC₁`–`WMC₁₀`)

In the background-free anomaly-first dependency order over `[Ring B] [StarRing B]`—where the
non-commuting nilpotent pairing generates the parity anomaly `Σ(N) = [N, N*]`, whose square defines
the support/gap `Gap(N) := Σ(N)²`, which the chiral block operator `Φ(N) = N + N*` turns into a
spectral gap `Φ(N)² = Gap(N)`—multi-channel additivity and weighted channel secular filtering are
governed by four cross-channel orthogonality conditions on `(N_a, N_b)`:
`N_a * N_b = 0`, `N_b * N_a = 0`, `N_a * star N_b = 0`, `star N_a * N_b = 0`.

1. **Part I (`MultiChannelAnomalyGapPoset`, `MC₁ ≺ MC₂ ≺ ⋯ ≺ MC₁₀`)**:
   - `MC₁`–`MC₂`: Closure of nilpotency `(N_a + N_b)² = 0` and Von Neumann regularity
     `(N_a + N_b) (N_a + N_b)* (N_a + N_b) = N_a + N_b`,
   - `MC₃`–`MC₄`: Additivity `Σ(N_a + N_b) = Σ(N_a) + Σ(N_b)` and mutual annihilation
     `Σ(N_a) Σ(N_b) = 0`, `Σ(N_b) Σ(N_a) = 0`,
   - `MC₅`–`MC₆`: Additivity `Gap(N_a + N_b) = Gap(N_a) + Gap(N_b)`, orthogonality
     `Gap(N_a) Gap(N_b) = 0`, and composite idempotency `Gap(N_a + N_b)² = Gap(N_a + N_b)`,
   - `MC₇`–`MC₈`: Channel-selective filtering `Gap(N_a) Φ(N_a + N_b) = Φ(N_a)`,
     `Φ(N_a + N_b)² = Gap(N_a) + Gap(N_b)`, and `Φ_tot (Φ_tot² - 1) = 0`,
   - `MC₉`–`MC₁₀`: Inductive 3-channel supercolor closure `Σ(N₁ + N₂ + N₃) = Σ₁ + Σ₂ + Σ₃` and
     `Gap(N₁ + N₂ + N₃) = Gap₁ + Gap₂ + Gap₃`.
2. **Part II (`WeightedMultiChannelGapPoset`, `WMC₁`–`WMC₁₀`)**:
   - Intra-channel weight commutation (`c_a N_a = N_a c_a`, `c_a N_a* = N_a* c_a`) suffices to
     annihilate all cross-channel terms `(c_a Φ(N_a)) (c_b Φ(N_b)) = 0`,
   - `J_w₂ * Φ_w₂ = c_a² Σ(N_a) + c_b² Σ(N_b) = Σ_w₂` and
     `Φ_w₂ * Φ_w₂ = c_a² Gap(N_a) + c_b² Gap(N_b) = Gap_w₂`,
   - `weighted_Phi_sum_sq_eq_weighted_Gap` extends the weighted square identity to any
     finite index set, assuming pairwise primitive orthogonality and channel-local weight commutation,
   - Channel-selective filtering `Gap(N_a) Φ_w₂ = c_a Φ(N_a)`, eigenvalue action
     `Gap_w₂ (c_a Φ(N_a)) = c_a² (c_a Φ(N_a))`, and secular equation
     `(Φ_w₂² - c_a²) (c_a Φ(N_a)) = 0`,
   - Three-channel weighted block square `Φ_w₃² = Gap_w₃` and cyclotomic `Φ₆(u) = u² - u + 1 = 0`
     linear reduction `(u Φ(N))² = (u - 1) Gap(N)`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset

open scoped Matrix

/-!
## 0. The 10-Stage Acyclic Causal Poset (`MC₁ ≺ MC₂ ≺ ⋯ ≺ MC₁₀`)
-/

/-- The 10 causal stages of the Multi-Channel Chiral Block Anomaly-to-Gap Poset. -/
inductive MultiChannelAnomalyGapStage : Type
  | MC1_SingleChannelAnomalyFoundation
  | MC2_MultiChannelNilpotencyAndRegularityClosure
  | MC3_ParityAnomalyAdditivity
  | MC4_MutualAnomalyAnnihilation
  | MC5_SpectralGapAdditivityAndOrthogonality
  | MC6_CompositeGapIdempotency
  | MC7_ChannelSelectiveAnomalyAndGapFiltering
  | MC8_MultiChannelChiralBlockSpectralGapEq
  | MC9_ThreeChannelSupercolorAnomalyAdditivity
  | MC10_ThreeChannelSupercolorGapAdditivity
  deriving DecidableEq, Repr

namespace MultiChannelAnomalyGapStage

/-- Monotone integer rank `0..9` witnessing strict causal acyclicity. -/
def rank : MultiChannelAnomalyGapStage → ℕ
  | .MC1_SingleChannelAnomalyFoundation => 0
  | .MC2_MultiChannelNilpotencyAndRegularityClosure => 1
  | .MC3_ParityAnomalyAdditivity => 2
  | .MC4_MutualAnomalyAnnihilation => 3
  | .MC5_SpectralGapAdditivityAndOrthogonality => 4
  | .MC6_CompositeGapIdempotency => 5
  | .MC7_ChannelSelectiveAnomalyAndGapFiltering => 6
  | .MC8_MultiChannelChiralBlockSpectralGapEq => 7
  | .MC9_ThreeChannelSupercolorAnomalyAdditivity => 8
  | .MC10_ThreeChannelSupercolorGapAdditivity => 9

/-- Strict causal precedence `s₁ ≺ s₂`. -/
@[reducible] def causalEdge (s₁ s₂ : MultiChannelAnomalyGapStage) : Prop :=
  rank s₁ < rank s₂

/-- Reflexive-transitive causal order `s₁ ≼ s₂`. -/
@[reducible] def causalLe (s₁ s₂ : MultiChannelAnomalyGapStage) : Prop :=
  rank s₁ ≤ rank s₂

instance instLT : LT MultiChannelAnomalyGapStage := ⟨causalEdge⟩
instance instLE : LE MultiChannelAnomalyGapStage := ⟨causalLe⟩

/-- Linear order on `MultiChannelAnomalyGapStage` induced by `rank`. -/
instance instLinearOrder : LinearOrder MultiChannelAnomalyGapStage :=
  LinearOrder.lift' rank (by
    intro a b h
    cases a <;> cases b <;> first | rfl | contradiction)

/-- The 10-stage multi-channel anomaly-to-gap poset forms a strictly increasing chain. -/
theorem poset_chain_and_acyclicity :
    (causalEdge .MC1_SingleChannelAnomalyFoundation .MC2_MultiChannelNilpotencyAndRegularityClosure ∧
     causalEdge .MC2_MultiChannelNilpotencyAndRegularityClosure .MC3_ParityAnomalyAdditivity ∧
     causalEdge .MC3_ParityAnomalyAdditivity .MC4_MutualAnomalyAnnihilation ∧
     causalEdge .MC4_MutualAnomalyAnnihilation .MC5_SpectralGapAdditivityAndOrthogonality ∧
     causalEdge .MC5_SpectralGapAdditivityAndOrthogonality .MC6_CompositeGapIdempotency ∧
     causalEdge .MC6_CompositeGapIdempotency .MC7_ChannelSelectiveAnomalyAndGapFiltering ∧
     causalEdge .MC7_ChannelSelectiveAnomalyAndGapFiltering .MC8_MultiChannelChiralBlockSpectralGapEq ∧
     causalEdge .MC8_MultiChannelChiralBlockSpectralGapEq .MC9_ThreeChannelSupercolorAnomalyAdditivity ∧
     causalEdge .MC9_ThreeChannelSupercolorAnomalyAdditivity .MC10_ThreeChannelSupercolorGapAdditivity) ∧
    (∀ s : MultiChannelAnomalyGapStage, ¬ causalEdge s s) := by
  refine ⟨by decide, ?_⟩
  intro s
  exact Nat.lt_irrefl (rank s)

end MultiChannelAnomalyGapStage

/-!
### 0.b Universal Additive Rearrangement Helpers
-/

section RingHelpers

variable {B : Type*} [Ring B]

theorem neg_sub_eq_neg_add (a b : B) : -a - b = -(a + b) := by
  abel

theorem add_add_add_comm' (a b c d : B) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  abel

theorem sub_add_sub_comm' (a b c d : B) :
    (a - b) + (c - d) = (a + c) - (b + d) := by
  abel

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

end RingHelpers

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 1. Single-Channel Anomaly-First Foundation (`MC₁`)
-/

/-- Foundational parity anomaly of a nilpotent channel `Σ(N) = [N, N*]`. -/
def Sigma (N : B) : B := comm N (star N)

/-- Self-adjoint chiral block pairing operator `Φ(N) = N + N*`. -/
def Phi (N : B) : B := N + star N

/-- Skew-adjoint chiral block rotor `J(N) = N - N*`. -/
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

theorem Sigma_mul_star_N (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * star N = -star N := by
  dsimp [Sigma, comm]
  rw [sub_mul, mul_assoc N (star N) (star N),
      star_N_sq N h_nil, mul_zero,
      star_N_reg N h_reg, zero_sub]

theorem Sigma_mul_Phi (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * Phi N = J N := by
  dsimp [Phi, J]
  rw [mul_add, Sigma_mul_N N h_nil h_reg, Sigma_mul_star_N N h_nil h_reg,
      ← sub_eq_add_neg]

theorem Sigma_mul_J (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * J N = Phi N := by
  dsimp [Phi, J]
  rw [mul_sub, Sigma_mul_N N h_nil h_reg, Sigma_mul_star_N N h_nil h_reg,
      sub_eq_add_neg, neg_neg]

theorem N_mul_Sigma (N : B) (h_nil : N * N = 0)
    (h_reg : N * star N * N = N) : N * Sigma N = -N := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc N N (star N), h_nil, zero_mul,
    ← mul_assoc N (star N) N, h_reg, zero_sub]

theorem star_N_mul_Sigma (N : B) (h_nil : N * N = 0)
    (h_reg : N * star N * N = N) : star N * Sigma N = star N := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc (star N) N (star N), star_N_reg N h_reg,
    ← mul_assoc (star N) (star N) N, star_N_sq N h_nil, zero_mul, sub_zero]

theorem Phi_mul_Sigma (N : B) (h_nil : N * N = 0)
    (h_reg : N * star N * N = N) : Phi N * Sigma N = -J N := by
  dsimp [Phi, J]
  rw [add_mul, N_mul_Sigma N h_nil h_reg,
    star_N_mul_Sigma N h_nil h_reg, add_comm (-N) (star N),
    ← sub_eq_add_neg, neg_sub]

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

theorem Phi_sq_eq_Gap (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Phi N * Phi N = Gap N := by
  calc Phi N * Phi N
    _ = (Sigma N * J N) * Phi N := by rw [Sigma_mul_J N h_nil h_reg]
    _ = Sigma N * (J N * Phi N) := by rw [mul_assoc]
    _ = Sigma N * Sigma N := by rw [J_mul_Phi N h_nil]
    _ = Gap N := rfl

/-- The skew chiral rotor squares to the negative channel gap. -/
theorem J_sq_eq_neg_Gap (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    J N * J N = -Gap N := by
  have hs_nil : star N * star N = 0 := star_N_sq N h_nil
  have hJ : J N * J N = -(Phi N * Phi N) := by
    dsimp [J, Phi]
    noncomm_ring [h_nil, hs_nil]
  rw [hJ, Phi_sq_eq_Gap N h_nil h_reg]

theorem Gap_mul_Phi (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * Phi N = Phi N := by
  calc Gap N * Phi N
    _ = Sigma N * (Sigma N * Phi N) := by dsimp [Gap]; rw [mul_assoc]
    _ = Sigma N * J N := by rw [Sigma_mul_Phi N h_nil h_reg]
    _ = Phi N := Sigma_mul_J N h_nil h_reg

theorem Gap_mul_N (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * N = N := by
  dsimp [Gap]
  rw [mul_assoc, Sigma_mul_N N h_nil h_reg, Sigma_mul_N N h_nil h_reg]

theorem Gap_mul_star_N (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * star N = star N := by
  dsimp [Gap]
  rw [mul_assoc, Sigma_mul_star_N N h_nil h_reg, mul_neg,
      Sigma_mul_star_N N h_nil h_reg, neg_neg]

theorem Gap_mul_Sigma (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * Sigma N = Sigma N := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc (Gap N) N (star N), Gap_mul_N N h_nil h_reg,
      ← mul_assoc (Gap N) (star N) N, Gap_mul_star_N N h_nil h_reg]

theorem Gap_idem (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * Gap N = Gap N := by
  calc Gap N * Gap N
    _ = Gap N * (Sigma N * Sigma N) := rfl
    _ = (Gap N * Sigma N) * Sigma N := by rw [← mul_assoc]
    _ = Sigma N * Sigma N := by rw [Gap_mul_Sigma N h_nil h_reg]
    _ = Gap N := rfl

/-!
### 2. Multi-Channel Cross-Orthogonality & Closure of Nilpotency/Regularity (`MC₂`)
-/

/-- Derived adjoint orthogonality: `N_b * N_a = 0 ⟹ N_a* * N_b* = 0`. -/
theorem star_N_a_mul_star_N_b (N_a N_b : B) (h_ba : N_b * N_a = 0) :
    star N_a * star N_b = 0 := by
  rw [← star_mul, h_ba, star_zero]

/-- Derived adjoint orthogonality: `N_a * N_b = 0 ⟹ N_b* * N_a* = 0`. -/
theorem star_N_b_mul_star_N_a (N_a N_b : B) (h_ab : N_a * N_b = 0) :
    star N_b * star N_a = 0 := by
  rw [← star_mul, h_ab, star_zero]

/-- Derived adjoint orthogonality: `N_a * N_b* = 0 ⟹ N_b * N_a* = 0`. -/
theorem N_b_mul_star_N_a (N_a N_b : B) (h_asb : N_a * star N_b = 0) :
    N_b * star N_a = 0 := by
  have h := congrArg star h_asb
  rw [star_mul, star_star, star_zero] at h
  exact h

/-- Derived adjoint orthogonality: `N_a* * N_b = 0 ⟹ N_b* * N_a = 0`. -/
theorem star_N_b_mul_N_a (N_a N_b : B) (h_sab : star N_a * N_b = 0) :
    star N_b * N_a = 0 := by
  have h := congrArg star h_sab
  rw [star_mul, star_star, star_zero] at h
  exact h

omit [StarRing B] in
/-- **`MC₂` Multi-Channel Nilpotency Closure (`(N_a + N_b)² = 0`):** -/
theorem N_tot_sq_eq_zero (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0) :
    (N_a + N_b) * (N_a + N_b) = 0 := by
  calc (N_a + N_b) * (N_a + N_b)
    _ = (N_a + N_b) * N_a + (N_a + N_b) * N_b := by rw [mul_add]
    _ = (N_a * N_a + N_b * N_a) + (N_a * N_b + N_b * N_b) := by
        rw [add_mul, add_mul]
    _ = (0 + 0) + (0 + 0) := by rw [h_nil_a, h_ba, h_ab, h_nil_b]
    _ = 0 := by rw [add_zero, add_zero]

theorem mul_star_add_orthog (N_a N_b : B)
    (h_asb : N_a * star N_b = 0) :
    (N_a + N_b) * star (N_a + N_b) =
      N_a * star N_a + N_b * star N_b := by
  have h_bsa := N_b_mul_star_N_a N_a N_b h_asb
  calc (N_a + N_b) * star (N_a + N_b)
    _ = (N_a + N_b) * (star N_a + star N_b) := by rw [star_add]
    _ = (N_a + N_b) * star N_a + (N_a + N_b) * star N_b := by rw [mul_add]
    _ = (N_a * star N_a + N_b * star N_a) +
        (N_a * star N_b + N_b * star N_b) := by rw [add_mul, add_mul]
    _ = (N_a * star N_a + 0) + (0 + N_b * star N_b) := by rw [h_bsa, h_asb]
    _ = N_a * star N_a + N_b * star N_b := by rw [add_zero, zero_add]

theorem star_mul_add_orthog (N_a N_b : B)
    (h_sab : star N_a * N_b = 0) :
    star (N_a + N_b) * (N_a + N_b) =
      star N_a * N_a + star N_b * N_b := by
  have h_sba := star_N_b_mul_N_a N_a N_b h_sab
  calc star (N_a + N_b) * (N_a + N_b)
    _ = (star N_a + star N_b) * (N_a + N_b) := by rw [star_add]
    _ = (star N_a + star N_b) * N_a + (star N_a + star N_b) * N_b := by
        rw [mul_add]
    _ = (star N_a * N_a + star N_b * N_a) +
        (star N_a * N_b + star N_b * N_b) := by rw [add_mul, add_mul]
    _ = (star N_a * N_a + 0) + (0 + star N_b * N_b) := by rw [h_sba, h_sab]
    _ = star N_a * N_a + star N_b * N_b := by rw [add_zero, zero_add]

/-- **`MC₂` Multi-Channel Von Neumann Regularity Closure:**
    `(N_a + N_b) * (N_a + N_b)* * (N_a + N_b) = N_a + N_b`. -/
theorem N_tot_reg (N_a N_b : B)
    (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_asb : N_a * star N_b = 0)
    (h_sab : star N_a * N_b = 0) :
    (N_a + N_b) * star (N_a + N_b) * (N_a + N_b) = N_a + N_b := by
  have h_sba := star_N_b_mul_N_a N_a N_b h_sab
  have h_ab_zero : (N_a * star N_a) * N_b = 0 := by
    rw [mul_assoc, h_sab, mul_zero]
  have h_ba_zero : (N_b * star N_b) * N_a = 0 := by
    rw [mul_assoc, h_sba, mul_zero]
  rw [mul_star_add_orthog N_a N_b h_asb]
  calc (N_a * star N_a + N_b * star N_b) * (N_a + N_b)
    _ = (N_a * star N_a + N_b * star N_b) * N_a +
        (N_a * star N_a + N_b * star N_b) * N_b := by rw [mul_add]
    _ = (N_a * star N_a * N_a + N_b * star N_b * N_a) +
        (N_a * star N_a * N_b + N_b * star N_b * N_b) := by
        rw [add_mul, add_mul]
    _ = (N_a + 0) + (0 + N_b) := by
        rw [h_reg_a, h_ba_zero, h_ab_zero, h_reg_b]
    _ = N_a + N_b := by rw [add_zero, zero_add]

/-!
### 3. Additivity & Mutual Annihilation of the Parity Anomaly (`MC₃–MC₄`)
-/

/-- **`MC₃` Additivity of the Parity Anomaly (`Σ(N_a + N_b) = Σ(N_a) + Σ(N_b)`):** -/
theorem Sigma_add (N_a N_b : B)
    (h_asb : N_a * star N_b = 0)
    (h_sab : star N_a * N_b = 0) :
    Sigma (N_a + N_b) = Sigma N_a + Sigma N_b := by
  dsimp [Sigma, comm]
  rw [mul_star_add_orthog N_a N_b h_asb,
      star_mul_add_orthog N_a N_b h_sab,
      ← sub_add_sub_comm']

theorem Sigma_mul_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_sab : star N_a * N_b = 0) :
    Sigma N_a * N_b = 0 := by
  dsimp [Sigma, comm]
  rw [sub_mul, mul_assoc N_a (star N_a) N_b, h_sab, mul_zero,
      mul_assoc (star N_a) N_a N_b, h_ab, mul_zero, sub_self]

theorem Sigma_mul_star_orthog (N_a N_b : B)
    (h_ba : N_b * N_a = 0) (h_asb : N_a * star N_b = 0) :
    Sigma N_a * star N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  dsimp [Sigma, comm]
  rw [sub_mul, mul_assoc N_a (star N_a) (star N_b), h_sasb, mul_zero,
              mul_assoc (star N_a) N_a (star N_b), h_asb, mul_zero, sub_self]

/-- **`MC₄` Mutual Annihilation of Channel Anomalies (`Σ(N_a) * Σ(N_b) = 0`):** -/
theorem Sigma_mul_Sigma_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Sigma N_a * Sigma N_b = 0 := by
  dsimp [Sigma, comm]
  calc Sigma N_a * (N_b * star N_b - star N_b * N_b)
    _ = Sigma N_a * (N_b * star N_b) - Sigma N_a * (star N_b * N_b) := by
        rw [mul_sub]
    _ = (Sigma N_a * N_b) * star N_b - (Sigma N_a * star N_b) * N_b := by
        rw [← mul_assoc, ← mul_assoc]
    _ = 0 * star N_b - 0 * N_b := by
        rw [Sigma_mul_orthog N_a N_b h_ab h_sab,
            Sigma_mul_star_orthog N_a N_b h_ba h_asb]
    _ = 0 := by rw [zero_mul, zero_mul, sub_self]

theorem Sigma_mul_Sigma_orthog_symm (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Sigma N_b * Sigma N_a = 0 :=
  Sigma_mul_Sigma_orthog N_b N_a h_ba h_ab
    (N_b_mul_star_N_a N_a N_b h_asb)
    (star_N_b_mul_N_a N_a N_b h_sab)

/-- Distinct channel anomalies both commute and anticommute: `[Σ_a, Σ_b] = 0` and `{Σ_a, Σ_b} = 0`. -/
theorem comm_Sigma_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    comm (Sigma N_a) (Sigma N_b) = 0 := by
  dsimp [comm]
  rw [Sigma_mul_Sigma_orthog N_a N_b h_ab h_ba h_asb h_sab,
      Sigma_mul_Sigma_orthog_symm N_a N_b h_ab h_ba h_asb h_sab,
      sub_self]

theorem anticomm_Sigma_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    anticomm (Sigma N_a) (Sigma N_b) = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_Sigma_orthog N_a N_b h_ab h_ba h_asb h_sab,
      Sigma_mul_Sigma_orthog_symm N_a N_b h_ab h_ba h_asb h_sab,
      add_zero]

/-!
### 4. Additive Spectral Gap `Gap_tot = Gap_a + Gap_b` (`MC₅–MC₆`)
-/

/-- **`MC₅` Additivity of the Spectral Gap (`Gap(N_a + N_b) = Gap(N_a) + Gap(N_b)`):**
    Proved directly from `Gap = Σ²` and the mutual annihilation of `Σ(N_a)` and `Σ(N_b)`. -/
theorem Gap_add (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Gap (N_a + N_b) = Gap N_a + Gap N_b := by
  dsimp [Gap]
  rw [Sigma_add N_a N_b h_asb h_sab]
  calc (Sigma N_a + Sigma N_b) * (Sigma N_a + Sigma N_b)
    _ = (Sigma N_a + Sigma N_b) * Sigma N_a +
        (Sigma N_a + Sigma N_b) * Sigma N_b := by rw [mul_add]
    _ = (Sigma N_a * Sigma N_a + Sigma N_b * Sigma N_a) +
        (Sigma N_a * Sigma N_b + Sigma N_b * Sigma N_b) := by
        rw [add_mul, add_mul]
    _ = (Sigma N_a * Sigma N_a + 0) + (0 + Sigma N_b * Sigma N_b) := by
        rw [Sigma_mul_Sigma_orthog_symm N_a N_b h_ab h_ba h_asb h_sab,
            Sigma_mul_Sigma_orthog N_a N_b h_ab h_ba h_asb h_sab]
    _ = Sigma N_a * Sigma N_a + Sigma N_b * Sigma N_b := by
        rw [add_zero, zero_add]

/-- **`MC₅` Mutual Orthogonality of Channel Gaps (`Gap(N_a) * Gap(N_b) = 0`):** -/
theorem Gap_mul_Gap_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Gap N_a * Gap N_b = 0 := by
  dsimp [Gap]
  calc (Sigma N_a * Sigma N_a) * (Sigma N_b * Sigma N_b)
    _ = Sigma N_a * (Sigma N_a * (Sigma N_b * Sigma N_b)) := by
        rw [mul_assoc (Sigma N_a) (Sigma N_a) (Sigma N_b * Sigma N_b)]
    _ = Sigma N_a * ((Sigma N_a * Sigma N_b) * Sigma N_b) := by
        rw [← mul_assoc (Sigma N_a) (Sigma N_b) (Sigma N_b)]
    _ = Sigma N_a * (0 * Sigma N_b) := by
        rw [Sigma_mul_Sigma_orthog N_a N_b h_ab h_ba h_asb h_sab]
    _ = 0 := by rw [zero_mul, mul_zero]

/-- **`MC₆` Idempotency of the Additive Multi-Channel Gap:**
    `Gap(N_a + N_b) * Gap(N_a + N_b) = Gap(N_a + N_b)`. -/
theorem Gap_tot_idem (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Gap (N_a + N_b) * Gap (N_a + N_b) = Gap (N_a + N_b) :=
  Gap_idem (N_a + N_b)
    (N_tot_sq_eq_zero N_a N_b h_nil_a h_nil_b h_ab h_ba)
    (N_tot_reg N_a N_b h_reg_a h_reg_b h_asb h_sab)

/-!
### 5. Multi-Channel Chiral Block Decomposition & Spectral Gap Equation (`MC₇–MC₈`)
-/

/-- Additivity of the self-adjoint chiral block operator: `Φ(N_a + N_b) = Φ(N_a) + Φ(N_b)`. -/
theorem Phi_add (N_a N_b : B) :
    Phi (N_a + N_b) = Phi N_a + Phi N_b := by
  dsimp [Phi]
  rw [star_add, add_add_add_comm']

/-- Additivity of the skew-adjoint chiral block rotor: `J(N_a + N_b) = J(N_a) + J(N_b)`. -/
theorem J_add (N_a N_b : B) :
    J (N_a + N_b) = J N_a + J N_b := by
  dsimp [J]
  rw [star_add, sub_add_sub_comm']

theorem Sigma_mul_Phi_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Sigma N_a * Phi N_b = 0 := by
  dsimp [Phi]
  rw [mul_add,
      Sigma_mul_orthog N_a N_b h_ab h_sab,
      Sigma_mul_star_orthog N_a N_b h_ba h_asb,
      add_zero]

theorem Gap_mul_Phi_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Gap N_a * Phi N_b = 0 := by
  dsimp [Gap]
  rw [mul_assoc, Sigma_mul_Phi_orthog N_a N_b h_ab h_ba h_asb h_sab, mul_zero]

/-- **`MC₇` Channel-Selective Action of the Total Anomaly:**
    `Σ(N_a + N_b) * Φ(N_a) = J(N_a)`. -/
theorem Sigma_tot_mul_Phi_left (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Sigma (N_a + N_b) * Phi N_a = J N_a := by
  have h_Sigma_b_Phi_a : Sigma N_b * Phi N_a = 0 :=
    Sigma_mul_Phi_orthog N_b N_a h_ba h_ab
      (N_b_mul_star_N_a N_a N_b h_asb)
      (star_N_b_mul_N_a N_a N_b h_sab)
  rw [Sigma_add N_a N_b h_asb h_sab,
      add_mul,
      Sigma_mul_Phi N_a h_nil_a h_reg_a,
      h_Sigma_b_Phi_a,
      add_zero]

/-- **`MC₇` Channel-Resolved Gap Projection:**
    `Gap(N_a) * Φ(N_a + N_b) = Φ(N_a)`. -/
theorem Gap_left_proj_Phi_tot (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Gap N_a * Phi (N_a + N_b) = Phi N_a := by
  rw [Phi_add, mul_add,
      Gap_mul_Phi N_a h_nil_a h_reg_a,
      Gap_mul_Phi_orthog N_a N_b h_ab h_ba h_asb h_sab,
      add_zero]

/-- **`MC₈` The Multi-Channel Chiral Block Square Equals the Sum of Channel Gaps:**
    `Φ(N_a + N_b)² = Gap(N_a) + Gap(N_b)`. -/
theorem Phi_tot_sq_eq_Gap_sum (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Phi (N_a + N_b) * Phi (N_a + N_b) = Gap N_a + Gap N_b := by
  rw [Phi_sq_eq_Gap (N_a + N_b)
        (N_tot_sq_eq_zero N_a N_b h_nil_a h_nil_b h_ab h_ba)
        (N_tot_reg N_a N_b h_reg_a h_reg_b h_asb h_sab),
      Gap_add N_a N_b h_ab h_ba h_asb h_sab]

/-- **`MC₈` Multi-Channel Chiral Block Spectral Gap Equation:**
    `Φ(N_a + N_b) * (Φ(N_a + N_b)² - 1) = 0`. -/
theorem multi_channel_spectral_gap_eq (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Phi (N_a + N_b) * (Phi (N_a + N_b) * Phi (N_a + N_b) - 1) = 0 := by
  have h_nil_tot := N_tot_sq_eq_zero N_a N_b h_nil_a h_nil_b h_ab h_ba
  have h_reg_tot := N_tot_reg N_a N_b h_reg_a h_reg_b h_asb h_sab
  rw [mul_sub, mul_one, ← mul_assoc,
      Phi_sq_eq_Gap (N_a + N_b) h_nil_tot h_reg_tot,
      Gap_mul_Phi (N_a + N_b) h_nil_tot h_reg_tot,
      sub_self]

/-!
### 6. Inductive 3-Channel Supercolor Generalization (`MC₉–MC₁₀`)
-/

/-- **`MC₉` Three-Channel Parity Anomaly Additivity (`Σ(N₁ + N₂ + N₃) = Σ₁ + Σ₂ + Σ₃`):** -/
theorem Sigma_three_channel (N₁ N₂ N₃ : B)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0) :
    Sigma (N₁ + N₂ + N₃) = Sigma N₁ + Sigma N₂ + Sigma N₃ := by
  have h12_3_asb : (N₁ + N₂) * star N₃ = 0 := by
    rw [add_mul, h13_asb, h23_asb, add_zero]
  have h12_3_sab : star (N₁ + N₂) * N₃ = 0 := by
    rw [star_add, add_mul, h13_sab, h23_sab, add_zero]
  rw [Sigma_add (N₁ + N₂) N₃ h12_3_asb h12_3_sab,
      Sigma_add N₁ N₂ h12_asb h12_sab]

/-- **`MC₁₀` Three-Channel Spectral Gap Additivity (`Gap(N₁ + N₂ + N₃) = Gap₁ + Gap₂ + Gap₃`):** -/
theorem Gap_three_channel (N₁ N₂ N₃ : B)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0) :
    Gap (N₁ + N₂ + N₃) = Gap N₁ + Gap N₂ + Gap N₃ := by
  have h12_3_ab : (N₁ + N₂) * N₃ = 0 := by
    rw [add_mul, h13_ab, h23_ab, add_zero]
  have h12_3_ba : N₃ * (N₁ + N₂) = 0 := by
    rw [mul_add, h13_ba, h23_ba, add_zero]
  have h12_3_asb : (N₁ + N₂) * star N₃ = 0 := by
    rw [add_mul, h13_asb, h23_asb, add_zero]
  have h12_3_sab : star (N₁ + N₂) * N₃ = 0 := by
    rw [star_add, add_mul, h13_sab, h23_sab, add_zero]
  rw [Gap_add (N₁ + N₂) N₃ h12_3_ab h12_3_ba h12_3_asb h12_3_sab,
      Gap_add N₁ N₂ h12_ab h12_ba h12_asb h12_sab]

/-!
### 7. Concrete `4 × 4` Two-Channel Non-Commutative Matrix Witness (`T16` / `T17`)
-/

/-- Concrete `4 × 4` Channel-`a` nilpotent generator `N_a = E₀₁`. -/
def mcMatrixNa : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Concrete `4 × 4` Channel-`a` dual nilpotent generator `N_a* = E₁₀`. -/
def mcMatrixNaStar : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Concrete `4 × 4` Channel-`b` nilpotent generator `N_b = E₂₃`. -/
def mcMatrixNb : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 0, 0]

/-- Concrete `4 × 4` integer matrix witness certifying non-commutativity (`T16`) and
non-vanishing two-channel anomaly and gap additivity (`T17`). -/
theorem mc_matrix_noncomm_and_additive_gap_witness :
    mcMatrixNa * mcMatrixNa = 0 ∧
    mcMatrixNb * mcMatrixNb = 0 ∧
    mcMatrixNa * mcMatrixNb = 0 ∧
    mcMatrixNb * mcMatrixNa = 0 ∧
    mcMatrixNa * mcMatrixNaStar ≠ mcMatrixNaStar * mcMatrixNa ∧
    Sigma (mcMatrixNa + mcMatrixNb) = Sigma mcMatrixNa + Sigma mcMatrixNb ∧
    Gap (mcMatrixNa + mcMatrixNb) = Gap mcMatrixNa + Gap mcMatrixNb ∧
    Gap (mcMatrixNa + mcMatrixNb) ≠ 0 := by
  decide

end InfoGeometry.OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset

/-!
## Part II: Weighted Multi-Channel Chiral Block Gap Poset (`WMC₁`–`WMC₁₀`)
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.WeightedMultiChannelGapPoset

section RingHelpers

variable {B : Type*} [Ring B]

/-- If two ring elements `A` and `B_term` mutually annihilate (`A * B_term = 0`, `B_term * A = 0`),
    then the square of their sum is the sum of their squares. -/
theorem sq_add_of_orthog (A B_term : B)
    (hAB : A * B_term = 0) (hBA : B_term * A = 0) :
    (A + B_term) * (A + B_term) = A * A + B_term * B_term := by
  calc (A + B_term) * (A + B_term)
    _ = (A + B_term) * A + (A + B_term) * B_term := by rw [mul_add]
    _ = (A * A + B_term * A) + (A * B_term + B_term * B_term) := by
        rw [add_mul, add_mul]
    _ = (A * A + 0) + (0 + B_term * B_term) := by rw [hBA, hAB]
    _ = A * A + B_term * B_term := by rw [add_zero, zero_add]

/-- If `A₁ * B₂ = 0` and `A₂ * B₁ = 0`, then `(A₁ + A₂) * (B₁ + B₂) = A₁ * B₁ + A₂ * B₂`. -/
theorem mul_add_of_cross_orthog (A₁ A₂ B₁ B₂ : B)
    (h12 : A₁ * B₂ = 0) (h21 : A₂ * B₁ = 0) :
    (A₁ + A₂) * (B₁ + B₂) = A₁ * B₁ + A₂ * B₂ := by
  calc (A₁ + A₂) * (B₁ + B₂)
    _ = (A₁ + A₂) * B₁ + (A₁ + A₂) * B₂ := by rw [mul_add]
    _ = (A₁ * B₁ + A₂ * B₁) + (A₁ * B₂ + A₂ * B₂) := by rw [add_mul, add_mul]
    _ = (A₁ * B₁ + 0) + (0 + A₂ * B₂) := by rw [h21, h12]
    _ = A₁ * B₁ + A₂ * B₂ := by rw [add_zero, zero_add]

/-- A finite sum of pairwise annihilating terms squares to the sum of the
individual squares. The multiplication order is retained throughout. -/
theorem sum_mul_self_of_pairwise_annihilating {ι : Type*}
    (s : Finset ι) (g : ι → B)
    (hzero : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g i * g j = 0) :
    (∑ i ∈ s, g i) * (∑ i ∈ s, g i) = ∑ i ∈ s, g i * g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g i * g j = 0 := by
        intro i hi j hj hij
        exact hzero i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hleft : g a * (∑ i ∈ s, g i) = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi =>
          hzero a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
            (ne_of_mem_of_not_mem hi ha).symm
      have hright : (∑ i ∈ s, g i) * g a = 0 := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_zero fun i hi =>
          hzero i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)
            (ne_of_mem_of_not_mem hi ha)
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        (g a + ∑ i ∈ s, g i) * (g a + ∑ i ∈ s, g i) =
            g a * g a +
              (g a * (∑ i ∈ s, g i) + (∑ i ∈ s, g i) * g a) +
                (∑ i ∈ s, g i) * (∑ i ∈ s, g i) := by
          rw [mul_add, add_mul, add_mul]
          abel
        _ = g a * g a + ∑ i ∈ s, g i * g i := by
          rw [hleft, hright]
          simp [ih hs]

/-- A finite product of two sums keeps only matching-index terms when all
off-diagonal products vanish in the given multiplication order. -/
theorem sum_mul_sum_of_pairwise_cross_annihilating {ι : Type*}
    (s : Finset ι) (f g : ι → B)
    (hzero : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * g j = 0) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) = ∑ i ∈ s, f i * g i := by
  classical
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single_of_mem i hi (by
    intro j hj hji
    exact hzero i hi j hj (Ne.symm hji))]

/-- A channel-local right weight can be moved past its own block, so an
annihilating unweighted cross product remains zero after weighting. -/
theorem weighted_cross_zero (w_a X_a w_b Y_b : B)
    (hXY : X_a * Y_b = 0) (hw_b : w_b * Y_b = Y_b * w_b) :
    (w_a * X_a) * (w_b * Y_b) = 0 := by
  calc (w_a * X_a) * (w_b * Y_b)
      = (w_a * X_a) * (Y_b * w_b) := by rw [hw_b]
    _ = w_a * ((X_a * Y_b) * w_b) := by noncomm_ring
    _ = w_a * (0 * w_b) := by rw [hXY]
    _ = 0 := by rw [zero_mul, mul_zero]

/-- Commutation is preserved under squaring the left factor. -/
theorem comm_square_of_comm (c x : B) (h : c * x = x * c) :
    (c * c) * x = x * (c * c) := by
  calc (c * c) * x = c * (c * x) := by rw [mul_assoc]
    _ = c * (x * c) := by rw [h]
    _ = (c * x) * c := by rw [← mul_assoc]
    _ = (x * c) * c := by rw [h]
    _ = x * (c * c) := by rw [mul_assoc]

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

end RingHelpers

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 1. Single-Channel Anomaly-First Operators & Weight Commutation (`WMC₁–WMC₂`)
-/

/-- Foundational parity anomaly `Σ(N) = [N, N*]`. -/
def Sigma (N : B) : B := N * star N - star N * N

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

theorem Sigma_mul_star_N (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * star N = -star N := by
  dsimp [Sigma, comm]
  rw [sub_mul, mul_assoc N (star N) (star N),
      star_N_sq N h_nil, mul_zero,
      star_N_reg N h_reg, zero_sub]

theorem Sigma_mul_Phi (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * Phi N = J N := by
  dsimp [Phi, J]
  rw [mul_add, Sigma_mul_N N h_nil h_reg, Sigma_mul_star_N N h_nil h_reg,
      ← sub_eq_add_neg]

theorem Sigma_mul_J (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Sigma N * J N = Phi N := by
  dsimp [Phi, J]
  rw [mul_sub, Sigma_mul_N N h_nil h_reg, Sigma_mul_star_N N h_nil h_reg,
      sub_eq_add_neg, neg_neg]

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

theorem Phi_sq_eq_Gap (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Phi N * Phi N = Gap N := by
  calc Phi N * Phi N
    _ = (Sigma N * J N) * Phi N := by rw [Sigma_mul_J N h_nil h_reg]
    _ = Sigma N * (J N * Phi N) := by rw [mul_assoc]
    _ = Sigma N * Sigma N := by rw [J_mul_Phi N h_nil]
    _ = Gap N := rfl

theorem Gap_mul_Phi (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * Phi N = Phi N := by
  calc Gap N * Phi N
    _ = Sigma N * (Sigma N * Phi N) := by dsimp [Gap]; rw [mul_assoc]
    _ = Sigma N * J N := by rw [Sigma_mul_Phi N h_nil h_reg]
    _ = Phi N := Sigma_mul_J N h_nil h_reg

theorem Gap_mul_N (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * N = N := by
  dsimp [Gap]
  rw [mul_assoc, Sigma_mul_N N h_nil h_reg, Sigma_mul_N N h_nil h_reg]

theorem Gap_mul_star_N (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * star N = star N := by
  dsimp [Gap]
  rw [mul_assoc, Sigma_mul_star_N N h_nil h_reg, mul_neg,
      Sigma_mul_star_N N h_nil h_reg, neg_neg]

theorem Gap_mul_Sigma (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * Sigma N = Sigma N := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc (Gap N) N (star N), Gap_mul_N N h_nil h_reg,
      ← mul_assoc (Gap N) (star N) N, Gap_mul_star_N N h_nil h_reg]

theorem Gap_idem (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Gap N * Gap N = Gap N := by
  calc Gap N * Gap N
    _ = Gap N * (Sigma N * Sigma N) := rfl
    _ = (Gap N * Sigma N) * Sigma N := by rw [← mul_assoc]
    _ = Sigma N * Sigma N := by rw [Gap_mul_Sigma N h_nil h_reg]
    _ = Gap N := rfl

/-- The skew chiral rotor squares to the negative channel gap. -/
theorem J_sq_eq_neg_Gap (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    J N * J N = -Gap N := by
  have hs_nil : star N * star N = 0 := star_N_sq N h_nil
  have hJ : J N * J N = -(Phi N * Phi N) := by
    dsimp [J, Phi]
    noncomm_ring [h_nil, hs_nil]
  rw [hJ, Phi_sq_eq_Gap N h_nil h_reg]

/-- `WMC₁` For a self-adjoint weight (`star c = c`), `c * N = N * c` automatically
    implies `c * star N = star N * c`. -/
theorem comm_star_of_self_adjoint (c N : B)
    (hc_star : star c = c) (hc : c * N = N * c) :
    c * star N = star N * c := by
  calc c * star N
    _ = star c * star N := by rw [hc_star]
    _ = star (N * c) := by rw [← star_mul]
    _ = star (c * N) := by rw [← hc]
    _ = star N * star c := by rw [star_mul]
    _ = star N * c := by rw [hc_star]

/-- `WMC₁` If `c` commutes with `N` and `star N`, then `c` commutes with `Φ(N)`. -/
theorem comm_weight_Phi (c N : B)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    c * Phi N = Phi N * c := by
  dsimp [Phi]
  rw [mul_add, add_mul, hc, hcs]

/-- `WMC₁` If `c` commutes with `N` and `star N`, then `c` commutes with `J(N)`. -/
theorem comm_weight_J (c N : B)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    c * J N = J N * c := by
  dsimp [J]
  rw [mul_sub, sub_mul, hc, hcs]

/-- `WMC₁` A channel-local weight commuting with both chiral generators
    also commutes with their parity anomaly `Σ(N) = [N, N*]`. -/
theorem comm_weight_Sigma (c N : B)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    c * Sigma N = Sigma N * c := by
  dsimp [Sigma, comm]
  rw [mul_sub, sub_mul]
  have h₁ : c * (N * star N) = (N * star N) * c := by
    calc c * (N * star N)
        = (c * N) * star N := by rw [mul_assoc]
      _ = (N * c) * star N := by rw [hc]
      _ = N * (c * star N) := by rw [mul_assoc]
      _ = N * (star N * c) := by rw [hcs]
      _ = (N * star N) * c := by rw [mul_assoc]
  have h₂ : c * (star N * N) = (star N * N) * c := by
    calc c * (star N * N)
        = (c * star N) * N := by rw [mul_assoc]
      _ = (star N * c) * N := by rw [hcs]
      _ = star N * (c * N) := by rw [mul_assoc]
      _ = star N * (N * c) := by rw [hc]
      _ = (star N * N) * c := by rw [mul_assoc]
  rw [h₁, h₂]

/-- `WMC₁` A channel-local weight commuting with the parity anomaly also
    commutes with its squared support `Gap(N) = Σ(N)²`. -/
theorem comm_weight_Gap (c N : B)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    c * Gap N = Gap N * c := by
  have hSig := comm_weight_Sigma c N hc hcs
  dsimp [Gap]
  calc c * (Sigma N * Sigma N)
      = (c * Sigma N) * Sigma N := by rw [mul_assoc]
    _ = (Sigma N * c) * Sigma N := by rw [hSig]
    _ = Sigma N * (c * Sigma N) := by rw [mul_assoc]
    _ = Sigma N * (Sigma N * c) := by rw [hSig]
    _ = (Sigma N * Sigma N) * c := by rw [mul_assoc]

/-- **`WMC₂` Single-Channel Weighted Rotor–Block Product:**
    `(c * J(N)) * (c * Φ(N)) = c² * Σ(N)`. -/
theorem weighted_single_J_mul_Phi (c N : B)
    (h_nil : N * N = 0)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    (c * J N) * (c * Phi N) = (c * c) * Sigma N := by
  have hcJ := comm_weight_J c N hc hcs
  calc (c * J N) * (c * Phi N)
    _ = c * (J N * (c * Phi N)) := by rw [mul_assoc]
    _ = c * ((J N * c) * Phi N) := by rw [← mul_assoc (J N) c (Phi N)]
    _ = c * ((c * J N) * Phi N) := by rw [← hcJ]
    _ = c * (c * (J N * Phi N)) := by rw [mul_assoc c (J N) (Phi N)]
    _ = (c * c) * (J N * Phi N) := by rw [← mul_assoc c c (J N * Phi N)]
    _ = (c * c) * Sigma N := by rw [J_mul_Phi N h_nil]

/-- **`WMC₂` Single-Channel Weighted Chiral Block Square:**
    `(c * Φ(N)) * (c * Φ(N)) = c² * Gap(N)`. -/
theorem weighted_single_Phi_sq (c N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    (c * Phi N) * (c * Phi N) = (c * c) * Gap N := by
  have hcPhi := comm_weight_Phi c N hc hcs
  calc (c * Phi N) * (c * Phi N)
    _ = c * (Phi N * (c * Phi N)) := by rw [mul_assoc]
    _ = c * ((Phi N * c) * Phi N) := by rw [← mul_assoc (Phi N) c (Phi N)]
    _ = c * ((c * Phi N) * Phi N) := by rw [← hcPhi]
    _ = c * (c * (Phi N * Phi N)) := by rw [mul_assoc c (Phi N) (Phi N)]
    _ = (c * c) * (Phi N * Phi N) := by rw [← mul_assoc c c (Phi N * Phi N)]
    _ = (c * c) * Gap N := by rw [Phi_sq_eq_Gap N h_nil h_reg]

/-- `WMC₂` Self-adjoint-weight form of the weighted chiral block square.
    Commutation with `N` alone suffices because `star c = c` derives the
    required commutation with `star N`. -/
theorem weighted_single_Phi_sq_self_adjoint (c N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N)
    (hc_star : star c = c) (hc : c * N = N * c) :
    (c * Phi N) * (c * Phi N) = (c * c) * Gap N := by
  exact weighted_single_Phi_sq c N h_nil h_reg hc
    (comm_star_of_self_adjoint c N hc_star hc)

/-- A channel-local weight squares the skew chiral rotor to `-c² Gap`. -/
theorem weighted_single_J_sq (c N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    (c * J N) * (c * J N) = -((c * c) * Gap N) := by
  have hcJ := comm_weight_J c N hc hcs
  calc (c * J N) * (c * J N)
      = c * (J N * (c * J N)) := by simp only [mul_assoc]
    _ = c * ((J N * c) * J N) := by
      exact congrArg (fun z : B => c * z) (mul_assoc (J N) c (J N)).symm
    _ = c * ((c * J N) * J N) := by rw [← hcJ]
    _ = c * (c * (J N * J N)) := by rw [mul_assoc]
    _ = (c * c) * (J N * J N) := by rw [← mul_assoc]
    _ = (c * c) * -(Phi N * Phi N) := by
      congr 1
      dsimp [J, Phi]
      noncomm_ring [h_nil, star_N_sq N h_nil]
    _ = -((c * c) * Gap N) := by
      rw [Phi_sq_eq_Gap N h_nil h_reg, mul_neg]

/-!
### 2. Cross-Channel Orthogonality of Weighted Chiral Blocks (`WMC₃`)
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

/-- Unweighted cross-channel block annihilation: `Φ(N_a) * Φ(N_b) = 0`. -/
theorem Phi_mul_Phi_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Phi N_a * Phi N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  dsimp [Phi]
  calc (N_a + star N_a) * (N_b + star N_b)
    _ = (N_a + star N_a) * N_b + (N_a + star N_a) * star N_b := by rw [mul_add]
    _ = (N_a * N_b + star N_a * N_b) + (N_a * star N_b + star N_a * star N_b) := by
        rw [add_mul, add_mul]
    _ = (0 + 0) + (0 + 0) := by rw [h_ab, h_sab, h_asb, h_sasb]
    _ = 0 := by rw [add_zero, add_zero]

/-- Orthogonal channels have annihilating skew chiral rotors. -/
theorem J_mul_J_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    J N_a * J N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  dsimp [J]
  rw [sub_mul, mul_sub, mul_sub, h_ab, h_sab, h_asb, h_sasb]
  noncomm_ring

/-- Unweighted cross-channel rotor-block annihilation: `J(N_a) * Φ(N_b) = 0`. -/
theorem J_mul_Phi_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    J N_a * Phi N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  dsimp [J, Phi]
  calc (N_a - star N_a) * (N_b + star N_b)
    _ = (N_a - star N_a) * N_b + (N_a - star N_a) * star N_b := by rw [mul_add]
    _ = (N_a * N_b - star N_a * N_b) + (N_a * star N_b - star N_a * star N_b) := by
        rw [sub_mul, sub_mul]
    _ = (0 - 0) + (0 - 0) := by rw [h_ab, h_sab, h_asb, h_sasb]
    _ = 0 := by rw [sub_self, add_zero]

/-- **`WMC₃` Weighted Cross-Channel Block Annihilation:**
    `(c_a * Φ(N_a)) * (c_b * Φ(N_b)) = 0` requires ONLY that `c_b` commutes with `N_b` and `N_b*`. -/
theorem weighted_Phi_mul_orthog (c_a N_a c_b N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    (c_a * Phi N_a) * (c_b * Phi N_b) = 0 := by
  have hcPhi_b := comm_weight_Phi c_b N_b hc_b hcs_b
  calc (c_a * Phi N_a) * (c_b * Phi N_b)
    _ = (c_a * Phi N_a) * (Phi N_b * c_b) := by rw [hcPhi_b]
    _ = c_a * (Phi N_a * (Phi N_b * c_b)) := by rw [mul_assoc]
    _ = c_a * ((Phi N_a * Phi N_b) * c_b) := by rw [← mul_assoc (Phi N_a) (Phi N_b) c_b]
    _ = c_a * (0 * c_b) := by rw [Phi_mul_Phi_orthog N_a N_b h_ab h_ba h_asb h_sab]
    _ = 0 := by rw [zero_mul, mul_zero]

/-- `WMC₃` Self-adjoint right-weight form of weighted cross-channel
    annihilation. No commutation between `c_b` and channel `N_a` is needed. -/
theorem weighted_Phi_mul_orthog_self_adjoint_right (c_a N_a c_b N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_b_star : star c_b = c_b) (hc_b : c_b * N_b = N_b * c_b) :
    (c_a * Phi N_a) * (c_b * Phi N_b) = 0 := by
  exact weighted_Phi_mul_orthog c_a N_a c_b N_b h_ab h_ba h_asb h_sab
    hc_b (comm_star_of_self_adjoint c_b N_b hc_b_star hc_b)

/-- **`WMC₃` Weighted Cross-Channel Rotor–Block Annihilation:**
    `(c_a * J(N_a)) * (c_b * Φ(N_b)) = 0`. -/
theorem weighted_J_mul_Phi_orthog (c_a N_a c_b N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    (c_a * J N_a) * (c_b * Phi N_b) = 0 := by
  have hcPhi_b := comm_weight_Phi c_b N_b hc_b hcs_b
  calc (c_a * J N_a) * (c_b * Phi N_b)
    _ = (c_a * J N_a) * (Phi N_b * c_b) := by rw [hcPhi_b]
    _ = c_a * (J N_a * (Phi N_b * c_b)) := by rw [mul_assoc]
    _ = c_a * ((J N_a * Phi N_b) * c_b) := by rw [← mul_assoc (J N_a) (Phi N_b) c_b]
    _ = c_a * (0 * c_b) := by rw [J_mul_Phi_orthog N_a N_b h_ab h_ba h_asb h_sab]
    _ = 0 := by rw [zero_mul, mul_zero]

/-!
### 3. Two-Channel Weighted Chiral Block `Φ_w = c_a Φ(N_a) + c_b Φ(N_b)` (`WMC₄–WMC₅`)
-/

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

/-- **`WMC₄` Weighted Rotor–Block Product Generates the Quadratic Weighted Anomaly:**
    `J_w₂ * Φ_w₂ = c_a² Σ(N_a) + c_b² Σ(N_b) = Σ_w₂`. -/
theorem J_w₂_mul_Phi_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    J_w₂ c_a N_a c_b N_b * Phi_w₂ c_a N_a c_b N_b =
      Sigma_w₂ c_a N_a c_b N_b := by
  dsimp [J_w₂, Phi_w₂, Sigma_w₂]
  have h12 := weighted_J_mul_Phi_orthog c_a N_a c_b N_b h_ab h_ba h_asb h_sab hc_b hcs_b
  have h21 := weighted_J_mul_Phi_orthog c_b N_b c_a N_a h_ba h_ab
    (N_b_mul_star_N_a N_a N_b h_asb) (star_N_b_mul_N_a N_a N_b h_sab) hc_a hcs_a
  rw [mul_add_of_cross_orthog (c_a * J N_a) (c_b * J N_b)
        (c_a * Phi N_a) (c_b * Phi N_b) h12 h21,
      weighted_single_J_mul_Phi c_a N_a h_nil_a hc_a hcs_a,
      weighted_single_J_mul_Phi c_b N_b h_nil_b hc_b hcs_b]

/-- **`WMC₅` Main Theorem (Weighted Multi-Channel Chiral Block Square):**
    `Φ_w₂ * Φ_w₂ = c_a² Gap(N_a) + c_b² Gap(N_b) = Gap_w₂`. -/
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
  have h12 := weighted_Phi_mul_orthog c_a N_a c_b N_b h_ab h_ba h_asb h_sab hc_b hcs_b
  have h21 := weighted_Phi_mul_orthog c_b N_b c_a N_a h_ba h_ab
    (N_b_mul_star_N_a N_a N_b h_asb) (star_N_b_mul_N_a N_a N_b h_sab) hc_a hcs_a
  rw [sq_add_of_orthog (c_a * Phi N_a) (c_b * Phi N_b) h12 h21,
      weighted_single_Phi_sq c_a N_a h_nil_a h_reg_a hc_a hcs_a,
      weighted_single_Phi_sq c_b N_b h_nil_b h_reg_b hc_b hcs_b]

/-- `WMC₅` Self-adjoint channel-weight form of the weighted two-channel square.
    Each weight only needs to commute with its own nilpotent; self-adjointness
    derives commutation with that channel's adjoint. No cross-channel weight
    commutation is assumed. -/
theorem Phi_w₂_sq_eq_Gap_w₂_self_adjoint (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a_star : star c_a = c_a) (hc_a : c_a * N_a = N_a * c_a)
    (hc_b_star : star c_b = c_b) (hc_b : c_b * N_b = N_b * c_b) :
    Phi_w₂ c_a N_a c_b N_b * Phi_w₂ c_a N_a c_b N_b =
      Gap_w₂ c_a N_a c_b N_b := by
  exact Phi_w₂_sq_eq_Gap_w₂ c_a N_a c_b N_b
    h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab
    hc_a (comm_star_of_self_adjoint c_a N_a hc_a_star hc_a)
    hc_b (comm_star_of_self_adjoint c_b N_b hc_b_star hc_b)

/-!
### 4. Channel-Selective Projective Filtering & Eigenmode Annihilation (`WMC₆–WMC₈`)
-/

theorem Sigma_mul_Phi_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Sigma N_a * Phi N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  have h1 : Sigma N_a * N_b = 0 := by
    dsimp [Sigma, comm]
    rw [sub_mul, mul_assoc N_a (star N_a) N_b, h_sab, mul_zero,
        mul_assoc (star N_a) N_a N_b, h_ab, mul_zero, sub_self]
  have h2 : Sigma N_a * star N_b = 0 := by
    dsimp [Sigma, comm]
    rw [sub_mul, mul_assoc N_a (star N_a) (star N_b), h_sasb, mul_zero,
        mul_assoc (star N_a) N_a (star N_b), h_asb, mul_zero, sub_self]
  dsimp [Phi]
  rw [mul_add, h1, h2, add_zero]

theorem Gap_mul_Phi_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Gap N_a * Phi N_b = 0 := by
  dsimp [Gap]
  rw [mul_assoc, Sigma_mul_Phi_orthog N_a N_b h_ab h_ba h_asb h_sab, mul_zero]

/-- `Gap(N_a)` acts as the identity on `c_a * Φ(N_a)`:
    `Gap(N_a) * (c_a * Φ(N_a)) = c_a * Φ(N_a)`. -/
theorem Gap_mul_weighted_Phi_same (c_a N_a : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a) :
    Gap N_a * (c_a * Phi N_a) = c_a * Phi N_a := by
  have hcPhi_a := comm_weight_Phi c_a N_a hc_a hcs_a
  calc Gap N_a * (c_a * Phi N_a)
    _ = Gap N_a * (Phi N_a * c_a) := by rw [hcPhi_a]
    _ = (Gap N_a * Phi N_a) * c_a := by rw [← mul_assoc]
    _ = Phi N_a * c_a := by rw [Gap_mul_Phi N_a h_nil_a h_reg_a]
    _ = c_a * Phi N_a := by rw [← hcPhi_a]

/-- `Gap(N_a)` annihilates `c_b * Φ(N_b)` for `a ≠ b`:
    `Gap(N_a) * (c_b * Φ(N_b)) = 0`. -/
theorem Gap_mul_weighted_Phi_orthog (N_a c_b N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Gap N_a * (c_b * Phi N_b) = 0 := by
  have hcPhi_b := comm_weight_Phi c_b N_b hc_b hcs_b
  calc Gap N_a * (c_b * Phi N_b)
    _ = Gap N_a * (Phi N_b * c_b) := by rw [hcPhi_b]
    _ = (Gap N_a * Phi N_b) * c_b := by rw [← mul_assoc]
    _ = 0 * c_b := by rw [Gap_mul_Phi_orthog N_a N_b h_ab h_ba h_asb h_sab]
    _ = 0 := by rw [zero_mul]

/-- **`WMC₆` Channel-Selective Projective Filtering:**
    `Gap(N_a) * Φ_w₂ = c_a * Φ(N_a)`. -/
theorem Gap_left_filter_Phi_w₂ (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    Gap N_a * Phi_w₂ c_a N_a c_b N_b = c_a * Phi N_a := by
  dsimp [Phi_w₂]
  rw [mul_add,
      Gap_mul_weighted_Phi_same c_a N_a h_nil_a h_reg_a hc_a hcs_a,
      Gap_mul_weighted_Phi_orthog N_a c_b N_b h_ab h_ba h_asb h_sab hc_b hcs_b,
      add_zero]

/-- **`WMC₇` Action of `Gap_w₂` on the `a`-th Weighted Channel Mode:**
    `Gap_w₂ * (c_a * Φ(N_a)) = c_a² * (c_a * Φ(N_a))`. -/
theorem Gap_w₂_mul_channel_a (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a) :
    Gap_w₂ c_a N_a c_b N_b * (c_a * Phi N_a) =
      (c_a * c_a) * (c_a * Phi N_a) := by
  dsimp [Gap_w₂]
  have h1 : ((c_a * c_a) * Gap N_a) * (c_a * Phi N_a) =
            (c_a * c_a) * (c_a * Phi N_a) := by
    rw [mul_assoc, Gap_mul_weighted_Phi_same c_a N_a h_nil_a h_reg_a hc_a hcs_a]
  have h2 : ((c_b * c_b) * Gap N_b) * (c_a * Phi N_a) = 0 := by
    rw [mul_assoc,
        Gap_mul_weighted_Phi_orthog N_b c_a N_a h_ba h_ab
          (N_b_mul_star_N_a N_a N_b h_asb) (star_N_b_mul_N_a N_a N_b h_sab) hc_a hcs_a,
        mul_zero]
  rw [add_mul, h1, h2, add_zero]

/-- **`WMC₈` Channel Eigenmode Secular Equation:**
    `(Φ_w₂² - c_a²) * (c_a * Φ(N_a)) = 0`. -/
theorem Phi_w₂_sq_eigenmode_a (c_a N_a c_b N_b : B)
    (h_nil_a : N_a * N_a = 0) (h_reg_a : N_a * star N_a * N_a = N_a)
    (h_nil_b : N_b * N_b = 0) (h_reg_b : N_b * star N_b * N_b = N_b)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0)
    (hc_a : c_a * N_a = N_a * c_a) (hcs_a : c_a * star N_a = star N_a * c_a)
    (hc_b : c_b * N_b = N_b * c_b) (hcs_b : c_b * star N_b = star N_b * c_b) :
    (Phi_w₂ c_a N_a c_b N_b * Phi_w₂ c_a N_a c_b N_b - c_a * c_a) *
      (c_a * Phi N_a) = 0 := by
  rw [sub_mul,
      Phi_w₂_sq_eq_Gap_w₂ c_a N_a c_b N_b
        h_nil_a h_reg_a h_nil_b h_reg_b h_ab h_ba h_asb h_sab hc_a hcs_a hc_b hcs_b,
      Gap_w₂_mul_channel_a c_a N_a c_b N_b
        h_nil_a h_reg_a h_ab h_ba h_asb h_sab hc_a hcs_a,
      sub_self]

/-!
### 5. Three-Channel Supercolor Extension & Cyclotomic Weight Reduction (`WMC₉–WMC₁₀`)
-/

/-- Three-channel weighted chiral block operator `Φ_w₃ = c₁ Φ(N₁) + c₂ Φ(N₂) + c₃ Φ(N₃)`. -/
def Phi_w₃ (c₁ N₁ c₂ N₂ c₃ N₃ : B) : B :=
  Phi_w₂ c₁ N₁ c₂ N₂ + c₃ * Phi N₃

/-- Three-channel weighted chiral rotor `J_w₃`. -/
def J_w₃ (c₁ N₁ c₂ N₂ c₃ N₃ : B) : B :=
  J_w₂ c₁ N₁ c₂ N₂ + c₃ * J N₃

/-- Three-channel quadratic weighted parity anomaly `Σ_w₃`. -/
def Sigma_w₃ (c₁ N₁ c₂ N₂ c₃ N₃ : B) : B :=
  Sigma_w₂ c₁ N₁ c₂ N₂ + (c₃ * c₃) * Sigma N₃

/-- Three-channel weighted spectral gap `Gap_w₃ = c₁² Gap(N₁) + c₂² Gap(N₂) + c₃² Gap(N₃)`. -/
def Gap_w₃ (c₁ N₁ c₂ N₂ c₃ N₃ : B) : B :=
  Gap_w₂ c₁ N₁ c₂ N₂ + (c₃ * c₃) * Gap N₃

/-- Three-channel channel-selective filtering. The support of channel one
extracts its weighted block from the full three-channel sum. Only each weight's
commutation with its own nilpotent channel is required. -/
theorem Gap_left_filter_Phi_w₃_channel1 (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h1_nil : N₁ * N₁ = 0) (h1_reg : N₁ * star N₁ * N₁ = N₁)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (hc1 : c₁ * N₁ = N₁ * c₁) (hcs1 : c₁ * star N₁ = star N₁ * c₁)
    (hc2 : c₂ * N₂ = N₂ * c₂) (hcs2 : c₂ * star N₂ = star N₂ * c₂)
    (hc3 : c₃ * N₃ = N₃ * c₃) (hcs3 : c₃ * star N₃ = star N₃ * c₃) :
    Gap N₁ * Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ = c₁ * Phi N₁ := by
  dsimp [Phi_w₃]
  rw [mul_add,
    Gap_left_filter_Phi_w₂ c₁ N₁ c₂ N₂ h1_nil h1_reg
      h12_ab h12_ba h12_asb h12_sab hc1 hcs1 hc2 hcs2,
    Gap_mul_weighted_Phi_orthog N₁ c₃ N₃
      h13_ab h13_ba h13_asb h13_sab hc3 hcs3,
    add_zero]

/-- The support of channel two extracts its weighted block from the
three-channel sum. -/
theorem Gap_left_filter_Phi_w₃_channel2 (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h2_nil : N₂ * N₂ = 0) (h2_reg : N₂ * star N₂ * N₂ = N₂)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc1 : c₁ * N₁ = N₁ * c₁) (hcs1 : c₁ * star N₁ = star N₁ * c₁)
    (hc2 : c₂ * N₂ = N₂ * c₂) (hcs2 : c₂ * star N₂ = star N₂ * c₂)
    (hc3 : c₃ * N₃ = N₃ * c₃) (hcs3 : c₃ * star N₃ = star N₃ * c₃) :
    Gap N₂ * Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ = c₂ * Phi N₂ := by
  dsimp [Phi_w₃, Phi_w₂]
  rw [mul_add, mul_add,
    Gap_mul_weighted_Phi_orthog N₂ c₁ N₁ h12_ba h12_ab
      (N_b_mul_star_N_a N₁ N₂ h12_asb)
      (star_N_b_mul_N_a N₁ N₂ h12_sab) hc1 hcs1,
    Gap_mul_weighted_Phi_same c₂ N₂ h2_nil h2_reg hc2 hcs2,
    Gap_mul_weighted_Phi_orthog N₂ c₃ N₃
      h23_ab h23_ba h23_asb h23_sab hc3 hcs3,
    zero_add, add_zero]

/-- The support of channel three extracts its weighted block from the
three-channel sum. -/
theorem Gap_left_filter_Phi_w₃_channel3 (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h3_nil : N₃ * N₃ = 0) (h3_reg : N₃ * star N₃ * N₃ = N₃)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc1 : c₁ * N₁ = N₁ * c₁) (hcs1 : c₁ * star N₁ = star N₁ * c₁)
    (hc2 : c₂ * N₂ = N₂ * c₂) (hcs2 : c₂ * star N₂ = star N₂ * c₂)
    (hc3 : c₃ * N₃ = N₃ * c₃) (hcs3 : c₃ * star N₃ = star N₃ * c₃) :
    Gap N₃ * Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ = c₃ * Phi N₃ := by
  dsimp [Phi_w₃, Phi_w₂]
  rw [mul_add, mul_add,
    Gap_mul_weighted_Phi_orthog N₃ c₁ N₁ h13_ba h13_ab
      (N_b_mul_star_N_a N₁ N₃ h13_asb)
      (star_N_b_mul_N_a N₁ N₃ h13_sab) hc1 hcs1,
    Gap_mul_weighted_Phi_orthog N₃ c₂ N₂ h23_ba h23_ab
      (N_b_mul_star_N_a N₂ N₃ h23_asb)
      (star_N_b_mul_N_a N₂ N₃ h23_sab) hc2 hcs2,
    Gap_mul_weighted_Phi_same c₃ N₃ h3_nil h3_reg hc3 hcs3,
    zero_add, zero_add]

/-- **Three-channel weighted rotor–block product:**
    `J_w₃ * Φ_w₃` is the sum of the three squared-weight channel anomalies.
    Each weight commutes only with its own channel; cross-channel products use
    the primitive four orthogonality relations. -/
theorem J_w₃_mul_Phi_w₃ (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h1_nil : N₁ * N₁ = 0)
    (h2_nil : N₂ * N₂ = 0)
    (h3_nil : N₃ * N₃ = 0)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc1 : c₁ * N₁ = N₁ * c₁) (hcs1 : c₁ * star N₁ = star N₁ * c₁)
    (hc2 : c₂ * N₂ = N₂ * c₂) (hcs2 : c₂ * star N₂ = star N₂ * c₂)
    (hc3 : c₃ * N₃ = N₃ * c₃) (hcs3 : c₃ * star N₃ = star N₃ * c₃) :
    J_w₃ c₁ N₁ c₂ N₂ c₃ N₃ * Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ =
      Sigma_w₃ c₁ N₁ c₂ N₂ c₃ N₃ := by
  dsimp [J_w₃, Phi_w₃, Sigma_w₃]
  have h12_3 : J_w₂ c₁ N₁ c₂ N₂ * (c₃ * Phi N₃) = 0 := by
    dsimp [J_w₂]
    rw [add_mul,
      weighted_J_mul_Phi_orthog c₁ N₁ c₃ N₃ h13_ab h13_ba h13_asb h13_sab hc3 hcs3,
      weighted_J_mul_Phi_orthog c₂ N₂ c₃ N₃ h23_ab h23_ba h23_asb h23_sab hc3 hcs3,
      add_zero]
  have h3_12 : (c₃ * J N₃) * Phi_w₂ c₁ N₁ c₂ N₂ = 0 := by
    dsimp [Phi_w₂]
    rw [mul_add,
      weighted_J_mul_Phi_orthog c₃ N₃ c₁ N₁ h13_ba h13_ab
        (N_b_mul_star_N_a N₁ N₃ h13_asb) (star_N_b_mul_N_a N₁ N₃ h13_sab) hc1 hcs1,
      weighted_J_mul_Phi_orthog c₃ N₃ c₂ N₂ h23_ba h23_ab
        (N_b_mul_star_N_a N₂ N₃ h23_asb) (star_N_b_mul_N_a N₂ N₃ h23_sab) hc2 hcs2,
      add_zero]
  rw [mul_add_of_cross_orthog (J_w₂ c₁ N₁ c₂ N₂) (c₃ * J N₃)
      (Phi_w₂ c₁ N₁ c₂ N₂) (c₃ * Phi N₃) h12_3 h3_12,
    J_w₂_mul_Phi_w₂ c₁ N₁ c₂ N₂ h1_nil h2_nil
      h12_ab h12_ba h12_asb h12_sab hc1 hcs1 hc2 hcs2,
    weighted_single_J_mul_Phi c₃ N₃ h3_nil hc3 hcs3]

/-- **`WMC₉` Three-Channel Weighted Chiral Block Square:**
    `Φ_w₃ * Φ_w₃ = c₁² Gap(N₁) + c₂² Gap(N₂) + c₃² Gap(N₃) = Gap_w₃`. -/
theorem Phi_w₃_sq_eq_Gap_w₃ (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h1_nil : N₁ * N₁ = 0) (h1_reg : N₁ * star N₁ * N₁ = N₁)
    (h2_nil : N₂ * N₂ = 0) (h2_reg : N₂ * star N₂ * N₂ = N₂)
    (h3_nil : N₃ * N₃ = 0) (h3_reg : N₃ * star N₃ * N₃ = N₃)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc1 : c₁ * N₁ = N₁ * c₁) (hcs1 : c₁ * star N₁ = star N₁ * c₁)
    (hc2 : c₂ * N₂ = N₂ * c₂) (hcs2 : c₂ * star N₂ = star N₂ * c₂)
    (hc3 : c₃ * N₃ = N₃ * c₃) (hcs3 : c₃ * star N₃ = star N₃ * c₃) :
    Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ * Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ =
      Gap_w₃ c₁ N₁ c₂ N₂ c₃ N₃ := by
  dsimp [Phi_w₃, Gap_w₃]
  have h12_3 : Phi_w₂ c₁ N₁ c₂ N₂ * (c₃ * Phi N₃) = 0 := by
    dsimp [Phi_w₂]
    rw [add_mul,
        weighted_Phi_mul_orthog c₁ N₁ c₃ N₃ h13_ab h13_ba h13_asb h13_sab hc3 hcs3,
        weighted_Phi_mul_orthog c₂ N₂ c₃ N₃ h23_ab h23_ba h23_asb h23_sab hc3 hcs3,
        add_zero]
  have h3_12 : (c₃ * Phi N₃) * Phi_w₂ c₁ N₁ c₂ N₂ = 0 := by
    dsimp [Phi_w₂]
    rw [mul_add,
        weighted_Phi_mul_orthog c₃ N₃ c₁ N₁ h13_ba h13_ab
          (N_b_mul_star_N_a N₁ N₃ h13_asb) (star_N_b_mul_N_a N₁ N₃ h13_sab) hc1 hcs1,
        weighted_Phi_mul_orthog c₃ N₃ c₂ N₂ h23_ba h23_ab
          (N_b_mul_star_N_a N₂ N₃ h23_asb) (star_N_b_mul_N_a N₂ N₃ h23_sab) hc2 hcs2,
        add_zero]
  rw [sq_add_of_orthog (Phi_w₂ c₁ N₁ c₂ N₂) (c₃ * Phi N₃) h12_3 h3_12,
      Phi_w₂_sq_eq_Gap_w₂ c₁ N₁ c₂ N₂
        h1_nil h1_reg h2_nil h2_reg h12_ab h12_ba h12_asb h12_sab hc1 hcs1 hc2 hcs2,
      weighted_single_Phi_sq c₃ N₃ h3_nil h3_reg hc3 hcs3]

/-- Self-adjoint-weight form of the three-channel block-square theorem.
Each coefficient commutes only with its own nilpotent; self-adjointness
derives the corresponding commutation with the adjoint generator. -/
theorem Phi_w₃_sq_eq_Gap_w₃_self_adjoint_weights (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h1_nil : N₁ * N₁ = 0) (h1_reg : N₁ * star N₁ * N₁ = N₁)
    (h2_nil : N₂ * N₂ = 0) (h2_reg : N₂ * star N₂ * N₂ = N₂)
    (h3_nil : N₃ * N₃ = 0) (h3_reg : N₃ * star N₃ * N₃ = N₃)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc1_star : star c₁ = c₁) (hc1 : c₁ * N₁ = N₁ * c₁)
    (hc2_star : star c₂ = c₂) (hc2 : c₂ * N₂ = N₂ * c₂)
    (hc3_star : star c₃ = c₃) (hc3 : c₃ * N₃ = N₃ * c₃) :
    Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ * Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ =
      Gap_w₃ c₁ N₁ c₂ N₂ c₃ N₃ := by
  exact Phi_w₃_sq_eq_Gap_w₃ c₁ N₁ c₂ N₂ c₃ N₃
    h1_nil h1_reg h2_nil h2_reg h3_nil h3_reg
    h12_ab h12_ba h12_asb h12_sab
    h13_ab h13_ba h13_asb h13_sab
    h23_ab h23_ba h23_asb h23_sab
    hc1 (comm_star_of_self_adjoint c₁ N₁ hc1_star hc1)
    hc2 (comm_star_of_self_adjoint c₂ N₂ hc2_star hc2)
    hc3 (comm_star_of_self_adjoint c₃ N₃ hc3_star hc3)

/-- The three-channel weighted gap acts on channel one's weighted block by
its squared weight. -/
theorem Gap_w₃_mul_channel1 (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h1_nil : N₁ * N₁ = 0) (h1_reg : N₁ * star N₁ * N₁ = N₁)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (hc1 : c₁ * N₁ = N₁ * c₁) (hcs1 : c₁ * star N₁ = star N₁ * c₁) :
    Gap_w₃ c₁ N₁ c₂ N₂ c₃ N₃ * (c₁ * Phi N₁) =
      (c₁ * c₁) * (c₁ * Phi N₁) := by
  dsimp [Gap_w₃, Gap_w₂]
  have h1 : ((c₁ * c₁) * Gap N₁) * (c₁ * Phi N₁) =
      (c₁ * c₁) * (c₁ * Phi N₁) := by
    rw [mul_assoc,
      Gap_mul_weighted_Phi_same c₁ N₁ h1_nil h1_reg hc1 hcs1]
  have h2 : ((c₂ * c₂) * Gap N₂) * (c₁ * Phi N₁) = 0 := by
    rw [mul_assoc,
      Gap_mul_weighted_Phi_orthog N₂ c₁ N₁ h12_ba h12_ab
        (N_b_mul_star_N_a N₁ N₂ h12_asb)
        (star_N_b_mul_N_a N₁ N₂ h12_sab) hc1 hcs1,
      mul_zero]
  have h3 : ((c₃ * c₃) * Gap N₃) * (c₁ * Phi N₁) = 0 := by
    rw [mul_assoc,
      Gap_mul_weighted_Phi_orthog N₃ c₁ N₁ h13_ba h13_ab
        (N_b_mul_star_N_a N₁ N₃ h13_asb)
        (star_N_b_mul_N_a N₁ N₃ h13_sab) hc1 hcs1,
      mul_zero]
  rw [add_mul, add_mul, h1, h2, h3, add_zero, add_zero]

/-- The channel-one weighted block satisfies the three-channel secular
equation at squared weight `c₁²`. -/
theorem Phi_w₃_sq_eigenmode_channel1 (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h1_nil : N₁ * N₁ = 0) (h1_reg : N₁ * star N₁ * N₁ = N₁)
    (h2_nil : N₂ * N₂ = 0) (h2_reg : N₂ * star N₂ * N₂ = N₂)
    (h3_nil : N₃ * N₃ = 0) (h3_reg : N₃ * star N₃ * N₃ = N₃)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc1 : c₁ * N₁ = N₁ * c₁) (hcs1 : c₁ * star N₁ = star N₁ * c₁)
    (hc2 : c₂ * N₂ = N₂ * c₂) (hcs2 : c₂ * star N₂ = star N₂ * c₂)
    (hc3 : c₃ * N₃ = N₃ * c₃) (hcs3 : c₃ * star N₃ = star N₃ * c₃) :
    (Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ * Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ - c₁ * c₁) *
      (c₁ * Phi N₁) = 0 := by
  rw [sub_mul,
    Phi_w₃_sq_eq_Gap_w₃ c₁ N₁ c₂ N₂ c₃ N₃
      h1_nil h1_reg h2_nil h2_reg h3_nil h3_reg
      h12_ab h12_ba h12_asb h12_sab
      h13_ab h13_ba h13_asb h13_sab
      h23_ab h23_ba h23_asb h23_sab hc1 hcs1 hc2 hcs2 hc3 hcs3,
    Gap_w₃_mul_channel1 c₁ N₁ c₂ N₂ c₃ N₃
      h1_nil h1_reg h12_ab h12_ba h12_asb h12_sab
      h13_ab h13_ba h13_asb h13_sab hc1 hcs1,
    sub_self]

/-- The three-channel weighted gap acts on channel two's weighted block by
its squared weight. Only the selected channel's weight commutation is needed. -/
theorem Gap_w₃_mul_channel2 (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h2_nil : N₂ * N₂ = 0) (h2_reg : N₂ * star N₂ * N₂ = N₂)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc2 : c₂ * N₂ = N₂ * c₂) (hcs2 : c₂ * star N₂ = star N₂ * c₂) :
    Gap_w₃ c₁ N₁ c₂ N₂ c₃ N₃ * (c₂ * Phi N₂) =
      (c₂ * c₂) * (c₂ * Phi N₂) := by
  dsimp [Gap_w₃, Gap_w₂]
  have h1 : ((c₁ * c₁) * Gap N₁) * (c₂ * Phi N₂) = 0 := by
    rw [mul_assoc,
      Gap_mul_weighted_Phi_orthog N₁ c₂ N₂ h12_ab h12_ba
        h12_asb h12_sab hc2 hcs2,
      mul_zero]
  have h2 : ((c₂ * c₂) * Gap N₂) * (c₂ * Phi N₂) =
      (c₂ * c₂) * (c₂ * Phi N₂) := by
    rw [mul_assoc,
      Gap_mul_weighted_Phi_same c₂ N₂ h2_nil h2_reg hc2 hcs2]
  have h3 : ((c₃ * c₃) * Gap N₃) * (c₂ * Phi N₂) = 0 := by
    rw [mul_assoc,
      Gap_mul_weighted_Phi_orthog N₃ c₂ N₂ h23_ba h23_ab
        (N_b_mul_star_N_a N₂ N₃ h23_asb)
        (star_N_b_mul_N_a N₂ N₃ h23_sab) hc2 hcs2,
      mul_zero]
  rw [add_mul, add_mul, h1, h2, h3, zero_add, add_zero]

/-- The channel-two weighted block satisfies the three-channel secular
equation at squared weight `c₂²`. -/
theorem Phi_w₃_sq_eigenmode_channel2 (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h1_nil : N₁ * N₁ = 0) (h1_reg : N₁ * star N₁ * N₁ = N₁)
    (h2_nil : N₂ * N₂ = 0) (h2_reg : N₂ * star N₂ * N₂ = N₂)
    (h3_nil : N₃ * N₃ = 0) (h3_reg : N₃ * star N₃ * N₃ = N₃)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc1 : c₁ * N₁ = N₁ * c₁) (hcs1 : c₁ * star N₁ = star N₁ * c₁)
    (hc2 : c₂ * N₂ = N₂ * c₂) (hcs2 : c₂ * star N₂ = star N₂ * c₂)
    (hc3 : c₃ * N₃ = N₃ * c₃) (hcs3 : c₃ * star N₃ = star N₃ * c₃) :
    (Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ * Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ - c₂ * c₂) *
      (c₂ * Phi N₂) = 0 := by
  rw [sub_mul,
    Phi_w₃_sq_eq_Gap_w₃ c₁ N₁ c₂ N₂ c₃ N₃
      h1_nil h1_reg h2_nil h2_reg h3_nil h3_reg
      h12_ab h12_ba h12_asb h12_sab
      h13_ab h13_ba h13_asb h13_sab
      h23_ab h23_ba h23_asb h23_sab hc1 hcs1 hc2 hcs2 hc3 hcs3,
    Gap_w₃_mul_channel2 c₁ N₁ c₂ N₂ c₃ N₃
      h2_nil h2_reg h12_ab h12_ba h12_asb h12_sab
      h23_ab h23_ba h23_asb h23_sab hc2 hcs2,
    sub_self]

/-- The three-channel weighted gap acts on channel three's weighted block by
its squared weight. Only the selected channel's weight commutation is needed. -/
theorem Gap_w₃_mul_channel3 (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h3_nil : N₃ * N₃ = 0) (h3_reg : N₃ * star N₃ * N₃ = N₃)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc3 : c₃ * N₃ = N₃ * c₃) (hcs3 : c₃ * star N₃ = star N₃ * c₃) :
    Gap_w₃ c₁ N₁ c₂ N₂ c₃ N₃ * (c₃ * Phi N₃) =
      (c₃ * c₃) * (c₃ * Phi N₃) := by
  dsimp [Gap_w₃, Gap_w₂]
  have h1 : ((c₁ * c₁) * Gap N₁) * (c₃ * Phi N₃) = 0 := by
    rw [mul_assoc,
      Gap_mul_weighted_Phi_orthog N₁ c₃ N₃ h13_ab h13_ba
        h13_asb h13_sab hc3 hcs3,
      mul_zero]
  have h2 : ((c₂ * c₂) * Gap N₂) * (c₃ * Phi N₃) = 0 := by
    rw [mul_assoc,
      Gap_mul_weighted_Phi_orthog N₂ c₃ N₃ h23_ab h23_ba
        h23_asb h23_sab hc3 hcs3,
      mul_zero]
  have h3 : ((c₃ * c₃) * Gap N₃) * (c₃ * Phi N₃) =
      (c₃ * c₃) * (c₃ * Phi N₃) := by
    rw [mul_assoc,
      Gap_mul_weighted_Phi_same c₃ N₃ h3_nil h3_reg hc3 hcs3]
  rw [add_mul, add_mul, h1, h2, h3, zero_add, zero_add]

/-- The channel-three weighted block satisfies the three-channel secular
equation at squared weight `c₃²`. -/
theorem Phi_w₃_sq_eigenmode_channel3 (c₁ N₁ c₂ N₂ c₃ N₃ : B)
    (h1_nil : N₁ * N₁ = 0) (h1_reg : N₁ * star N₁ * N₁ = N₁)
    (h2_nil : N₂ * N₂ = 0) (h2_reg : N₂ * star N₂ * N₂ = N₂)
    (h3_nil : N₃ * N₃ = 0) (h3_reg : N₃ * star N₃ * N₃ = N₃)
    (h12_ab : N₁ * N₂ = 0) (h12_ba : N₂ * N₁ = 0)
    (h12_asb : N₁ * star N₂ = 0) (h12_sab : star N₁ * N₂ = 0)
    (h13_ab : N₁ * N₃ = 0) (h13_ba : N₃ * N₁ = 0)
    (h13_asb : N₁ * star N₃ = 0) (h13_sab : star N₁ * N₃ = 0)
    (h23_ab : N₂ * N₃ = 0) (h23_ba : N₃ * N₂ = 0)
    (h23_asb : N₂ * star N₃ = 0) (h23_sab : star N₂ * N₃ = 0)
    (hc1 : c₁ * N₁ = N₁ * c₁) (hcs1 : c₁ * star N₁ = star N₁ * c₁)
    (hc2 : c₂ * N₂ = N₂ * c₂) (hcs2 : c₂ * star N₂ = star N₂ * c₂)
    (hc3 : c₃ * N₃ = N₃ * c₃) (hcs3 : c₃ * star N₃ = star N₃ * c₃) :
    (Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ * Phi_w₃ c₁ N₁ c₂ N₂ c₃ N₃ - c₃ * c₃) *
      (c₃ * Phi N₃) = 0 := by
  rw [sub_mul,
    Phi_w₃_sq_eq_Gap_w₃ c₁ N₁ c₂ N₂ c₃ N₃
      h1_nil h1_reg h2_nil h2_reg h3_nil h3_reg
      h12_ab h12_ba h12_asb h12_sab
      h13_ab h13_ba h13_asb h13_sab
      h23_ab h23_ba h23_asb h23_sab hc1 hcs1 hc2 hcs2 hc3 hcs3,
    Gap_w₃_mul_channel3 c₁ N₁ c₂ N₂ c₃ N₃
      h3_nil h3_reg h13_ab h13_ba h13_asb h13_sab
      h23_ab h23_ba h23_asb h23_sab hc3 hcs3,
    sub_self]

/-- **`WMC₁₀` Cyclotomic Root Weight Specialization (`Φ₆(u) = u² - u + 1 = 0`):**
    When a channel weight `u` is a root of `u² - u + 1 = 0`, its squared chiral block
    `(u * Φ(N))²` reduces linearly to `(u - 1) * Gap(N)`. -/
theorem cyclotomic_weighted_Phi_sq (u N : B)
    (h_cyc : u * u - u + 1 = 0)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N)
    (hu : u * N = N * u) (hus : u * star N = star N * u) :
    (u * Phi N) * (u * Phi N) = (u - 1) * Gap N := by
  have hu_sq : u * u = u - 1 := by
    calc u * u
      _ = (u * u - u + 1) + (u - 1) := by abel
      _ = 0 + (u - 1) := by rw [h_cyc]
      _ = u - 1 := by rw [zero_add]
  rw [weighted_single_Phi_sq u N h_nil h_reg hu hus, hu_sq]

/-- **Finite weighted channel square.** For any finite family of regular
square-zero channels with pairwise primitive orthogonality, the weighted
chiral block sum squares to the sum of the channel gaps weighted by `cᵢ²`.
Each coefficient is required to commute only with its own channel and its
adjoint; no coefficient-to-foreign-channel commutation is assumed. -/
theorem weighted_Phi_sum_sq_eq_weighted_Gap {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i)
    (h_weight_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i) :
    (∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * Phi (N i)) =
      ∑ i ∈ s, (c i * c i) * Gap (N i) := by
  calc
    (∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * Phi (N i)) =
        ∑ i ∈ s, (c i * Phi (N i)) * (c i * Phi (N i)) :=
      sum_mul_self_of_pairwise_annihilating s (fun i => c i * Phi (N i)) (by
        intro i hi j hj hij
        obtain ⟨hij₁, hji₁, hij₂, hij₃⟩ := h_orth i hi j hj hij
        exact weighted_Phi_mul_orthog (c i) (N i) (c j) (N j)
          hij₁ hji₁ hij₂ hij₃ (h_weight j hj) (h_weight_star j hj))
    _ = ∑ i ∈ s, (c i * c i) * Gap (N i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_single_Phi_sq (c i) (N i) (h_nil i hi) (h_reg i hi)
        (h_weight i hi) (h_weight_star i hi)

/-- Self-adjoint-weight form of the finite weighted channel square. Each
coefficient need only commute with its own nilpotent: self-adjointness derives
the corresponding commutation with the adjoint generator. -/
theorem weighted_Phi_sum_sq_eq_weighted_Gap_self_adjoint {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight_star : ∀ i ∈ s, star (c i) = c i)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i) :
    (∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * Phi (N i)) =
      ∑ i ∈ s, (c i * c i) * Gap (N i) := by
  exact weighted_Phi_sum_sq_eq_weighted_Gap s c N h_nil h_reg h_orth h_weight
    (fun i hi => comm_star_of_self_adjoint (c i) (N i)
      (h_weight_star i hi) (h_weight i hi))

/-- **Finite weighted rotor square.** For a finite family of regular
square-zero channels with pairwise primitive orthogonality, the weighted
skew chiral sum squares to the negative sum of channel gaps weighted by
`cᵢ²`. Each coefficient commutes only with its own channel and adjoint. -/
theorem weighted_J_sum_sq_eq_neg_weighted_Gap {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i)
    (h_weight_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i) :
    (∑ i ∈ s, c i * J (N i)) * (∑ i ∈ s, c i * J (N i)) =
      - ∑ i ∈ s, (c i * c i) * Gap (N i) := by
  calc
    (∑ i ∈ s, c i * J (N i)) * (∑ i ∈ s, c i * J (N i)) =
        ∑ i ∈ s, (c i * J (N i)) * (c i * J (N i)) :=
      sum_mul_self_of_pairwise_annihilating s (fun i => c i * J (N i)) (by
        intro i hi j hj hij
        obtain ⟨hij₁, hji₁, hij₂, hij₃⟩ := h_orth i hi j hj hij
        have hcomm : c j * J (N j) = J (N j) * c j :=
          comm_weight_J (c j) (N j) (h_weight j hj) (h_weight_star j hj)
        calc (c i * J (N i)) * (c j * J (N j))
            = (c i * J (N i)) * (J (N j) * c j) := by rw [hcomm]
          _ = c i * ((J (N i) * J (N j)) * c j) := by
            rw [mul_assoc, ← mul_assoc (J (N i)) (J (N j)) (c j)]
          _ = c i * (0 * c j) := by
            rw [J_mul_J_orthog (N i) (N j) hij₁ hji₁ hij₂ hij₃]
          _ = 0 := by rw [zero_mul, mul_zero])
    _ = ∑ i ∈ s, -((c i * c i) * Gap (N i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_single_J_sq (c i) (N i) (h_nil i hi) (h_reg i hi)
        (h_weight i hi) (h_weight_star i hi)
    _ = - ∑ i ∈ s, (c i * c i) * Gap (N i) := by
      rw [Finset.sum_neg_distrib]

/-- Self-adjoint local weights need only commute with their own nilpotent;
the involution derives commutation with each adjoint channel. -/
theorem weighted_J_sum_sq_eq_neg_weighted_Gap_self_adjoint {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight_star : ∀ i ∈ s, star (c i) = c i)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i) :
    (∑ i ∈ s, c i * J (N i)) * (∑ i ∈ s, c i * J (N i)) =
      - ∑ i ∈ s, (c i * c i) * Gap (N i) := by
  exact weighted_J_sum_sq_eq_neg_weighted_Gap s c N h_nil h_reg h_orth h_weight
    (fun i hi => comm_star_of_self_adjoint (c i) (N i)
      (h_weight_star i hi) (h_weight i hi))

/-- Reversing the chiral block and rotor gives the negative channel anomaly. -/
theorem weighted_single_Phi_mul_J (c N : B)
    (h_nil : N * N = 0)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    (c * Phi N) * (c * J N) = -((c * c) * Sigma N) := by
  have hcPhi := comm_weight_Phi c N hc hcs
  have hPhiJ : Phi N * J N = -Sigma N := by
    dsimp [Phi, J, Sigma, comm]
    calc (N + star N) * (N - star N)
        = (N + star N) * N - (N + star N) * star N := by rw [mul_sub]
      _ = (N * N + star N * N) - (N * star N + star N * star N) := by
        rw [add_mul, add_mul]
      _ = star N * N - N * star N := by
        rw [h_nil, star_N_sq N h_nil, zero_add, add_zero]
      _ = -(N * star N - star N * N) := by rw [neg_sub]
  calc (c * Phi N) * (c * J N)
      = c * ((Phi N * c) * J N) := by noncomm_ring
    _ = c * ((Phi N * c) * J N) := by rw [← mul_assoc]
    _ = c * ((c * Phi N) * J N) := by rw [← hcPhi]
    _ = c * (c * (Phi N * J N)) := by rw [mul_assoc]
    _ = (c * c) * (Phi N * J N) := by rw [← mul_assoc]
    _ = -((c * c) * Sigma N) := by rw [hPhiJ, mul_neg]

/-- Cross-channel reverse rotor-block products vanish under the same primitive
orthogonality assumptions as the forward products. -/
theorem Phi_mul_J_orthog (N_a N_b : B)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Phi N_a * J N_b = 0 := by
  have h_sasb := star_N_a_mul_star_N_b N_a N_b h_ba
  dsimp [Phi, J]
  noncomm_ring [h_ab, h_ba, h_asb, h_sab, h_sasb]

/-- A finite weighted rotor sum times its block sum is the sum of the
quadratically weighted channel anomalies. Only each right-channel weight must
commute with that channel. -/
theorem weighted_J_sum_mul_Phi_sum {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i)
    (h_weight_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i) :
    (∑ i ∈ s, c i * J (N i)) * (∑ i ∈ s, c i * Phi (N i)) =
      ∑ i ∈ s, (c i * c i) * Sigma (N i) := by
  calc
    (∑ i ∈ s, c i * J (N i)) * (∑ i ∈ s, c i * Phi (N i)) =
        ∑ i ∈ s, (c i * J (N i)) * (c i * Phi (N i)) :=
      sum_mul_sum_of_pairwise_cross_annihilating s
        (fun i => c i * J (N i)) (fun i => c i * Phi (N i)) (by
          intro i hi j hj hij
          obtain ⟨hij₁, hji₁, hij₂, hij₃⟩ := h_orth i hi j hj hij
          exact weighted_J_mul_Phi_orthog (c i) (N i) (c j) (N j)
            hij₁ hji₁ hij₂ hij₃ (h_weight j hj) (h_weight_star j hj))
    _ = ∑ i ∈ s, (c i * c i) * Sigma (N i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_single_J_mul_Phi (c i) (N i) (h_nil i hi)
        (h_weight i hi) (h_weight_star i hi)

/-- The reversed finite weighted product is the negative of the summed
quadratic anomaly. -/
theorem weighted_Phi_sum_mul_J_sum {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i)
    (h_weight_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i) :
    (∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * J (N i)) =
      - ∑ i ∈ s, (c i * c i) * Sigma (N i) := by
  calc
    (∑ i ∈ s, c i * Phi (N i)) * (∑ i ∈ s, c i * J (N i)) =
        ∑ i ∈ s, (c i * Phi (N i)) * (c i * J (N i)) :=
      sum_mul_sum_of_pairwise_cross_annihilating s
        (fun i => c i * Phi (N i)) (fun i => c i * J (N i)) (by
          intro i hi j hj hij
          obtain ⟨hij₁, hji₁, hij₂, hij₃⟩ := h_orth i hi j hj hij
          exact weighted_cross_zero (c i) (Phi (N i)) (c j) (J (N j))
            (Phi_mul_J_orthog (N i) (N j) hij₁ hji₁ hij₂ hij₃)
            (comm_weight_J (c j) (N j) (h_weight j hj) (h_weight_star j hj)))
    _ = ∑ i ∈ s, -((c i * c i) * Sigma (N i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_single_Phi_mul_J (c i) (N i) (h_nil i hi)
        (h_weight i hi) (h_weight_star i hi)
    _ = - ∑ i ∈ s, (c i * c i) * Sigma (N i) := by
      rw [Finset.sum_neg_distrib]

/-- The finite weighted blocks anticommute; the identity is the sum of the
forward and reverse product theorems. -/
theorem weighted_chiral_sum_anticomm {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i)
    (h_weight_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i) :
    MultiChannelAnomalyGapPoset.anticomm
      (∑ i ∈ s, c i * Phi (N i)) (∑ i ∈ s, c i * J (N i)) = 0 := by
  dsimp [MultiChannelAnomalyGapPoset.anticomm]
  rw [weighted_Phi_sum_mul_J_sum s c N h_nil h_orth h_weight h_weight_star,
    weighted_J_sum_mul_Phi_sum s c N h_nil h_orth h_weight h_weight_star,
    add_comm (-∑ i ∈ s, (c i * c i) * Sigma (N i)),
    ← sub_eq_add_neg, sub_self]

/-- The commutator of the finite weighted rotor and block sums is twice the
quadratic-weighted anomaly. -/
theorem weighted_chiral_sum_comm {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i)
    (h_weight_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i) :
    MultiChannelAnomalyGapPoset.comm
      (∑ i ∈ s, c i * J (N i)) (∑ i ∈ s, c i * Phi (N i)) =
      (∑ i ∈ s, (c i * c i) * Sigma (N i)) +
        (∑ i ∈ s, (c i * c i) * Sigma (N i)) := by
  dsimp [MultiChannelAnomalyGapPoset.comm]
  rw [weighted_J_sum_mul_Phi_sum s c N h_nil h_orth h_weight h_weight_star,
    weighted_Phi_sum_mul_J_sum s c N h_nil h_orth h_weight h_weight_star,
    sub_eq_add_neg, neg_neg]

/-- Grade-three Jordan associator in the unnormalized convention used here. -/
def JordanAssoc (X Y Z : B) : B :=
  MultiChannelAnomalyGapPoset.anticomm
      (MultiChannelAnomalyGapPoset.anticomm X Y) Z -
    MultiChannelAnomalyGapPoset.anticomm X
      (MultiChannelAnomalyGapPoset.anticomm Y Z)

/-- Four copies of an element, kept in an additive-group-friendly form. -/
def quad (x : B) : B := (x + x) + (x + x)

/-- Cubic power with the association fixed for noncommutative rings. -/
def cube (c : B) : B := (c * c) * c

theorem Gap_mul_J (N : B) (h_nil : N * N = 0)
    (h_reg : N * star N * N = N) : Gap N * J N = J N := by
  have hPhiJ : Phi N * J N = -Sigma N := by
    dsimp [Phi, J, Sigma, comm]
    calc (N + star N) * (N - star N)
        = (N + star N) * N - (N + star N) * star N := by rw [mul_sub]
      _ = (N * N + star N * N) - (N * star N + star N * star N) := by
          rw [add_mul, add_mul]
      _ = star N * N - N * star N := by
          rw [h_nil, star_N_sq N h_nil, zero_add, add_zero]
      _ = -(N * star N - star N * N) := by rw [neg_sub]
  calc Gap N * J N = (Phi N * Phi N) * J N := by
        rw [Phi_sq_eq_Gap N h_nil h_reg]
    _ = Phi N * (Phi N * J N) := by rw [mul_assoc]
    _ = Phi N * (-Sigma N) := by rw [hPhiJ]
    _ = -(Phi N * Sigma N) := by rw [mul_neg]
    _ = -(-J N) := by
      have h : Phi N * Sigma N = -J N := by
        simpa [Phi, J, Sigma,
          MultiChannelAnomalyGapPoset.Phi, MultiChannelAnomalyGapPoset.J,
          MultiChannelAnomalyGapPoset.Sigma, MultiChannelAnomalyGapPoset.comm] using
          (MultiChannelAnomalyGapPoset.Phi_mul_Sigma N h_nil h_reg)
      rw [h]
    _ = J N := by rw [neg_neg]

theorem J_mul_Gap (N : B) (h_nil : N * N = 0)
    (h_reg : N * star N * N = N) : J N * Gap N = J N := by
  calc J N * Gap N = J N * (Phi N * Phi N) := by
        rw [Phi_sq_eq_Gap N h_nil h_reg]
    _ = (J N * Phi N) * Phi N := by rw [← mul_assoc]
    _ = Sigma N * Phi N := by rw [J_mul_Phi N h_nil]
    _ = J N := Sigma_mul_Phi N h_nil h_reg

theorem Gap_mul_J_orthog (N_a N_b : B)
    (h_nil_a : N_a * N_a = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    Gap N_a * J N_b = 0 := by
  have hPhiJ := Phi_mul_J_orthog N_a N_b h_ab h_ba h_asb h_sab
  have hSigJ : Sigma N_a * J N_b = 0 := by
    calc Sigma N_a * J N_b = (J N_a * Phi N_a) * J N_b := by
          rw [J_mul_Phi N_a h_nil_a]
      _ = J N_a * (Phi N_a * J N_b) := by rw [mul_assoc]
      _ = 0 := by rw [hPhiJ, mul_zero]
  dsimp [Gap]
  rw [mul_assoc, hSigJ, mul_zero]

theorem J_mul_Gap_orthog (N_a N_b : B)
    (h_nil_b : N_b * N_b = 0)
    (h_ab : N_a * N_b = 0) (h_ba : N_b * N_a = 0)
    (h_asb : N_a * star N_b = 0) (h_sab : star N_a * N_b = 0) :
    J N_a * Gap N_b = 0 := by
  have hJJ := J_mul_J_orthog N_a N_b h_ab h_ba h_asb h_sab
  have hJS : J N_a * Sigma N_b = 0 := by
    calc J N_a * Sigma N_b = J N_a * (J N_b * Phi N_b) := by
          rw [← J_mul_Phi N_b h_nil_b]
      _ = (J N_a * J N_b) * Phi N_b := by rw [← mul_assoc]
      _ = 0 := by rw [hJJ, zero_mul]
  dsimp [Gap]
  rw [← mul_assoc, hJS, zero_mul]

theorem Gap_mul_weighted_J_same (c N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N)
    (hc : c * N = N * c) (hcs : c * star N = star N * c) :
    Gap N * (c * J N) = c * J N := by
  have hcJ := comm_weight_J c N hc hcs
  calc Gap N * (c * J N) = Gap N * (J N * c) := by rw [hcJ]
    _ = (Gap N * J N) * c := by rw [← mul_assoc]
    _ = J N * c := by rw [Gap_mul_J N h_nil h_reg]
    _ = c * J N := by rw [← hcJ]

theorem weighted_gap_sum_mul_J_sum {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i)
    (h_weight_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i) :
    (∑ i ∈ s, (c i * c i) * Gap (N i)) *
      (∑ i ∈ s, c i * J (N i)) =
      ∑ i ∈ s, cube (c i) * J (N i) := by
  calc
    (∑ i ∈ s, (c i * c i) * Gap (N i)) *
        (∑ i ∈ s, c i * J (N i)) =
        ∑ i ∈ s, ((c i * c i) * Gap (N i)) * (c i * J (N i)) :=
      sum_mul_sum_of_pairwise_cross_annihilating s
        (fun i => (c i * c i) * Gap (N i)) (fun i => c i * J (N i)) (by
          intro i hi j hj hij
          obtain ⟨hij₁, hji₁, hij₂, hij₃⟩ := h_orth i hi j hj hij
          exact weighted_cross_zero (c i * c i) (Gap (N i)) (c j) (J (N j))
            (Gap_mul_J_orthog (N i) (N j) (h_nil i hi) hij₁ hji₁ hij₂ hij₃)
            (comm_weight_J (c j) (N j) (h_weight j hj) (h_weight_star j hj)))
    _ = ∑ i ∈ s, cube (c i) * J (N i) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ((c i * c i) * Gap (N i)) * (c i * J (N i)) =
            (c i * c i) * (c i * J (N i)) := by
          calc
            ((c i * c i) * Gap (N i)) * (c i * J (N i)) =
                (c i * c i) * (Gap (N i) * (c i * J (N i))) := by rw [mul_assoc]
            _ = (c i * c i) * (c i * J (N i)) := by
              rw [Gap_mul_weighted_J_same (c i) (N i) (h_nil i hi) (h_reg i hi)
                (h_weight i hi) (h_weight_star i hi)]
        _ = cube (c i) * J (N i) := by
          dsimp [cube]
          noncomm_ring

theorem J_sum_mul_weighted_gap_sum {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i)
    (h_weight_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i) :
    (∑ i ∈ s, c i * J (N i)) *
      (∑ i ∈ s, (c i * c i) * Gap (N i)) =
      ∑ i ∈ s, cube (c i) * J (N i) := by
  calc
    (∑ i ∈ s, c i * J (N i)) *
        (∑ i ∈ s, (c i * c i) * Gap (N i)) =
        ∑ i ∈ s, (c i * J (N i)) * ((c i * c i) * Gap (N i)) :=
      sum_mul_sum_of_pairwise_cross_annihilating s
        (fun i => c i * J (N i)) (fun i => (c i * c i) * Gap (N i)) (by
          intro i hi j hj hij
          obtain ⟨hij₁, hji₁, hij₂, hij₃⟩ := h_orth i hi j hj hij
          have hc2Gap := comm_square_of_comm (c j) (Gap (N j))
            (comm_weight_Gap (c j) (N j) (h_weight j hj) (h_weight_star j hj))
          exact weighted_cross_zero (c i) (J (N i)) (c j * c j) (Gap (N j))
            (J_mul_Gap_orthog (N i) (N j) (h_nil j hj) hij₁ hji₁ hij₂ hij₃)
            hc2Gap)
    _ = ∑ i ∈ s, cube (c i) * J (N i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hc2J := comm_square_of_comm (c i) (J (N i))
        (comm_weight_J (c i) (N i) (h_weight i hi) (h_weight_star i hi))
      calc
        (c i * J (N i)) * ((c i * c i) * Gap (N i)) =
            (cube (c i) * J (N i)) * Gap (N i) := by
          dsimp [cube]
          noncomm_ring [hc2J]
        _ = cube (c i) * (J (N i) * Gap (N i)) := by rw [mul_assoc]
        _ = cube (c i) * J (N i) := by
          rw [J_mul_Gap (N i) (h_nil i hi) (h_reg i hi)]

/-- The finite weighted grade-three Jordan associator scales cubically. -/
theorem weighted_JordanAssoc_Phi_Phi_J {ι : Type*}
    (s : Finset ι) (c N : ι → B)
    (h_nil : ∀ i ∈ s, N i * N i = 0)
    (h_reg : ∀ i ∈ s, N i * star (N i) * N i = N i)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      N i * N j = 0 ∧ N j * N i = 0 ∧
        N i * star (N j) = 0 ∧ star (N i) * N j = 0)
    (h_weight : ∀ i ∈ s, c i * N i = N i * c i)
    (h_weight_star : ∀ i ∈ s, c i * star (N i) = star (N i) * c i) :
    JordanAssoc (∑ i ∈ s, c i * Phi (N i))
      (∑ i ∈ s, c i * Phi (N i)) (∑ i ∈ s, c i * J (N i)) =
      quad (∑ i ∈ s, cube (c i) * J (N i)) := by
  let A := ∑ i ∈ s, c i * Phi (N i)
  let K := ∑ i ∈ s, c i * J (N i)
  let T := ∑ i ∈ s, (c i * c i) * Gap (N i)
  let C := ∑ i ∈ s, cube (c i) * J (N i)
  have hAA : A * A = T := by
    dsimp [A, T]
    exact weighted_Phi_sum_sq_eq_weighted_Gap s c N h_nil h_reg h_orth
      h_weight h_weight_star
  have hAK : MultiChannelAnomalyGapPoset.anticomm A K = 0 := by
    dsimp [A, K]
    exact weighted_chiral_sum_anticomm s c N h_nil h_orth h_weight h_weight_star
  have hAK' : A * K + K * A = 0 := hAK
  have hTK : T * K = C := by
    dsimp [T, K, C]
    exact weighted_gap_sum_mul_J_sum s c N h_nil h_reg h_orth h_weight h_weight_star
  have hKT : K * T = C := by
    dsimp [T, K, C]
    exact J_sum_mul_weighted_gap_sum s c N h_nil h_reg h_orth h_weight h_weight_star
  dsimp [JordanAssoc]
  change (A * A + A * A) * K + K * (A * A + A * A) -
      (A * (A * K + K * A) + (A * K + K * A) * A) =
      (C + C) + (C + C)
  rw [hAA, hAK']
  simp only [mul_zero, zero_mul, add_zero, sub_zero]
  calc (T + T) * K + K * (T + T) =
      (T * K + T * K) + (K * T + K * T) := by rw [add_mul, mul_add]
    _ = (C + C) + (C + C) := by rw [hTK, hKT]

end InfoGeometry.OperatorAlgebra.PeirceSpine.WeightedMultiChannelGapPoset
