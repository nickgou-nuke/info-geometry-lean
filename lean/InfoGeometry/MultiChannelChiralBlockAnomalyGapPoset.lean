/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic

namespace OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 0. Universal Additive Rearrangement Helpers
-/

private theorem neg_sub_eq_neg_add (a b : B) : -a - b = -(a + b) := by
  rw [sub_eq_add_neg, ← neg_add_rev, add_comm b a]

private theorem add_add_add_comm' (a b c d : B) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc (a + b) + (c + d)
    _ = a + (b + (c + d)) := by rw [add_assoc a b (c + d)]
    _ = a + ((b + c) + d) := by rw [← add_assoc b c d]
    _ = a + ((c + b) + d) := by rw [add_comm b c]
    _ = a + (c + (b + d)) := by rw [add_assoc c b d]
    _ = (a + c) + (b + d) := by rw [← add_assoc a c (b + d)]

private theorem sub_add_sub_comm' (a b c d : B) :
    (a - b) + (c - d) = (a + c) - (b + d) := by
  calc (a - b) + (c - d)
    _ = (a + -b) + (c + -d) := by rw [sub_eq_add_neg, sub_eq_add_neg]
    _ = (a + c) + (-b + -d) := by rw [add_add_add_comm']
    _ = (a + c) + -(d + b) := by rw [← neg_add_rev]
    _ = (a + c) + -(b + d) := by rw [add_comm d b]
    _ = (a + c) - (b + d) := by rw [← sub_eq_add_neg]

/-!
### 1. Single-Channel Anomaly-First Foundation (`MC₁`)
-/

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

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

theorem Phi_mul_Sigma (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Phi N * Sigma N = -J N := by
  have hN : N * Sigma N = -N := by
    dsimp [Sigma, comm]
    rw [mul_sub, ← mul_assoc N N (star N), h_nil, zero_mul,
      ← mul_assoc N (star N) N, h_reg, zero_sub]
  have hsN : star N * Sigma N = star N := by
    dsimp [Sigma, comm]
    rw [mul_sub, ← mul_assoc (star N) N (star N),
      star_N_reg N h_reg, ← mul_assoc (star N) (star N) N,
      star_N_sq N h_nil, zero_mul, sub_zero]
  dsimp [Phi, J]
  rw [add_mul, hN, hsN, add_comm (-N) (star N), ← sub_eq_add_neg, neg_sub]

theorem J_mul_Sigma (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    J N * Sigma N = -Phi N := by
  have hN : N * Sigma N = -N := by
    dsimp [Sigma, comm]
    rw [mul_sub, ← mul_assoc N N (star N), h_nil, zero_mul,
      ← mul_assoc N (star N) N, h_reg, zero_sub]
  have hsN : star N * Sigma N = star N := by
    dsimp [Sigma, comm]
    rw [mul_sub, ← mul_assoc (star N) N (star N),
      star_N_reg N h_reg, ← mul_assoc (star N) (star N) N,
      star_N_sq N h_nil, zero_mul, sub_zero]
  dsimp [J, Phi]
  rw [sub_mul, hN, hsN, neg_sub_eq_neg_add]

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

theorem Phi_mul_Gap (N : B)
    (h_nil : N * N = 0) (h_reg : N * star N * N = N) :
    Phi N * Gap N = Phi N := by
  dsimp [Gap]
  rw [← mul_assoc, Phi_mul_Sigma N h_nil h_reg, neg_mul,
      J_mul_Sigma N h_nil h_reg, neg_neg]

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
  change Gap N * (Sigma N * Sigma N) = Gap N
  rw [← mul_assoc, Gap_mul_Sigma N h_nil h_reg]
  rfl

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

end OperatorAlgebra.PeirceSpine.MultiChannelAnomalyGapPoset
