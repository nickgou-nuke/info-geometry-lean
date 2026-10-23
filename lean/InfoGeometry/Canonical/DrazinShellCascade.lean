/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.DrazinObliqueShellResolution

/-!
# One-step cascade of oblique Drazin shells

This module consumes the existing Drazin and powerwise Moore-Penrose owners.
It strengthens extinction/recovery into a strictly lower-shell right action,
a faithful leading step, and the corresponding decomposition of the operator.
The shells need not be self-adjoint, nonzero, or commuting with the operator.
-/
namespace InfoGeometry.Canonical.DrazinShellCascade

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinObliqueShellResolution
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MoorePenrosePowerShells
open scoped BigOperators

variable {R : Type*} [Ring R] [StarRing R]
variable {a d : R} {k : ℕ} {g : ℕ → R}
local notation "F" => complementaryProjection a d
local notation "E" => projection a d
local notation "S" => dressedShell a d g
local notation "H" => dressedRange a d g

theorem shell_right_complement (hD : IsDrazinInverse a d k) (m : ℕ) :
    S m * F = S m := by
  unfold dressedShell
  simp only [mul_assoc, complementaryProjection_is_idempotent hD]

theorem shell_step_right_complement (hD : IsDrazinInverse a d k) (m : ℕ) :
    (S m * a) * F = S m * a := by
  rw [mul_assoc, ← complementaryProjection_comm_self hD, ← mul_assoc,
    shell_right_complement hD]

/-- The finite partial sum is the complement of the remaining filtration. -/
theorem shell_partial_sum (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) (m : ℕ) :
    (∑ r ∈ Finset.range m, S r) = F - H m := by
  simp_rw [dressedShell_eq_sub]
  rw [telescope, dressedRange_zero hD hg]

/-- Multiplication by a dressed support is a power followed by recovery. -/
theorem supported_mul_range (hD : IsDrazinInverse a d k)
    {x : R} (hx : x * F = x) (m : ℕ) :
    x * H m = (x * a ^ m) * (g m * F) := by
  calc
    x * H m = (x * (F * nilpotent a d ^ m)) * (g m * F) := by
      unfold dressedRange
      simp only [mul_assoc]
    _ = (x * (F * a ^ m)) * (g m * F) := by
      rw [← complement_mul_pow_eq hD]
    _ = (x * a ^ m) * (g m * F) := by
      rw [← mul_assoc x F (a ^ m), hx]

theorem shell_step_range_zero (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) (m : ℕ) :
    (S m * a) * H m = 0 := by
  rw [supported_mul_range hD (shell_step_right_complement hD m),
    mul_assoc (S m) a (a ^ m), ← pow_succ',
    dressedShell_mul_pow_succ hD hg, zero_mul]

/-- Right action strictly lowers shell index; the case zero is extinction. -/
theorem shell_step_eq_lower (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) (m : ℕ) :
    S m * a = (S m * a) * (∑ r ∈ Finset.range m, S r) := by
  rw [shell_partial_sum hD hg, mul_sub, shell_step_right_complement hD,
    shell_step_range_zero hD hg, sub_zero]

theorem shell_mul_power_zero (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m))
    {m r : ℕ} (hr : m + 1 ≤ r) : S m * a ^ r = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [pow_add, ← mul_assoc, dressedShell_mul_pow_succ hD hg, zero_mul]

theorem lower_sum_mul_power_zero (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) (m : ℕ) :
    (∑ r ∈ Finset.range m, S r) * a ^ m = 0 := by
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro r hr
  exact shell_mul_power_zero hD hg (Nat.succ_le_of_lt (Finset.mem_range.mp hr))

/-- Only the leading block survives the next `m` right-action steps. -/
theorem leading_step_power (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) (m : ℕ) :
    (S (m + 1) * a) * a ^ m = ((S (m + 1) * a) * S m) * a ^ m := by
  calc
    (S (m + 1) * a) * a ^ m =
        ((S (m + 1) * a) * (∑ r ∈ Finset.range (m + 1), S r)) * a ^ m := by
      rw [← shell_step_eq_lower hD hg (m + 1)]
    _ = ((S (m + 1) * a) * S m) * a ^ m := by
      rw [Finset.sum_range_succ, mul_add, add_mul,
        mul_assoc (S (m + 1) * a) (∑ r ∈ Finset.range m, S r) (a ^ m),
        lower_sum_mul_power_zero hD hg, mul_zero, zero_add]

/-- A nonzero shell component cannot lose its leading step. No shell is assumed inhabited. -/
theorem leading_step_faithful (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) (m : ℕ) (x : R) :
    x * S (m + 1) * a * S m = 0 ↔ x * S (m + 1) = 0 := by
  constructor
  · intro hx
    apply (dressedShell_survives_iff hD hg (m + 1) x).mp
    calc
      x * S (m + 1) * a ^ (m + 1) = x * ((S (m + 1) * a) * a ^ m) := by
        rw [pow_succ']
        simp only [mul_assoc]
      _ = x * (((S (m + 1) * a) * S m) * a ^ m) := by
        rw [leading_step_power hD hg]
      _ = (x * S (m + 1) * a * S m) * a ^ m := by simp only [mul_assoc]
      _ = 0 := by rw [hx, zero_mul]
  · intro hx
    rw [hx, zero_mul, zero_mul]

/-- All blocks on or above the shell diagonal vanish. -/
theorem shell_step_block_zero (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m))
    {m r : ℕ} (hmr : m ≤ r) : S m * a * S r = 0 := by
  calc
    S m * a * S r = ((S m * a) * (∑ t ∈ Finset.range m, S t)) * S r := by
      rw [← shell_step_eq_lower hD hg]
    _ = (S m * a) * (∑ t ∈ Finset.range m, S t * S r) := by
      rw [mul_assoc, Finset.sum_mul]
    _ = 0 := by
      have hz : (∑ t ∈ Finset.range m, S t * S r) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        apply dressedShell_mul_eq_zero hD hg
        have htm := Finset.mem_range.mp ht
        omega
      rw [hz, mul_zero]

/-- Operator identity, not a claim that the shells are eigenspaces. -/
theorem operator_cascade (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) :
    a = E * a + ∑ m ∈ Finset.range k,
      (S m * a) * (∑ r ∈ Finset.range m, S r) := by
  simp_rw [← shell_step_eq_lower hD hg]
  rw [← Finset.sum_mul, dressedShell_sum hD hg, ← add_mul,
    projection_add_complementaryProjection, one_mul]

/-- Powers are invertible on the regular projector, including power zero. -/
theorem core_power_recovery (hD : IsDrazinInverse a d k) (r : ℕ) :
    (E * a ^ r) * d ^ r = E := by
  have hc : Commute a d := hD.comm
  calc
    (E * a ^ r) * d ^ r = E * (a ^ r * d ^ r) := mul_assoc _ _ _
    _ = E * E ^ r := by rw [← hc.mul_pow r]; rfl
    _ = E ^ (r + 1) := (pow_succ' E r).symm
    _ = E := InfoGeometry.Singular.Drazin.pow_succ_eq_of_idempotent
      (projection_is_idempotent hD) r

theorem core_inverse_power_recovery (hD : IsDrazinInverse a d k) (r : ℕ) :
    (E * d ^ r) * a ^ r = E := by
  have hc : Commute a d := hD.comm
  rw [mul_assoc, ← ((hc.pow_left r).pow_right r).eq, ← mul_assoc]
  exact core_power_recovery hD r

/-- Summary of the regular recovery and strictly lowering nilpotent action. -/
theorem operator_core_isomorphism_and_shell_cascade (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) :
    (∀ r, (E * a ^ r) * d ^ r = E) ∧
    (∀ m, S m * a = (S m * a) * (∑ r ∈ Finset.range m, S r)) ∧
    (∀ m x, x * S (m + 1) * a * S m = 0 ↔ x * S (m + 1) = 0) :=
  ⟨core_power_recovery hD, shell_step_eq_lower hD hg, leading_step_faithful hD hg⟩

end InfoGeometry.Canonical.DrazinShellCascade
