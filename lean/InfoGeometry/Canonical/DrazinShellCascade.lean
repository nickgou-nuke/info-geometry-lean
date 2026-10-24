/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.DrazinNilpotentShellResolution
import InfoGeometry.Canonical.DrazinObliqueShellResolution

/-!
# Drazin shell cascade

Given a Drazin inverse `d` of index `k` for `a`, the dressed shell projectors
`S m = E_N * Q_m * E_N` satisfy the strictly triangular cascade law

`S m * a * S r = 0` whenever `m ≤ r`.

Consequently the operator splits as

`a = E_C * a * E_C + Σ m, S m * a * (Σ r < m, S r)`.

This is the generic, noncommutative, non-diagonalizable form of the
`drazinShellProj_succ_mul_A_maps_into_earlier_shells` claim.  The shells are
indexed by the range filtration of the nilpotent part; `S 0` is the
kernel-side shell and the cascade runs from higher indices to lower indices.
The theorem is an algebraic identity.  It does not assert that a shell is
nonzero or that `k` is minimal.
-/

namespace InfoGeometry.Canonical.DrazinNilpotentShell

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.MoorePenrose

variable {R : Type*} [Ring R] [StarRing R]

section RawShell

variable {N : R} {M : ℕ → R}

/-- The nilpotent part acts on the `r`-th raw shell as a difference of two
range projections. -/
lemma nilpotent_mul_shellProj (N : R) (M : ℕ → R) (r : ℕ) :
    N * shellProj N M r =
      N ^ (r + 1) * M r - N ^ (r + 2) * M (r + 1) := by
  unfold shellProj rangeProj
  rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', ← pow_succ']

/-- A shell can only act on strictly earlier shells: `Q_m * N * Q_r = 0` for
`m ≤ r`. -/
theorem shellProj_mul_nilpotent_mul_shellProj_eq_zero
    (hM : PowerMPFamily N M) {m r : ℕ} (hmr : m ≤ r) :
    shellProj N M m * N * shellProj N M r = 0 := by
  rw [mul_assoc (shellProj N M m) N (shellProj N M r),
    nilpotent_mul_shellProj]
  rw [mul_sub, ← mul_assoc, ← mul_assoc]
  rw [shellProj_mul_pow_eq_zero hM (Nat.add_le_add_right hmr 1),
    shellProj_mul_pow_eq_zero hM (Nat.le_succ_of_le (Nat.add_le_add_right hmr 1))]
  simp

end RawShell

section Drazin

variable {a d : R} {k : ℕ}

/-- The regular projector annihilates the nilpotent side after multiplication
by `a`. -/
theorem projection_mul_a_mul_complementaryProjection_eq_zero
    (h : IsDrazinInverse a d k) :
    projection a d * a * complementaryProjection a d = 0 := by
  rw [projection_comm_self h, mul_assoc,
    projection_mul_complementaryProjection h, mul_zero]

/-- The nilpotent side annihilates the regular projector after multiplication
by `a`. -/
theorem complementaryProjection_mul_a_mul_projection_eq_zero
    (h : IsDrazinInverse a d k) :
    complementaryProjection a d * a * projection a d = 0 := by
  rw [complementaryProjection_comm_self h, mul_assoc,
    complementaryProjection_mul_projection h, mul_zero]

/-- Dressed shell cascade: `S_m * a * S_r = 0` for `m ≤ r`. -/
theorem drazinShellProj_mul_a_mul_drazinShellProj_eq_zero_of_le
    (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    {m r : ℕ} (hmr : m ≤ r) :
    drazinShellProj a d M m * a * drazinShellProj a d M r = 0 := by
  have ha : a = projection a d * a + fittingNilpotentPart a d := by
    calc
      a = fittingRegularPart a d + fittingNilpotentPart a d :=
            (fittingRegularPart_add_fittingNilpotentPart_eq_self
              (a := a) (b := d)).symm
      _ = a * projection a d + fittingNilpotentPart a d := by
            unfold fittingRegularPart
            rfl
      _ = projection a d * a + fittingNilpotentPart a d := by
            rw [← projection_comm_self h]
  have hP : drazinShellProj a d M m * (projection a d * a) *
      drazinShellProj a d M r = 0 := by
    rw [drazinShellProj_eq_right_mul h hM m]
    calc
      (shellProj (fittingNilpotentPart a d) M m *
          complementaryProjection a d) * (projection a d * a) *
          drazinShellProj a d M r
          = shellProj (fittingNilpotentPart a d) M m *
              (complementaryProjection a d * projection a d) * a *
              drazinShellProj a d M r := by noncomm_ring
      _ = 0 := by
            rw [complementaryProjection_mul_projection h]
            simp
  have hN : drazinShellProj a d M m * fittingNilpotentPart a d *
      drazinShellProj a d M r = 0 := by
    rw [drazinShellProj_eq_right_mul h hM m,
      drazinShellProj_eq_right_mul h hM r]
    calc
      (shellProj (fittingNilpotentPart a d) M m *
          complementaryProjection a d) * fittingNilpotentPart a d *
          (shellProj (fittingNilpotentPart a d) M r *
            complementaryProjection a d)
          = (shellProj (fittingNilpotentPart a d) M m *
              fittingNilpotentPart a d *
              shellProj (fittingNilpotentPart a d) M r) *
              complementaryProjection a d := by
            rw [mul_assoc (shellProj (fittingNilpotentPart a d) M m)
                  (complementaryProjection a d) (fittingNilpotentPart a d),
              complementaryProjection_mul_fittingNilpotentPart h]
            noncomm_ring
      _ = 0 := by
            rw [shellProj_mul_nilpotent_mul_shellProj_eq_zero hM hmr,
              zero_mul]
  conv_lhs =>
    arg 1
    arg 2
    rw [ha]
  rw [mul_add, add_mul, hP, hN, add_zero]

/-- The exact core + shell cascade expansion.  The core term is the regular
part; the shells act strictly triangularly. -/
theorem drazin_core_and_shell_cascade
    (h : IsDrazinInverse a d k) {M : ℕ → R}
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    a = projection a d * a * projection a d +
        ∑ m ∈ Finset.range k,
          drazinShellProj a d M m * a *
            (∑ r ∈ Finset.range m, drazinShellProj a d M r) := by
  have hT : projection a d +
      (∑ m ∈ Finset.range k, drazinShellProj a d M m) = 1 :=
    projection_add_sum_drazinShellProj h hM
  have hET : projection a d * a *
      (∑ m ∈ Finset.range k, drazinShellProj a d M m) = 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro m _
    unfold drazinShellProj
    calc
      projection a d * a *
          (complementaryProjection a d *
            shellProj (fittingNilpotentPart a d) M m *
            complementaryProjection a d)
          = projection a d * a * complementaryProjection a d *
              shellProj (fittingNilpotentPart a d) M m *
              complementaryProjection a d := by noncomm_ring
      _ = 0 := by
            rw [projection_mul_a_mul_complementaryProjection_eq_zero h,
              zero_mul, zero_mul]
  have hTE : (∑ m ∈ Finset.range k, drazinShellProj a d M m) * a *
      projection a d = 0 := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro m _
    unfold drazinShellProj
    calc
      (complementaryProjection a d *
          shellProj (fittingNilpotentPart a d) M m *
          complementaryProjection a d) * a * projection a d
          = complementaryProjection a d *
              shellProj (fittingNilpotentPart a d) M m *
              (complementaryProjection a d * a * projection a d) := by
            noncomm_ring
      _ = 0 := by
            rw [complementaryProjection_mul_a_mul_projection_eq_zero h,
              mul_zero]
  have hTT : (∑ m ∈ Finset.range k, drazinShellProj a d M m) * a *
      (∑ r ∈ Finset.range k, drazinShellProj a d M r) =
      ∑ m ∈ Finset.range k,
        drazinShellProj a d M m * a *
          (∑ r ∈ Finset.range m, drazinShellProj a d M r) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    have hsub : Finset.range m ⊆ Finset.range k := by
      intro r hr
      exact Finset.mem_range.mpr
        (lt_trans (Finset.mem_range.mp hr) (Finset.mem_range.mp hm))
    have hzero : ∀ r ∈ Finset.range k, r ∉ Finset.range m →
        (drazinShellProj a d M m * a) * drazinShellProj a d M r = 0 := by
      intro r _ hrm
      have hrm' : ¬ r < m := by simpa [Finset.mem_range] using hrm
      have hmr : m ≤ r := le_of_not_gt hrm'
      exact drazinShellProj_mul_a_mul_drazinShellProj_eq_zero_of_le h hM hmr
    calc
      (drazinShellProj a d M m * a) *
          (∑ r ∈ Finset.range k, drazinShellProj a d M r)
          = ∑ r ∈ Finset.range k,
              (drazinShellProj a d M m * a) *
                drazinShellProj a d M r := by
            rw [Finset.mul_sum]
      _ = ∑ r ∈ Finset.range m,
              (drazinShellProj a d M m * a) *
                drazinShellProj a d M r := by
            symm
            exact Finset.sum_subset hsub hzero
      _ = (drazinShellProj a d M m * a) *
              (∑ r ∈ Finset.range m, drazinShellProj a d M r) := by
            rw [Finset.mul_sum]
  calc
    a = (projection a d +
        (∑ m ∈ Finset.range k, drazinShellProj a d M m)) * a *
        (projection a d +
          (∑ r ∈ Finset.range k, drazinShellProj a d M r)) := by
          rw [hT, one_mul, mul_one]
    _ = projection a d * a * projection a d +
          projection a d * a *
            (∑ r ∈ Finset.range k, drazinShellProj a d M r) +
          (∑ m ∈ Finset.range k, drazinShellProj a d M m) * a *
            projection a d +
          (∑ m ∈ Finset.range k, drazinShellProj a d M m) * a *
            (∑ r ∈ Finset.range k, drazinShellProj a d M r) := by
          rw [add_mul, add_mul, mul_add, mul_add]
          abel
    _ = projection a d * a * projection a d +
          (∑ m ∈ Finset.range k, drazinShellProj a d M m) * a *
            (∑ r ∈ Finset.range k, drazinShellProj a d M r) := by
          rw [hET, hTE]
          abel
    _ = projection a d * a * projection a d +
          ∑ m ∈ Finset.range k,
            drazinShellProj a d M m * a *
              (∑ r ∈ Finset.range m, drazinShellProj a d M r) := by
          rw [hTT]

end Drazin

end InfoGeometry.Canonical.DrazinNilpotentShell

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
        exact ne_of_lt (lt_of_lt_of_le (Finset.mem_range.mp ht) hmr)
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
