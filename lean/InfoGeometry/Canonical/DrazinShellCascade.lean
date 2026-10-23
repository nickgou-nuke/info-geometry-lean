/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.DrazinNilpotentShellResolution

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
  rw [shellProj_mul_pow_eq_zero hM (by omega : m + 1 ≤ r + 1),
    shellProj_mul_pow_eq_zero hM (by omega : m + 1 ≤ r + 2)]
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
