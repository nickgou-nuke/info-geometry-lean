/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Singular.MoorePenroseShellDynamics

/-!
# Oblique Drazin shell resolution

Let `F = 1 - a*d` and `N = a*F`. The existing power range shells `Q_m`
produce `F*Q_m*F`, a complete family of mutually annihilating idempotents
inside the Drazin complement, including witness exponent zero.

Extinction is for right multiplication by `a`, hence for row states.
Self-adjointness is an additional conclusion when `F` is self-adjoint.
The shell projections are not asserted to commute with `a`.
-/

namespace InfoGeometry.Canonical.DrazinObliqueShellResolution

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MoorePenrosePowerShells
open InfoGeometry.Singular.MoorePenroseShellDynamics
open scoped BigOperators

variable {R : Type*} [Ring R] [StarRing R]

/-- The range-support filtration compressed into the Drazin complement. -/
def dressedRange (a d : R) (g : ℕ → R) (m : ℕ) : R :=
  complementaryProjection a d * (nilpotent a d ^ m * g m) * complementaryProjection a d

/-- Two-sided compression, rather than an unsupported one-sided refinement. -/
def dressedShell (a d : R) (g : ℕ → R) (m : ℕ) : R :=
  complementaryProjection a d * rangeShell (nilpotent a d) g m * complementaryProjection a d

variable {a d : R} {k : ℕ} {g : ℕ → R}
local notation "F" => complementaryProjection a d
local notation "N" => nilpotent a d

theorem complement_mul_nilpotent (hD : IsDrazinInverse a d k) : F * N = N := by
  rw [nilpotent_eq_mul_complementaryProjection, ← mul_assoc,
    complementaryProjection_comm_self hD, mul_assoc,
    complementaryProjection_is_idempotent hD]

theorem complement_mul_nilpotent_pow_succ (hD : IsDrazinInverse a d k) (m : ℕ) :
    F * N ^ (m + 1) = N ^ (m + 1) := by
  rw [pow_succ', ← mul_assoc, complement_mul_nilpotent hD]

/-- This identity is valid also at exponent zero. -/
theorem complement_mul_nilpotent_pow (hD : IsDrazinInverse a d k) (m : ℕ) :
    F * N ^ m = a ^ m * F := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      F * N ^ (m + 1) = (F * N) * N ^ m := by rw [pow_succ', mul_assoc]
      _ = N * N ^ m := by rw [complement_mul_nilpotent hD]
      _ = a * (F * N ^ m) := by rw [nilpotent_eq_mul_complementaryProjection, mul_assoc]
      _ = a * (a ^ m * F) := by rw [ih]
      _ = a ^ (m + 1) * F := by rw [pow_succ', mul_assoc]

theorem complement_mul_pow_eq (hD : IsDrazinInverse a d k) (m : ℕ) :
    F * a ^ m = F * N ^ m := by
  have hc : Commute F a := complementaryProjection_comm_self hD
  rw [complement_mul_nilpotent_pow hD]
  exact (hc.pow_right m).eq

theorem complement_mul_pow_succ (hD : IsDrazinInverse a d k) (m : ℕ) :
    F * a ^ (m + 1) = N ^ (m + 1) := by
  rw [complement_mul_pow_eq hD, complement_mul_nilpotent_pow_succ hD]

theorem complement_mul_nilpotent_pow_index (hD : IsDrazinInverse a d k) :
    F * N ^ k = 0 := by
  rw [complement_mul_nilpotent_pow hD]
  exact power_mul_complementaryProjection_eq_zero hD

theorem complement_mul_rangeSupport_succ (hD : IsDrazinInverse a d k)
    (g : ℕ → R) (m : ℕ) :
    F * (N ^ (m + 1) * g (m + 1)) = N ^ (m + 1) * g (m + 1) := by
  rw [← mul_assoc, complement_mul_nilpotent_pow_succ hD]

theorem dressedRange_zero (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) : dressedRange a d g 0 = F := by
  have hg0 : g 0 = 1 := by simpa using (hg 0).aba_eq_a
  simp only [dressedRange, pow_zero, hg0, one_mul, mul_one,
    complementaryProjection_is_idempotent hD]

theorem dressedRange_eq_right_mul (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) (m : ℕ) :
    dressedRange a d g m = (N ^ m * g m) * F := by
  cases m with
  | zero =>
    have hg0 : g 0 = 1 := by simpa using (hg 0).aba_eq_a
    rw [dressedRange_zero hD hg]
    simp [hg0]
  | succ m =>
    unfold dressedRange
    rw [complement_mul_rangeSupport_succ hD]

/-- Nested absorption survives compression by an oblique complement. -/
theorem dressedRange_mul_max (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) (i j : ℕ) :
    dressedRange a d g i * dressedRange a d g j = dressedRange a d g (max i j) := by
  cases j with
  | zero =>
    rw [max_zero, dressedRange_zero hD hg]
    unfold dressedRange
    simp only [mul_assoc, complementaryProjection_is_idempotent hD]
  | succ j =>
    simp only [dressedRange_eq_right_mul hD hg]
    calc
      ((N ^ i * g i) * F) * ((N ^ (j + 1) * g (j + 1)) * F) =
          (N ^ i * g i) * (F * (N ^ (j + 1) * g (j + 1))) * F := by
            simp only [mul_assoc]
      _ = (N ^ i * g i) * (N ^ (j + 1) * g (j + 1)) * F := by
        rw [complement_mul_rangeSupport_succ hD]
      _ = (N ^ max i (j + 1) * g (max i (j + 1))) * F := by
        rw [rangeSupport_mul_max N g hg]

theorem dressedShell_eq_sub (a d : R) (g : ℕ → R) (m : ℕ) :
    dressedShell a d g m = dressedRange a d g m - dressedRange a d g (m + 1) := by
  unfold dressedShell dressedRange rangeShell
  noncomm_ring

theorem dressedShell_eq_right_mul (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) (m : ℕ) :
    dressedShell a d g m = rangeShell N g m * F := by
  rw [dressedShell_eq_sub, dressedRange_eq_right_mul hD hg,
    dressedRange_eq_right_mul hD hg]
  exact (sub_mul _ _ _).symm

theorem dressedShell_idempotent (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) (m : ℕ) :
    IsIdempotentElem (dressedShell a d g m) := by
  change dressedShell a d g m * dressedShell a d g m = dressedShell a d g m
  simp only [dressedShell_eq_sub, sub_mul, mul_sub, dressedRange_mul_max hD hg,
    max_self, max_eq_right (Nat.le_succ m), max_eq_left (Nat.le_succ m)]
  abel

/-- Orthogonality here means zero products; it does not assert self-adjointness. -/
theorem dressedShell_mul_eq_zero (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) {i j : ℕ} (hij : i ≠ j) :
    dressedShell a d g i * dressedShell a d g j = 0 := by
  simp only [dressedShell_eq_sub, sub_mul, mul_sub, dressedRange_mul_max hD hg]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [max_eq_right (by omega : i ≤ j), max_eq_right (by omega : i ≤ j + 1),
      max_eq_right (by omega : i + 1 ≤ j), max_eq_right (by omega : i + 1 ≤ j + 1)]
    abel
  · rw [max_eq_left (by omega : j ≤ i), max_eq_left (by omega : j + 1 ≤ i),
      max_eq_left (by omega : j ≤ i + 1), max_eq_left (by omega : j + 1 ≤ i + 1)]
    abel

theorem core_shell_mul_eq_zero (hD : IsDrazinInverse a d k) (g : ℕ → R) (m : ℕ) :
    projection a d * dressedShell a d g m = 0 ∧
    dressedShell a d g m * projection a d = 0 := by
  constructor
  · unfold dressedShell
    rw [← mul_assoc, ← mul_assoc, projection_mul_complementaryProjection hD,
      zero_mul, zero_mul]
  · unfold dressedShell
    rw [mul_assoc, complementaryProjection_mul_projection hD, mul_zero]

/-- The sum is the actual oblique complement, even at witness exponent zero. -/
theorem dressedShell_sum (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) :
    (∑ m ∈ Finset.range k, dressedShell a d g m) = F := by
  simp_rw [dressedShell_eq_sub]
  rw [telescope, dressedRange_zero hD hg]
  have hk : dressedRange a d g k = 0 := by
    unfold dressedRange
    rw [← mul_assoc F (N ^ k) (g k), complement_mul_nilpotent_pow_index hD,
      zero_mul, zero_mul]
  rw [hk, sub_zero]

theorem core_add_dressedShell_sum (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) :
    projection a d + (∑ m ∈ Finset.range k, dressedShell a d g m) = 1 := by
  rw [dressedShell_sum hD hg, projection_add_complementaryProjection]

/-- Extinction on the full operator is a right-action statement. -/
theorem dressedShell_mul_pow_succ (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) (m : ℕ) :
    dressedShell a d g m * a ^ (m + 1) = 0 := by
  rw [dressedShell_eq_right_mul hD hg, mul_assoc, complement_mul_pow_succ hD]
  exact rangeShell_mul_pow_eq_zero N g hg (le_refl (m + 1))

/-- Recovery at step `m`, including `m = 0`, without dividing by the shell. -/
theorem dressedShell_recovery (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) (m : ℕ) :
    (dressedShell a d g m * a ^ m) * (g m * F) = dressedShell a d g m := by
  have hmid : F * a ^ m = F * (F * N ^ m) := by
    rw [← mul_assoc F F (N ^ m), complementaryProjection_is_idempotent hD,
      complement_mul_pow_eq hD]
  calc
    (dressedShell a d g m * a ^ m) * (g m * F) =
        dressedShell a d g m * dressedRange a d g m := by
      unfold dressedShell dressedRange
      calc
        ((F * rangeShell N g m * F) * a ^ m) * (g m * F) =
            F * rangeShell N g m * (F * a ^ m) * g m * F := by
              simp only [mul_assoc]
        _ = (F * rangeShell N g m * F) * (F * (N ^ m * g m) * F) := by
          rw [hmid]
          simp only [mul_assoc]
    _ = dressedShell a d g m := by
      rw [dressedShell_eq_sub, sub_mul, dressedRange_mul_max hD hg,
        dressedRange_mul_max hD hg, max_self, max_eq_left (Nat.le_succ m)]

theorem dressedShell_survives_iff (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) (m : ℕ) (x : R) :
    x * dressedShell a d g m * a ^ m = 0 ↔ x * dressedShell a d g m = 0 := by
  constructor
  · intro hx
    calc
      x * dressedShell a d g m = (x * dressedShell a d g m * a ^ m) * (g m * F) := by
        rw [mul_assoc x _ (a ^ m), mul_assoc x _ (g m * F), dressedShell_recovery hD hg]
      _ = 0 := by rw [hx, zero_mul]
  · intro hx
    rw [hx, zero_mul]

theorem dressedShell_exact_extinction (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m)) {m : ℕ} {x : R}
    (hx : x * dressedShell a d g m ≠ 0) (r : ℕ) :
    x * dressedShell a d g m * a ^ r = 0 ↔ m < r :=
  right_extinction_iff a (dressedShell_mul_pow_succ hD hg m)
    (dressedShell_recovery hD hg m) hx r

/-- Self-adjointness is sufficient to upgrade the oblique shell to a star projection. -/
theorem dressedShell_isStarProjection (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (N ^ m) (g m))
    (hF : IsSelfAdjoint F) (m : ℕ) : IsStarProjection (dressedShell a d g m) := by
  refine ⟨dressedShell_idempotent hD hg m, ?_⟩
  change star (F * rangeShell N g m * F) = F * rangeShell N g m * F
  simp only [star_mul, hF.star_eq,
    (rangeShell_isStarProjection N g hg m).isSelfAdjoint.star_eq, mul_assoc]

end InfoGeometry.Canonical.DrazinObliqueShellResolution
