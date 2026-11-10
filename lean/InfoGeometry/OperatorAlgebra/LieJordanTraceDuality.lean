/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.LieJordanDuality
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Bilinear trace duality and the distinct star-trace adjoints

`trace(X * Y)` is used only as a bilinear form. The star-trace formulas are
stated separately. No BKM metric, statistical manifold or Levi-Civita
connection is asserted by these finite operator identities.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LieJordanTraceDuality

open Matrix LieJordanDuality
open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingTraceDuality

variable {B M : Type*} [Ring B] [AddCommGroup M]

/-- Cyclic movement of the leading factor in any non-commutative ring `[Ring B]`
equipped with a cyclic additive trace `τ : B →+ M`. -/
theorem trace_cycle3_ring (τ : B →+ M) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (A C D : B) :
    τ (A * C * D) = τ (C * (D * A)) := by
  calc
    τ (A * C * D) = τ (A * (C * D)) := by rw [mul_assoc]
    _ = τ ((C * D) * A) := h_cyc A (C * D)
    _ = τ (C * (D * A)) := by rw [mul_assoc]

/-- Skew-transposition of the inner commutator derivation `X ↦ H * X - X * H`
for any cyclic additive trace `τ : B →+ M` on a non-commutative ring `[Ring B]`. -/
theorem trace_ad_skew_ring (τ : B →+ M) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (H X Y : B) :
    τ ((H * X - X * H) * Y) + τ (X * (H * Y - Y * H)) = 0 := by
  rw [sub_mul, mul_sub, map_sub, map_sub,
    trace_cycle3_ring τ h_cyc H X Y, mul_assoc X H Y]
  abel

/-- Symmetry of the Jordan anticommutator `X ↦ S * X + X * S` for any cyclic
additive trace `τ : B →+ M` on a non-commutative ring `[Ring B]`. -/
theorem trace_jordan_symmetric_ring (τ : B →+ M) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (S X Y : B) :
    τ ((S * X + X * S) * Y) = τ (X * (S * Y + Y * S)) := by
  rw [add_mul, mul_add, map_add, map_add,
    trace_cycle3_ring τ h_cyc S X Y, mul_assoc X S Y]
  abel

/-- Exact Lie–Jordan trace duality for the dual superoperators over any
non-commutative ring `[Ring B]` equipped with a cyclic additive trace `τ : B →+ M`. -/
theorem trace_dual_balance_ring (τ : B →+ M) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (H S X Y : B) :
    τ (((H * X - X * H) + (S * X + X * S)) * Y) +
      τ (X * ((H * Y - Y * H) - (S * Y + Y * S))) = 0 := by
  rw [add_mul, mul_sub, map_add, map_sub,
    ← trace_jordan_symmetric_ring τ h_cyc S X Y]
  calc
    (τ ((H * X - X * H) * Y) + τ ((S * X + X * S) * Y)) +
        (τ (X * (H * Y - Y * H)) - τ ((S * X + X * S) * Y))
      = τ ((H * X - X * H) * Y) + τ (X * (H * Y - Y * H)) := by abel
    _ = 0 := trace_ad_skew_ring τ h_cyc H X Y

/-- Exact commutator obstruction to symmetry of a left-weighted cyclic trace form
over any non-commutative ring `[Ring B]`. -/
theorem weighted_symmetry_defect_ring (τ : B →+ M) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (W X Y : B) :
    τ (W * X * Y) - τ (W * Y * X) =
      τ ((W * X - X * W) * Y) := by
  rw [sub_mul, map_sub, trace_cycle3_ring τ h_cyc X W Y, mul_assoc W Y X]

end NonCommRingTraceDuality

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Cyclic movement of the leading factor, with a fixed association convention. -/
theorem trace_cycle3 (A B C : Matrix n n R) :
    trace (A * B * C) = trace (B * (C * A)) := by
  calc
    _ = trace (A * (B * C)) := by rw [mul_assoc]
    _ = trace ((B * C) * A) := trace_mul_comm A (B * C)
    _ = _ := by rw [mul_assoc]

/-- Skew-transposition of the inner derivation for the bilinear trace form. -/
theorem trace_ad_skew (H X Y : Matrix n n R) :
    trace (ad R H X * Y) + trace (X * ad R H Y) = 0 := by
  simp only [ad_apply, sub_mul, mul_sub, trace_sub]
  rw [trace_cycle3 H X Y, mul_assoc X H Y]
  abel

/-- Jordan multiplication is symmetric for the same bilinear form. -/
theorem trace_jordan_symmetric (S X Y : Matrix n n R) :
    trace (jordan R S X * Y) = trace (X * jordan R S Y) := by
  simp only [jordan_apply, add_mul, mul_add, trace_add]
  rw [trace_cycle3 S X Y, mul_assoc X S Y]
  abel

/-- Exact duality for the two linear superoperators. -/
theorem trace_dual_balance (H S X Y : Matrix n n R) :
    trace (dualPlus R H S X * Y) + trace (X * dualMinus R H S Y) = 0 := by
  change trace ((ad R H X + jordan R S X) * Y) +
    trace (X * (ad R H Y - jordan R S Y)) = 0
  rw [add_mul, mul_sub, trace_add, trace_sub,
    ← trace_jordan_symmetric S X Y]
  calc
    _ = trace (ad R H X * Y) + trace (X * ad R H Y) := by abel
    _ = 0 := trace_ad_skew H X Y

/-- The exact failure of using the positive perturbation on both arguments. -/
theorem trace_same_side_defect (H S X Y : Matrix n n R) :
    trace (dualPlus R H S X * Y) + trace (X * dualPlus R H S Y) =
      2 • trace (jordan R S X * Y) := by
  change trace ((ad R H X + jordan R S X) * Y) +
    trace (X * (ad R H Y + jordan R S Y)) = _
  rw [add_mul, mul_add, trace_add, trace_add,
    ← trace_jordan_symmetric S X Y]
  calc
    _ = (trace (ad R H X * Y) + trace (X * ad R H Y)) +
        (trace (jordan R S X * Y) + trace (jordan R S X * Y)) := by abel
    _ = _ := by rw [trace_ad_skew]; simp [two_mul]

/-- The trace shift of the positive perturbation; it is not generally zero. -/
theorem trace_plus (H S X : Matrix n n R) :
    trace (dualPlus R H S X) = 2 • trace (S * X) := by
  simp only [dualPlus_apply, trace_add, trace_sub]
  rw [trace_mul_comm X H, trace_mul_comm X S]
  simp [two_mul]

theorem trace_minus (H S X : Matrix n n R) :
    trace (dualMinus R H S X) = -(2 • trace (S * X)) := by
  simp only [dualMinus_apply, trace_add, trace_sub]
  rw [trace_mul_comm X H, trace_mul_comm X S]
  simp [two_mul]

/-- Exact obstruction to symmetry of a left-weighted bilinear trace form. -/
theorem weighted_symmetry_defect (W X Y : Matrix n n R) :
    trace (W * X * Y) - trace (W * Y * X) =
      trace ((W * X - X * W) * Y) := by
  rw [sub_mul, trace_sub, trace_cycle3 X W Y, mul_assoc W Y X]

/-- Nondegeneracy of the native trace pairing characterizes the obstruction. -/
theorem weighted_symmetric_iff (W : Matrix n n R) :
    (∀ X Y, trace (W * X * Y) = trace (W * Y * X)) ↔
      ∀ X, W * X = X * W := by
  constructor
  · intro h X
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Y
    calc
      trace ((W * X) * Y) = trace ((W * Y) * X) := h X Y
      _ = trace ((X * W) * Y) := by
        rw [trace_cycle3 X W Y, mul_assoc W Y X]
  · intro h X Y
    calc
      trace (W * X * Y) = trace (X * W * Y) := by rw [h X]
      _ = trace (W * Y * X) := by rw [trace_cycle3 X W Y, mul_assoc]

section Star

variable [StarRing R]

/-- For the star-trace pairing the adjoint of `ad_H` is `ad_(star H)`.
In particular a Hermitian generator gives a symmetric, not skew, action. -/
theorem star_trace_ad (H X Y : Matrix n n R) :
    trace (star (ad R H X) * Y) = trace (star X * ad R (star H) Y) := by
  simp only [ad_apply, star_sub, star_mul, sub_mul, mul_sub, trace_sub]
  rw [trace_cycle3 (star H) (star X) Y, mul_assoc (star X) (star H) Y]

theorem star_trace_jordan (S X Y : Matrix n n R) :
    trace (star (jordan R S X) * Y) = trace (star X * jordan R (star S) Y) := by
  simp only [jordan_apply, star_add, star_mul, add_mul, mul_add, trace_add]
  rw [trace_cycle3 (star S) (star X) Y, mul_assoc (star X) (star S) Y]

/-- The extra star hypotheses required to obtain skew/symmetric duality. -/
theorem star_trace_dual_balance (H S X Y : Matrix n n R)
    (hH : star H = -H) (hS : star S = S) :
    trace (star (dualPlus R H S X) * Y) +
      trace (star X * dualMinus R H S Y) = 0 := by
  change trace (star (ad R H X + jordan R S X) * Y) +
    trace (star X * (ad R H Y - jordan R S Y)) = 0
  rw [star_add, add_mul, mul_sub, trace_add, trace_sub,
    star_trace_ad, star_trace_jordan, hH, hS]
  have hn : ad R (-H) Y = -(ad R H Y) := by
    simp only [ad_apply]
    noncomm_ring
  rw [hn, mul_neg, trace_neg]
  abel

end Star

end InfoGeometry.OperatorAlgebra.LieJordanTraceDuality
