/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Partial isometries and their ordered composition defect

Source and range expressions are defined in an arbitrary associative star
ring. A partial isometry satisfies the explicit equation `v * star v * v = v`.
For two such elements, the defect of their product is the sandwich of the
commutator of the intermediate range and source projections. Thus compatible
supports give a partial isometry without requiring ambient commutativity.

These are algebraic statements. No norm, completion, spectral consequence,
or empirical interpretation is inferred from the star-ring equations.
-/

namespace InfoGeometry.Algebra.NonCommutativity

variable {A : Type*} [Ring A] [StarRing A]

/-- Range projection expression associated to a branch operator. -/
def rangeProjection (S : A) : A :=
  S * star S

/-- Source projection expression associated to a branch operator. -/
def sourceProjection (S : A) : A :=
  star S * S

/-- The commutator with the adjoint is the range expression minus the source. -/
theorem branch_commutator_eq_range_sub_source (S : A) :
    S * star S - star S * S = rangeProjection S - sourceProjection S := by
  rfl

/-- For an isometry, the adjoint commutator measures the range/unit mismatch. -/
theorem isometry_branch_commutator_eq_range_sub_one
    (S : A) (hS : star S * S = 1) :
    S * star S - star S * S = rangeProjection S - 1 := by
  unfold rangeProjection
  rw [hS]

/-- A proper isometric range gives a nonzero commutator with the adjoint. -/
theorem isometry_branch_commutator_ne_zero
    (S : A) (hS : star S * S = 1)
    (hRange : rangeProjection S ≠ (1 : A)) :
    S * star S - star S * S ≠ 0 := by
  rw [isometry_branch_commutator_eq_range_sub_one S hS]
  intro h
  exact hRange (sub_eq_zero.mp h)

/-- The range projection of a partial isometry is idempotent. -/
theorem rangeProjection_idempotent_of_partial_isometry
    (S : A) (hS : S * star S * S = S) :
    rangeProjection S * rangeProjection S = rangeProjection S := by
  unfold rangeProjection
  calc
    (S * star S) * (S * star S) = (S * star S * S) * star S := by
      simp only [mul_assoc]
    _ = S * star S := by rw [hS]

/-- The source projection of a partial isometry is idempotent. -/
theorem sourceProjection_idempotent_of_partial_isometry
    (S : A) (hS : star S * S * star S = star S) :
    sourceProjection S * sourceProjection S = sourceProjection S := by
  unfold sourceProjection
  calc
    (star S * S) * (star S * S) = (star S * S * star S) * S := by
      simp only [mul_assoc]
    _ = star S * S := by rw [hS]

/-- A two-sided inverse makes the adjoint commutator vanish. -/
theorem two_sided_inverse_branch_commutator_zero
    (S : A) (h_left : star S * S = 1) (h_right : S * star S = 1) :
    S * star S - star S * S = 0 := by
  rw [h_left, h_right]
  exact sub_self 1

/-- The adjoint satisfies the reversed partial-isometry equation. -/
theorem partial_isometry_star {v : A} (hv : v * star v * v = v) :
    star v * v * star v = star v := by
  simpa only [star_mul, star_star, mul_assoc] using congrArg star hv

/-- The composite defect retains the ordered commutator of the intermediate
supports. Only the two partial-isometry equations are assumed. -/
theorem partial_isometry_mul_residual {v w : A}
    (hv : v * star v * v = v) (hw : w * star w * w = w) :
    (w * v) * star (w * v) * (w * v) - w * v =
      w * (rangeProjection v * sourceProjection w -
        sourceProjection w * rangeProjection v) * v := by
  have hcancel : w * (sourceProjection w * rangeProjection v) * v = w * v := by
    calc
      _ = (w * star w * w) * (v * star v * v) := by
        simp only [sourceProjection, rangeProjection, mul_assoc]
      _ = w * v := by rw [hw, hv]
  calc
    _ = w * (rangeProjection v * sourceProjection w) * v - w * v := by
      simp only [rangeProjection, sourceProjection, star_mul, mul_assoc]
    _ = w * (rangeProjection v * sourceProjection w) * v -
        w * (sourceProjection w * rangeProjection v) * v := by rw [hcancel]
    _ = _ := by rw [mul_sub, sub_mul]

/-- The exact compatibility condition is vanishing of the sandwiched support
commutator; no cancellation of the two outside operators is asserted. -/
theorem partial_isometry_mul_iff_sandwich_commutator_eq_zero {v w : A}
    (hv : v * star v * v = v) (hw : w * star w * w = w) :
    (w * v) * star (w * v) * (w * v) = w * v ↔
      w * (rangeProjection v * sourceProjection w -
        sourceProjection w * rangeProjection v) * v = 0 := by
  calc
    _ ↔ (w * v) * star (w * v) * (w * v) - w * v = 0 := sub_eq_zero.symm
    _ ↔ _ := by rw [partial_isometry_mul_residual hv hw]

/-- Commutation of the intermediate supports is sufficient for composition. -/
theorem partial_isometry_mul_of_commute {v w : A}
    (hv : v * star v * v = v) (hw : w * star w * w = w)
    (hcomm : Commute (rangeProjection v) (sourceProjection w)) :
    (w * v) * star (w * v) * (w * v) = w * v := by
  apply (partial_isometry_mul_iff_sandwich_commutator_eq_zero hv hw).mpr
  rw [hcomm.eq, sub_self, mul_zero, zero_mul]

/-- Matched source and range projections give a composable partial isometry. -/
theorem partial_isometry_mul_of_matched_support {v w : A}
    (hv : v * star v * v = v) (hw : w * star w * w = w)
    (hmatch : sourceProjection w = rangeProjection v) :
    (w * v) * star (w * v) * (w * v) = w * v := by
  apply partial_isometry_mul_of_commute hv hw
  change rangeProjection v * sourceProjection w =
    sourceProjection w * rangeProjection v
  rw [hmatch]

/-- On a matched intermediate support, the second adjoint recovers the first arrow. -/
theorem star_mul_mul_of_matched_support {v w : A}
    (hv : v * star v * v = v)
    (hmatch : sourceProjection w = rangeProjection v) :
    star w * (w * v) = v := by
  calc
    _ = sourceProjection w * v := by rw [sourceProjection, mul_assoc]
    _ = rangeProjection v * v := by rw [hmatch]
    _ = v := hv

/-- The first adjoint recovers the second arrow on the same matched support. -/
theorem mul_mul_star_of_matched_support {v w : A}
    (hw : w * star w * w = w)
    (hmatch : sourceProjection w = rangeProjection v) :
    (w * v) * star v = w := by
  calc
    _ = w * rangeProjection v := by rw [rangeProjection, mul_assoc]
    _ = w * sourceProjection w := by rw [hmatch]
    _ = w := by simpa only [sourceProjection, mul_assoc] using hw

/-- Matched composition keeps the initial support of the first arrow. -/
theorem sourceProjection_mul_of_matched_support {v w : A}
    (hv : v * star v * v = v)
    (hmatch : sourceProjection w = rangeProjection v) :
    sourceProjection (w * v) = sourceProjection v := by
  calc
    _ = star v * (star w * (w * v)) := by
      simp only [sourceProjection, star_mul, mul_assoc]
    _ = sourceProjection v := by rw [star_mul_mul_of_matched_support hv hmatch]; rfl

/-- Matched composition keeps the final support of the second arrow. -/
theorem rangeProjection_mul_of_matched_support {v w : A}
    (hw : w * star w * w = w)
    (hmatch : sourceProjection w = rangeProjection v) :
    rangeProjection (w * v) = rangeProjection w := by
  calc
    _ = ((w * v) * star v) * star w := by
      simp only [rangeProjection, star_mul, mul_assoc]
    _ = rangeProjection w := by rw [mul_mul_star_of_matched_support hw hmatch]; rfl

/-- With matched supports, a nonzero first arrow cannot compose to zero. -/
theorem mul_ne_zero_of_matched_support {v w : A}
    (hv : v * star v * v = v)
    (hmatch : sourceProjection w = rangeProjection v) (hv0 : v ≠ 0) :
    w * v ≠ 0 := by
  intro hzero
  apply hv0
  calc
    v = star w * (w * v) := (star_mul_mul_of_matched_support hv hmatch).symm
    _ = 0 := by rw [hzero, mul_zero]

end InfoGeometry.Algebra.NonCommutativity
