/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.SuperGrassmannianSusy

/-!
# Color multiplication with an explicit common source

The base supercolor hypotheses annihilate unmatched middle indices. They do
not suffice for the matching-middle matrix-unit law: a common co-range is
required here. These are associative product identities, not an `sl(k|1)`
representation or a Lie-superalgebra classification.
-/

namespace InfoGeometry.Core.SuperGrassmannianSusy

variable {R : Type*} [Ring R] [StarRing R]
variable {ι : Type*} {d b : ι → R}

/-- Exact product before any common-source simplification. -/
omit [StarRing R] in
theorem colorBoson_mul_middle (i j l m : ι) :
    colorBoson d b i j * colorBoson d b l m = d i * (b j * d l) * b m := by
  simp only [colorBoson, mul_assoc]

/-- Common co-range projections supply the missing matching-middle law. -/
theorem colorBoson_mul_of_common_source [DecidableEq ι]
    (hS : IsSupercolorSystem d b) {q : R}
    (hq : ∀ i, b i * d i = q) (i j l m : ι) :
    colorBoson d b i j * colorBoson d b l m =
      if j = l then colorBoson d b i m else 0 := by
  by_cases hjl : j = l
  · subst l
    simp only [↓reduceIte]
    rw [colorBoson_mul_middle, hq j, ← hq i]
    change d i * (b i * d i) * b m = d i * b m
    rw [← mul_assoc (d i) (b i) (d i), (hS.mp i).aba_eq_a]
  · simp only [hjl, ↓reduceIte]
    exact colorBoson_mul_eq_zero_of_middle_ne hS hjl

/-- The commutator is closed in the span of color products under the same
common-source hypothesis. No super-Jacobi or representation is asserted. -/
theorem colorBoson_lieBracket_of_common_source [DecidableEq ι]
    (hS : IsSupercolorSystem d b) {q : R}
    (hq : ∀ i, b i * d i = q) (i j l m : ι) :
    lieBracket (colorBoson d b i j) (colorBoson d b l m) =
      (if j = l then colorBoson d b i m else 0) -
        (if m = i then colorBoson d b l j else 0) := by
  unfold lieBracket
  rw [colorBoson_mul_of_common_source hS hq, colorBoson_mul_of_common_source hS hq]

/-- Adjoint duality is an explicit hypothesis, not a consequence of MP. -/
theorem star_majoranaPlus_of_dual (hdual : ∀ i, b i = star (d i)) (i : ι) :
    star (majoranaPlus (d i) (b i)) = majoranaPlus (d i) (b i) := by
  simp only [majoranaPlus, star_add, hdual i, star_star, add_comm]

theorem star_majoranaMinus_of_dual (hdual : ∀ i, b i = star (d i)) (i : ι) :
    star (majoranaMinus (d i) (b i)) = -majoranaMinus (d i) (b i) := by
  simp only [majoranaMinus, star_sub, hdual i, star_star]
  abel

end InfoGeometry.Core.SuperGrassmannianSusy
