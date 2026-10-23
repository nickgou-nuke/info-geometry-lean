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

omit [StarRing R] in
/-- Exact product before any common-source simplification. -/
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

/-! The sector charge is not generally central on the individual matrix
units: it records the source/target endpoint action.  The endpoint terms
cancel after summing over all colors, which is the centrality statement used
by the extended finite-color system. -/

theorem sectorCentralCharge_mul_colorBoson_of_orthogonal
    [DecidableEq ι] (hE : IsOrthogonalExtendedSusy d b)
    (i l m : ι) :
    sectorCentralCharge (d i) (b i) * colorBoson d b l m =
      if i = l then colorBoson d b l m else 0 := by
  by_cases hil : i = l
  · subst l
    simp only [↓reduceIte]
    unfold sectorCentralCharge jordanProd colorBoson
    calc
      (d i * b i + b i * d i) * (d i * b m) =
          (d i * b i * d i) * b m + (b i * d i * d i) * b m := by
            noncomm_ring
      _ = d i * b m + 0 := by
            rw [(hE.mp i).aba_eq_a]
            congr 1
            calc
              (b i * d i * d i) * b m = b i * (d i * d i) * b m := by
                simp only [mul_assoc]
              _ = 0 := by
                rw [hE.toIsSupercolorSystem.d_mul_d i i]
                simp
      _ = d i * b m := add_zero _
  · simp only [hil, ↓reduceIte]
    unfold sectorCentralCharge jordanProd colorBoson
    calc
      (d i * b i + b i * d i) * (d l * b m) =
          d i * (b i * d l) * b m + b i * (d i * d l) * b m := by
            noncomm_ring
      _ = 0 := by
            rw [hE.toIsSupercolorSystem.b_mul_d_ne hil,
              hE.toIsSupercolorSystem.d_mul_d i l]
            simp

theorem colorBoson_mul_sectorCentralCharge_of_orthogonal
    [DecidableEq ι] (hE : IsOrthogonalExtendedSusy d b)
    (i l m : ι) :
    colorBoson d b l m * sectorCentralCharge (d i) (b i) =
      if m = i then colorBoson d b l m else 0 := by
  by_cases hmi : m = i
  · subst m
    simp only [↓reduceIte]
    unfold sectorCentralCharge jordanProd colorBoson
    calc
      (d l * b i) * (d i * b i + b i * d i) =
          d l * (b i * d i * b i) + d l * (b i * b i) * d i := by
            noncomm_ring
      _ = d l * b i := by
            rw [(hE.mp i).bab_eq_b, hE.toIsSupercolorSystem.b_mul_b i i]
            simp
  · simp only [hmi, ↓reduceIte]
    unfold sectorCentralCharge jordanProd colorBoson
    calc
      (d l * b m) * (d i * b i + b i * d i) =
          d l * (b m * d i) * b i + d l * (b m * b i) * d i := by
            noncomm_ring
      _ = 0 := by
            rw [hE.toIsSupercolorSystem.b_mul_d_ne hmi,
              hE.toIsSupercolorSystem.b_mul_b m i]
            simp

theorem sectorCentralCharge_lieBracket_colorBoson_of_orthogonal
    [DecidableEq ι] (hE : IsOrthogonalExtendedSusy d b)
    (i l m : ι) :
    lieBracket (sectorCentralCharge (d i) (b i)) (colorBoson d b l m) =
      (if i = l then colorBoson d b l m else 0) -
        (if m = i then colorBoson d b l m else 0) := by
  unfold lieBracket
  rw [sectorCentralCharge_mul_colorBoson_of_orthogonal hE,
    colorBoson_mul_sectorCentralCharge_of_orthogonal hE]

theorem totalCentralCharge_lieBracket_colorBoson_of_orthogonal
    [Fintype ι] [DecidableEq ι]
    (hE : IsOrthogonalExtendedSusy d b) (l m : ι) :
    lieBracket (totalCentralCharge d b) (colorBoson d b l m) = 0 := by
  unfold totalCentralCharge lieBracket
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [sectorCentralCharge_mul_colorBoson_of_orthogonal hE,
    colorBoson_mul_sectorCentralCharge_of_orthogonal hE]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq' Finset.univ l (fun _ => colorBoson d b l m)]
  rw [Finset.sum_ite_eq Finset.univ m (fun _ => colorBoson d b l m)]
  simp

/-- Adjoint duality is an explicit hypothesis, not a consequence of MP. -/
theorem star_majoranaPlus_of_dual (hdual : ∀ i, b i = star (d i)) (i : ι) :
    star (majoranaPlus (d i) (b i)) = majoranaPlus (d i) (b i) := by
  simp only [majoranaPlus, star_add, hdual i, star_star, add_comm]

theorem star_majoranaMinus_of_dual (hdual : ∀ i, b i = star (d i)) (i : ι) :
    star (majoranaMinus (d i) (b i)) = -majoranaMinus (d i) (b i) := by
  simp only [majoranaMinus, star_sub, hdual i, star_star]
  abel

end InfoGeometry.Core.SuperGrassmannianSusy
