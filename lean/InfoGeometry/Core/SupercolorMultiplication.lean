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

/-- Mutual absorption by the co-range projections is exactly their equality.
This characterizes a common source, not a Lie-superalgebra representation. -/
theorem coexact_absorption_iff_equal
    (hS : IsSupercolorSystem d b) :
    (∀ i j, d i * (b j * d j) = d i) ↔
      (∀ i j, b i * d i = b j * d j) := by
  constructor
  · intro h i j
    have hmul (a c : ι) : (b a * d a) * (b c * d c) = b a * d a := by
      rw [mul_assoc, h a c]
    have hstar := congrArg star (hmul i j)
    rw [star_mul, (hS.mp i).2.2.2, (hS.mp j).2.2.2] at hstar
    exact hstar.symm.trans (hmul j i)
  · intro h i j
    rw [← h i j, ← mul_assoc, (hS.mp i).aba_eq_a]

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

theorem sectorCentralCharge_lieBracket_majoranaPlus_of_orthogonal
    [Fintype ι] [DecidableEq ι] (hE : IsOrthogonalExtendedSusy d b)
    (i j : ι) :
    lieBracket (sectorCentralCharge (d i) (b i))
        (majoranaPlus (d j) (b j)) = 0 := by
  have h := (extended_susy_centrality hE).1 i j
  unfold lieBracket majoranaPlus
  calc
    sectorCentralCharge (d i) (b i) * (d j + b j) -
        (d j + b j) * sectorCentralCharge (d i) (b i) =
      (sectorCentralCharge (d i) (b i) * d j -
          d j * sectorCentralCharge (d i) (b i)) +
        (sectorCentralCharge (d i) (b i) * b j -
          b j * sectorCentralCharge (d i) (b i)) := by
            noncomm_ring
    _ = 0 := by
      rw [show sectorCentralCharge (d i) (b i) * d j -
          d j * sectorCentralCharge (d i) (b i) =
          lieBracket (sectorCentralCharge (d i) (b i)) (d j) by rfl,
        show sectorCentralCharge (d i) (b i) * b j -
          b j * sectorCentralCharge (d i) (b i) =
          lieBracket (sectorCentralCharge (d i) (b i)) (b j) by rfl,
        h.1, h.2, add_zero]

theorem sectorCentralCharge_lieBracket_majoranaMinus_of_orthogonal
    [Fintype ι] [DecidableEq ι] (hE : IsOrthogonalExtendedSusy d b)
    (i j : ι) :
    lieBracket (sectorCentralCharge (d i) (b i))
        (majoranaMinus (d j) (b j)) = 0 := by
  have h := (extended_susy_centrality hE).1 i j
  unfold lieBracket majoranaMinus
  calc
    sectorCentralCharge (d i) (b i) * (d j - b j) -
        (d j - b j) * sectorCentralCharge (d i) (b i) =
      (sectorCentralCharge (d i) (b i) * d j -
          d j * sectorCentralCharge (d i) (b i)) -
        (sectorCentralCharge (d i) (b i) * b j -
          b j * sectorCentralCharge (d i) (b i)) := by
            noncomm_ring
    _ = 0 := by
      rw [show sectorCentralCharge (d i) (b i) * d j -
          d j * sectorCentralCharge (d i) (b i) =
          lieBracket (sectorCentralCharge (d i) (b i)) (d j) by rfl,
        show sectorCentralCharge (d i) (b i) * b j -
          b j * sectorCentralCharge (d i) (b i) =
          lieBracket (sectorCentralCharge (d i) (b i)) (b j) by rfl,
        h.1, h.2, sub_zero]

/-- Distinct orthogonal colors have vanishing mixed Majorana
anticommutators.  This is the individual-generator form of the mixed term
used in the total extended-charge calculation. -/
theorem majoranaPlus_majoranaMinus_anticommute_of_orthogonal
    [DecidableEq ι] (hE : IsOrthogonalExtendedSusy d b)
    {i j : ι} (hij : i ≠ j) :
    jordanProd (majoranaPlus (d i) (b i)) (majoranaMinus (d j) (b j)) = 0 ∧
    jordanProd (majoranaMinus (d i) (b i)) (majoranaPlus (d j) (b j)) = 0 := by
  have hS := hE.toIsSupercolorSystem
  have h_ij : (majoranaPlus (d i) (b i)) *
      (majoranaMinus (d j) (b j)) = 0 := by
    unfold majoranaPlus majoranaMinus
    calc
      (d i + b i) * (d j - b j) =
          d i * d j - d i * b j + b i * d j - b i * b j := by
            noncomm_ring
      _ = 0 := by
        rw [hS.d_mul_d i j, hE.d_mul_b_ne hij,
          hS.b_mul_d_ne hij, hS.b_mul_b i j]
        abel
  have h_ji : (majoranaMinus (d j) (b j)) *
      (majoranaPlus (d i) (b i)) = 0 := by
    unfold majoranaMinus majoranaPlus
    calc
      (d j - b j) * (d i + b i) =
          d j * d i + d j * b i - b j * d i - b j * b i := by
            noncomm_ring
      _ = 0 := by
        rw [hS.d_mul_d j i, hE.d_mul_b_ne hij.symm,
          hS.b_mul_d_ne hij.symm, hS.b_mul_b j i]
        abel
  have h_rev_ij : (majoranaMinus (d i) (b i)) *
      (majoranaPlus (d j) (b j)) = 0 := by
    unfold majoranaMinus majoranaPlus
    calc
      (d i - b i) * (d j + b j) =
          d i * d j + d i * b j - b i * d j - b i * b j := by
            noncomm_ring
      _ = 0 := by
        rw [hS.d_mul_d i j, hE.d_mul_b_ne hij,
          hS.b_mul_d_ne hij, hS.b_mul_b i j]
        abel
  have h_rev_ji : (majoranaPlus (d j) (b j)) *
      (majoranaMinus (d i) (b i)) = 0 := by
    unfold majoranaPlus majoranaMinus
    calc
      (d j + b j) * (d i - b i) =
          d j * d i - d j * b i + b j * d i - b j * b i := by
            noncomm_ring
      _ = 0 := by
        rw [hS.d_mul_d j i, hE.d_mul_b_ne hij.symm,
          hS.b_mul_d_ne hij.symm, hS.b_mul_b j i]
        abel
  constructor
  · unfold jordanProd
    rw [h_ij, h_ji, add_zero]
  · unfold jordanProd
    rw [h_rev_ij, h_rev_ji, add_zero]

/-- The total sector charge is central on the generated finite-color algebra. -/
theorem totalCentralCharge_lieBracket_generated
    [Fintype ι] [DecidableEq ι]
    (hE : IsOrthogonalExtendedSusy d b) :
    (∀ j, lieBracket (totalCentralCharge d b) (d j) = 0 ∧
      lieBracket (totalCentralCharge d b) (b j) = 0 ∧
      lieBracket (totalCentralCharge d b) (majoranaPlus (d j) (b j)) = 0 ∧
      lieBracket (totalCentralCharge d b) (majoranaMinus (d j) (b j)) = 0) ∧
    (∀ l m, lieBracket (totalCentralCharge d b) (colorBoson d b l m) = 0) := by
  have h_chiral := (extended_susy_centrality hE).2
  constructor
  · intro j
    have hd := (h_chiral j).1
    have hb := (h_chiral j).2
    have hd' : totalCentralCharge d b * d j - d j * totalCentralCharge d b = 0 := by
      simpa [lieBracket] using hd
    have hb' : totalCentralCharge d b * b j - b j * totalCentralCharge d b = 0 := by
      simpa [lieBracket] using hb
    refine ⟨hd, hb, ?_, ?_⟩
    · unfold lieBracket majoranaPlus
      calc
        totalCentralCharge d b * (d j + b j) - (d j + b j) * totalCentralCharge d b =
            (totalCentralCharge d b * d j - d j * totalCentralCharge d b) +
              (totalCentralCharge d b * b j - b j * totalCentralCharge d b) := by
                noncomm_ring
        _ = 0 := by rw [hd', hb', add_zero]
    · unfold lieBracket majoranaMinus
      calc
        totalCentralCharge d b * (d j - b j) - (d j - b j) * totalCentralCharge d b =
            (totalCentralCharge d b * d j - d j * totalCentralCharge d b) -
              (totalCentralCharge d b * b j - b j * totalCentralCharge d b) := by
                noncomm_ring
        _ = 0 := by rw [hd', hb', sub_zero]
  · intro l m
    exact totalCentralCharge_lieBracket_colorBoson_of_orthogonal hE l m

/-- Unified extended-SUSY contract: distinct colors anticommute, each sector
charge is central on the primitive and Majorana generators, and the total
charge is central on the generated color algebra while the two total
Majorana charges square to opposite central charges. -/
theorem extended_susy_central_charge_master
    [Fintype ι] [DecidableEq ι]
    (hE : IsOrthogonalExtendedSusy d b) :
    (∀ {i j : ι}, i ≠ j →
      jordanProd (majoranaPlus (d i) (b i)) (majoranaPlus (d j) (b j)) = 0 ∧
      jordanProd (majoranaMinus (d i) (b i)) (majoranaMinus (d j) (b j)) = 0 ∧
      jordanProd (majoranaPlus (d i) (b i)) (majoranaMinus (d j) (b j)) = 0 ∧
      jordanProd (majoranaMinus (d i) (b i)) (majoranaPlus (d j) (b j)) = 0) ∧
    (∀ i j : ι,
      lieBracket (sectorCentralCharge (d i) (b i)) (d j) = 0 ∧
      lieBracket (sectorCentralCharge (d i) (b i)) (b j) = 0 ∧
      lieBracket (sectorCentralCharge (d i) (b i))
        (majoranaPlus (d j) (b j)) = 0 ∧
      lieBracket (sectorCentralCharge (d i) (b i))
        (majoranaMinus (d j) (b j)) = 0) ∧
    (∀ j : ι,
      lieBracket (totalCentralCharge d b) (d j) = 0 ∧
      lieBracket (totalCentralCharge d b) (b j) = 0 ∧
      lieBracket (totalCentralCharge d b)
        (majoranaPlus (d j) (b j)) = 0 ∧
      lieBracket (totalCentralCharge d b)
        (majoranaMinus (d j) (b j)) = 0) ∧
    (∀ l m : ι,
      lieBracket (totalCentralCharge d b) (colorBoson d b l m) = 0) ∧
    (totalMajoranaPlus d b * totalMajoranaPlus d b = totalCentralCharge d b ∧
      totalMajoranaMinus d b * totalMajoranaMinus d b = -totalCentralCharge d b ∧
      jordanProd (totalMajoranaPlus d b) (totalMajoranaMinus d b) = 0) := by
  have h_cross : ∀ {i j : ι}, i ≠ j →
      jordanProd (majoranaPlus (d i) (b i)) (majoranaPlus (d j) (b j)) = 0 ∧
      jordanProd (majoranaMinus (d i) (b i)) (majoranaMinus (d j) (b j)) = 0 ∧
      jordanProd (majoranaPlus (d i) (b i)) (majoranaMinus (d j) (b j)) = 0 ∧
      jordanProd (majoranaMinus (d i) (b i)) (majoranaPlus (d j) (b j)) = 0 := by
    intro i j hij
    have h_mixed := majoranaPlus_majoranaMinus_anticommute_of_orthogonal hE hij
    have h_pp : jordanProd (majoranaPlus (d i) (b i))
        (majoranaPlus (d j) (b j)) = 0 := by
      unfold jordanProd majoranaPlus
      calc
        (d i + b i) * (d j + b j) + (d j + b j) * (d i + b i) =
            d i * d j + d i * b j + b i * d j + b i * b j +
              (d j * d i + d j * b i + b j * d i + b j * b i) := by
                noncomm_ring
        _ = 0 := by
          rw [hE.toIsSupercolorSystem.d_mul_d i j,
            hE.d_mul_b_ne hij, hE.toIsSupercolorSystem.b_mul_d_ne hij,
            hE.toIsSupercolorSystem.b_mul_b i j,
            hE.toIsSupercolorSystem.d_mul_d j i,
            hE.d_mul_b_ne hij.symm,
            hE.toIsSupercolorSystem.b_mul_d_ne hij.symm,
            hE.toIsSupercolorSystem.b_mul_b j i]
          abel
    have h_mm : jordanProd (majoranaMinus (d i) (b i))
        (majoranaMinus (d j) (b j)) = 0 := by
      unfold jordanProd majoranaMinus
      calc
        (d i - b i) * (d j - b j) + (d j - b j) * (d i - b i) =
            d i * d j - d i * b j - b i * d j + b i * b j +
              (d j * d i - d j * b i - b j * d i + b j * b i) := by
                noncomm_ring
        _ = 0 := by
          rw [hE.toIsSupercolorSystem.d_mul_d i j,
            hE.d_mul_b_ne hij, hE.toIsSupercolorSystem.b_mul_d_ne hij,
            hE.toIsSupercolorSystem.b_mul_b i j,
            hE.toIsSupercolorSystem.d_mul_d j i,
            hE.d_mul_b_ne hij.symm,
            hE.toIsSupercolorSystem.b_mul_d_ne hij.symm,
            hE.toIsSupercolorSystem.b_mul_b j i]
          abel
    exact ⟨h_pp, h_mm, h_mixed.1, h_mixed.2⟩
  have h_sector : ∀ i j : ι,
      lieBracket (sectorCentralCharge (d i) (b i)) (d j) = 0 ∧
      lieBracket (sectorCentralCharge (d i) (b i)) (b j) = 0 ∧
      lieBracket (sectorCentralCharge (d i) (b i))
        (majoranaPlus (d j) (b j)) = 0 ∧
      lieBracket (sectorCentralCharge (d i) (b i))
        (majoranaMinus (d j) (b j)) = 0 := by
    intro i j
    have h_primitive := (extended_susy_centrality hE).1 i j
    exact ⟨h_primitive.1, h_primitive.2,
      sectorCentralCharge_lieBracket_majoranaPlus_of_orthogonal hE i j,
      sectorCentralCharge_lieBracket_majoranaMinus_of_orthogonal hE i j⟩
  have h_total := totalCentralCharge_lieBracket_generated hE
  have h_squares := extended_susy_total_charges hE
  refine ⟨h_cross, h_sector, ?_, ?_, h_squares⟩
  · intro j
    exact ⟨(h_total.1 j).1, (h_total.1 j).2.1,
      (h_total.1 j).2.2.1, (h_total.1 j).2.2.2⟩
  · exact h_total.2

/-- Adjoint duality is an explicit hypothesis, not a consequence of MP. -/
theorem star_majoranaPlus_of_dual (hdual : ∀ i, b i = star (d i)) (i : ι) :
    star (majoranaPlus (d i) (b i)) = majoranaPlus (d i) (b i) := by
  simp only [majoranaPlus, star_add, hdual i, star_star, add_comm]

theorem star_majoranaMinus_of_dual (hdual : ∀ i, b i = star (d i)) (i : ι) :
    star (majoranaMinus (d i) (b i)) = -majoranaMinus (d i) (b i) := by
  simp only [majoranaMinus, star_sub, hdual i, star_star]
  abel

end InfoGeometry.Core.SuperGrassmannianSusy
