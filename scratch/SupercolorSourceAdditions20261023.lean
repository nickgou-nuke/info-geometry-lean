/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.SupercolorMultiplication

/-!
# SCRATCH CANDIDATE: source actions extending native supercolor owners

Uncompiled candidate for parent integration. Adapted from
upstream/feat/supercolor-source-closure at
41284b6c0a84785c7bf20ed153a0c17b29f98932,
Core/SupercolorSourceClosure.lean.

Contract: use the native IsSupercolorSystem/IsOrthogonalExtendedSusy,
colorBoson, jordanProd, and totalCentralCharge on an associative ring.
Multiplication order is retained: a source acts on forward arrows on the
right, and backward arrows on the left. The converse endpoint actions vanish.
The native coexact_absorption_iff_equal supplies common-source absorption;
there is no second absorption-equivalence theorem here.

The charge-star result requires only the individual MP laws, not adjoint
duality, common sources, or orthogonal cross-colors. No bracket definition,
Jacobi theorem, representation, classification, or aggregate certificate is added.
-/

namespace InfoGeometry.Core.SuperGrassmannianSusy.SourceAdditions

open InfoGeometry.Core.SuperGrassmannianSusy
open InfoGeometry.Singular.MoorePenrose

variable {R : Type*} [Ring R] {ι : Type*} {d b : ι → R}

/-- One absorption equation gives the matching-middle product, without MP. -/
theorem colorBoson_mul_of_absorption (i j m : ι)
    (habs : d i * (b j * d j) = d i) :
    colorBoson d b i j * colorBoson d b j m = colorBoson d b i m := by
  rw [colorBoson_mul_middle, habs]
  rfl

section StarRing
variable [StarRing R]

/-- Each summand is self-adjoint by its two MP support equations. -/
theorem total_charge_star_of_mp [Fintype ι]
    (hmp : ∀ i, IsMoorePenroseInverse (d i) (b i)) :
    star (totalCentralCharge d b) = totalCentralCharge d b := by
  unfold totalCentralCharge
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sectorCentralCharge, jordanProd, star_add,
    (hmp i).ab_adj_eq, (hmp i).ba_adj_eq]

/-- The four ordered source endpoint actions; no arrow/adjoint identification. -/
theorem source_endpoint_actions (hS : IsSupercolorSystem d b)
    {q : R} (hq : ∀ i, b i * d i = q) (i : ι) :
    d i * q = d i ∧ q * d i = 0 ∧ q * b i = b i ∧ b i * q = 0 := by
  have habs : ∀ j k, d j * (b k * d k) = d j :=
    (coexact_absorption_iff_equal hS).mpr
      (fun j k => (hq j).trans (hq k).symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hq i] using habs i i
  · rw [← hq i, mul_assoc, hS.d_mul_d i i, mul_zero]
  · rw [← hq i, (hS.mp i).bab_eq_b]
  · rw [← hq i, ← mul_assoc, hS.b_mul_b i i, zero_mul]

/-- A color product acts on the forward family at its matching right index. -/
theorem colorBoson_mul_forward [DecidableEq ι] (hS : IsSupercolorSystem d b)
    {q : R} (hq : ∀ i, b i * d i = q) (i j l : ι) :
    colorBoson d b i j * d l = if j = l then d i else 0 := by
  by_cases h : j = l
  · subst l
    simpa only [colorBoson, mul_assoc, hq j, ite_true] using
      (source_endpoint_actions hS hq i).1
  · simp only [h, ite_false, colorBoson, mul_assoc,
      hS.b_mul_d_ne h, mul_zero]

/-- Reverse ordered forward action vanishes without a common-source assumption. -/
theorem forward_mul_colorBoson (hS : IsSupercolorSystem d b) (i j l : ι) :
    d l * colorBoson d b i j = 0 := by
  simp only [colorBoson, ← mul_assoc, hS.d_mul_d l i, zero_mul]

/-- The backward family acts on a color product at its matching left index. -/
theorem backward_mul_colorBoson [DecidableEq ι] (hS : IsSupercolorSystem d b)
    {q : R} (hq : ∀ i, b i * d i = q) (i j l : ι) :
    b l * colorBoson d b i j = if l = i then b j else 0 := by
  by_cases h : l = i
  · subst l
    simpa only [colorBoson, ← mul_assoc, hq i, ite_true] using
      (source_endpoint_actions hS hq j).2.2.1
  · simp only [h, ite_false, colorBoson, ← mul_assoc,
      hS.b_mul_d_ne h, zero_mul]

/-- Reverse ordered backward action vanishes without a common-source assumption. -/
theorem colorBoson_mul_backward (hS : IsSupercolorSystem d b) (i j l : ι) :
    colorBoson d b i j * b l = 0 := by
  simp only [colorBoson, mul_assoc, hS.b_mul_b j l, mul_zero]

/-- The unnormalized odd pair retains the common-source diagonal term. -/
theorem odd_pair_closure [DecidableEq ι] (hS : IsSupercolorSystem d b)
    {q : R} (hq : ∀ i, b i * d i = q) (i j : ι) :
    jordanProd (d i) (b j) =
      colorBoson d b i j + (if i = j then q else 0) := by
  by_cases h : i = j
  · subst j
    simp only [jordanProd, colorBoson, ite_true, hq i]
  · simp only [jordanProd, colorBoson, h, ite_false,
      hS.b_mul_d_ne (Ne.symm h), add_zero]

/-- Absorption across distinct orthogonal sectors forces that MP pair to vanish. -/
theorem orthogonal_absorption_forces_zero
    (hE : IsOrthogonalExtendedSusy d b) {i j : ι} (hij : i ≠ j)
    (habs : d i * (b j * d j) = d i) : d i = 0 ∧ b i = 0 := by
  have hd : d i = 0 := by
    calc
      d i = (d i * b j) * d j := by simpa only [mul_assoc] using habs.symm
      _ = 0 := by rw [hE.d_mul_b_ne hij, zero_mul]
  refine ⟨hd, ?_⟩
  have houter := (hE.mp i).bab_eq_b
  simpa only [hd, mul_zero, zero_mul] using houter.symm

end StarRing
end InfoGeometry.Core.SuperGrassmannianSusy.SourceAdditions
