/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.DelaunayFlipMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.RohozhkinProjectiveCrossRatio
import InfoGeometry.Projective.MobiusGauge

/-!
# Delaunay Möbius Flip

This file bridges the rational local Delaunay flip matrices with their underlying
projective-gauge structure.

#### BUCKET 1: CLOSED FINITE THEOREMS
- The two columns of `flipBlock` sum to `1`.
- The two columns are barycentric coordinates for `ζ l` and `ζ j` in the
  affine chart determined by `(ζ k, ζ i)`.
- The determinant and entry-ratio residue of `flipBlock` are the expected
  rational projective quantities.
- The induced ratio coordinate action is the corresponding fractional linear
  expression.
- `flipBlock_mobius_gauge_covariant` proves the finite Möbius gauge covariance
  under explicit nonzero gauge hypotheses.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
- Geometric Delaunay admissibility and global analytic projective geometry remain
  outside this finite matrix owner.
-/

namespace InfoGeometry.Topology.Delaunay

open InfoGeometry.Projective
open Matrix

variable {ι : Type*} [DecidableEq ι] (labels : FlipLabels ι)
variable (i k j l : ι) (hik : i ≠ k)

omit [DecidableEq ι] in
/-- The flipBlock is a barycentric transition: its left column sums to 1. -/
theorem flipBlock_column_sum_left :
    flipBlock labels i k j l hik 0 0 + flipBlock labels i k j l hik 1 0 = 1 := by
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  simpa [flipBlock, rohozhkinFlipBlock] using
    (rohozhkinFlipBlock_first_column_sum (labels.ζ i) (labels.ζ k) (labels.ζ j) (labels.ζ l) hd)

omit [DecidableEq ι] in
/-- The flipBlock is a barycentric transition: its right column sums to 1. -/
theorem flipBlock_column_sum_right :
    flipBlock labels i k j l hik 0 1 + flipBlock labels i k j l hik 1 1 = 1 := by
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  simpa [flipBlock, rohozhkinFlipBlock] using
    (rohozhkinFlipBlock_second_column_sum (labels.ζ i) (labels.ζ k) (labels.ζ j) (labels.ζ l) hd)

omit [DecidableEq ι] in
/-- The first column gives the barycentric coordinates of ζ l in the segment [ζ k, ζ i]. -/
theorem flipBlock_barycentric_l :
    flipBlock labels i k j l hik 0 0 * labels.ζ k + flipBlock labels i k j l hik 1 0 * labels.ζ i = labels.ζ l := by
  dsimp [flipBlock]
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  field_simp [hd]
  ring

omit [DecidableEq ι] in
/-- The second column gives the barycentric coordinates of ζ j in the segment [ζ k, ζ i]. -/
theorem flipBlock_barycentric_j :
    flipBlock labels i k j l hik 0 1 * labels.ζ k + flipBlock labels i k j l hik 1 1 * labels.ζ i = labels.ζ j := by
  dsimp [flipBlock]
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  field_simp [hd]
  ring

omit [DecidableEq ι] in
/-- The determinant of the flip block evaluates to the ratio of cross edges. -/
theorem flipBlock_det :
    Matrix.det (flipBlock labels i k j l hik) = (labels.ζ j - labels.ζ l) / (labels.ζ i - labels.ζ k) := by
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  exact rohozhkinFlipBlock_det (labels.ζ i) (labels.ζ k) (labels.ζ j) (labels.ζ l) hd

omit [DecidableEq ι] in
/-- The projective action of the flip block aligns perfectly with the Möbius evaluation. -/
theorem flipBlock_projective_action (r : ℚ) :
    let A := flipBlock labels i k j l hik
    (A 0 0 * r + A 0 1) / (A 1 0 * r + A 1 1) =
      ((labels.ζ i - labels.ζ l) * r + (labels.ζ i - labels.ζ j)) /
      ((labels.ζ l - labels.ζ k) * r + (labels.ζ j - labels.ζ k)) := by
  dsimp [flipBlock]
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  field_simp [hd]

omit [DecidableEq ι] in
/-- The Möbius-invariant residue extracted from the matrix is exactly the cross ratio. -/
theorem flipBlock_crossRatio (a b c d : ℚ) (A : Matrix (Fin 2) (Fin 2) ℚ) (hA : A = flipBlock labels i k j l hik) :
    a = A 0 0 → b = A 0 1 → c = A 1 0 → d = A 1 1 →
    (a * d) / (b * c) =
      ((labels.ζ i - labels.ζ l) * (labels.ζ j - labels.ζ k)) /
      ((labels.ζ i - labels.ζ j) * (labels.ζ l - labels.ζ k)) := by
  intro ha hb hc hd'
  subst A
  subst a
  subst b
  subst c
  subst d
  dsimp [flipBlock]
  have hden : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  field_simp [hden]

omit [DecidableEq ι] in
/-- A nondegenerate source chart remains nondegenerate after a Möbius relabeling. -/
theorem mobiusComp_sub_ne_zero
    (hik : i ≠ k)
    (T : MobiusMap ℚ)
    (hgi : leftGauge T (labels.ζ i) ≠ 0)
    (hgk : leftGauge T (labels.ζ k) ≠ 0) :
    mobiusComp T labels.ζ i - mobiusComp T labels.ζ k ≠ 0 := by
  change projectiveAction T (labels.ζ i) - projectiveAction T (labels.ζ k) ≠ 0
  rw [projectiveAction_sub T (labels.ζ i) (labels.ζ k) hgi hgk]
  exact div_ne_zero
    (mul_ne_zero T.det_ne_zero (labels.nonzero_den hik))
    (mul_ne_zero hgi hgk)

omit [DecidableEq ι] in
/-- The local flip block transforms covariantly under a nondegenerate Möbius relabeling.

Each entry is obtained from the determinant-over-gauges difference formula; the four
diagonal gauge factors therefore cancel exactly in the affine chart. -/
theorem flipBlock_mobius_gauge_covariant
    (T : MobiusMap ℚ)
    (hgi : leftGauge T (labels.ζ i) ≠ 0)
    (hgk : leftGauge T (labels.ζ k) ≠ 0)
    (hgj : leftGauge T (labels.ζ j) ≠ 0)
    (hgl : leftGauge T (labels.ζ l) ≠ 0) :
    let ζ' : ι → ℚ := mobiusComp T labels.ζ
    let A' := !![(ζ' i - ζ' l) / (ζ' i - ζ' k), (ζ' i - ζ' j) / (ζ' i - ζ' k);
                 (ζ' l - ζ' k) / (ζ' i - ζ' k), (ζ' j - ζ' k) / (ζ' i - ζ' k)]
    A' = !![leftGauge T (labels.ζ k), 0; 0, leftGauge T (labels.ζ i)] *
         flipBlock labels i k j l hik *
         !![(leftGauge T (labels.ζ l))⁻¹, 0; 0, (leftGauge T (labels.ζ j))⁻¹] := by
  dsimp
  have h_ik' := mobiusComp_sub_ne_zero labels i k hik T hgi hgk
  have hgi' : T.γ * labels.ζ i + T.δ ≠ 0 := hgi
  have hgk' : T.γ * labels.ζ k + T.δ ≠ 0 := hgk
  have hgj' : T.γ * labels.ζ j + T.δ ≠ 0 := hgj
  have hgl' : T.γ * labels.ζ l + T.δ ≠ 0 := hgl
  simp only [mobiusComp]
  ext a b
  fin_cases a <;> fin_cases b
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [projectiveAction_sub T (labels.ζ i) (labels.ζ l) hgi hgl,
      projectiveAction_sub T (labels.ζ i) (labels.ζ k) hgi hgk]
    simp [flipBlock, leftGauge]
    field_simp [T.det_ne_zero, hgi', hgk', hgl', labels.nonzero_den hik]
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [projectiveAction_sub T (labels.ζ i) (labels.ζ j) hgi hgj,
      projectiveAction_sub T (labels.ζ i) (labels.ζ k) hgi hgk]
    simp [flipBlock, leftGauge]
    field_simp [T.det_ne_zero, hgi', hgk', hgj', labels.nonzero_den hik]
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [projectiveAction_sub T (labels.ζ l) (labels.ζ k) hgl hgk,
      projectiveAction_sub T (labels.ζ i) (labels.ζ k) hgi hgk]
    simp [flipBlock, leftGauge]
    field_simp [T.det_ne_zero, hgi', hgk', hgl', labels.nonzero_den hik]
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [projectiveAction_sub T (labels.ζ j) (labels.ζ k) hgj hgk,
      projectiveAction_sub T (labels.ζ i) (labels.ζ k) hgi hgk]
    simp [flipBlock, leftGauge]
    field_simp [T.det_ne_zero, hgi', hgk', hgj', labels.nonzero_den hik]

section MobiusCrossRatio

variable {K : Type} [Field K]

/-- A nondegenerate Möbius transformation preserves the projective cross-ratio. -/
theorem projectiveCrossRatio_mobius_invariant
    (T : MobiusMap K) (a b c d : K)
    (ha : leftGauge T a ≠ 0) (hb : leftGauge T b ≠ 0)
    (hc : leftGauge T c ≠ 0) (hd : leftGauge T d ≠ 0)
    (hac : a - c ≠ 0) (hbd : b - d ≠ 0) :
    projectiveCrossRatio
        (projectiveAction T a) (projectiveAction T b)
        (projectiveAction T c) (projectiveAction T d) =
      projectiveCrossRatio a b c d := by
  unfold projectiveCrossRatio
  rw [projectiveAction_sub T a b ha hb,
      projectiveAction_sub T c d hc hd,
      projectiveAction_sub T a c ha hc,
      projectiveAction_sub T b d hb hd]
  field_simp [T.det_ne_zero, ha, hb, hc, hd, hac, hbd]

end MobiusCrossRatio

end InfoGeometry.Topology.Delaunay
