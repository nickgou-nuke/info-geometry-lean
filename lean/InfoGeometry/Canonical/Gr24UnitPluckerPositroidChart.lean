/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Topology.Gr24PositroidCanonicalForm

/-!
# The `p₀₁ = 1` Plücker chart and its positroid faces

This module gives the closed affine chart `p₀₁ = 1` on the nonnegative Klein
quadric of `Gr(2,4)`.  Its four coordinates are `p₀₂, p₀₃, p₁₂, p₁₃`, with
the nonnegative constraint `p₂₃ = p₀₂ p₁₃ - p₀₃ p₁₂ ≥ 0`.  This is the exact
Plücker relation in this gauge, so the chart includes boundary points where
monomial network coordinates cease to be valid.

The exact supports of its six Plücker coordinates give a finite disjoint
decomposition.  The full-support positive-network chart is embedded into this
decomposition and retains the existing Mathlib alternating canonical form and
its residue theorems.  This is a chart-level result, not a claim that this
single chart covers the entire projective Grassmannian.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.Gr24UnitPluckerPositroidChart

open InfoGeometry.Topology.Gr24PositroidCanonicalForm

/-! ## The closed affine chart of the nonnegative Klein quadric -/

/-- Four independent nonnegative coordinates on the projective chart
`p₀₁ = 1`. -/
@[ext]
structure ChartCoordinates where
  p02 : ℝ
  p03 : ℝ
  p12 : ℝ
  p13 : ℝ
  p02_nonneg : 0 ≤ p02
  p03_nonneg : 0 ≤ p03
  p12_nonneg : 0 ≤ p12
  p13_nonneg : 0 ≤ p13
  p23_nonneg : 0 ≤ p02 * p13 - p03 * p12

/-- The origin is a concrete point of the closed affine chart. -/
def chartCoordinatesOrigin : ChartCoordinates :=
  ⟨0, 0, 0, 0, le_rfl, le_rfl, le_rfl, le_rfl, by norm_num⟩

instance : Inhabited ChartCoordinates := ⟨chartCoordinatesOrigin⟩

/-- The six Plücker coordinates, in order `01, 02, 03, 12, 13, 23`.
The last coordinate is determined by the Klein equation. -/
def plucker (x : ChartCoordinates) : Fin 6 → ℝ
  | 0 => 1
  | 1 => x.p02
  | 2 => x.p03
  | 3 => x.p12
  | 4 => x.p13
  | 5 => x.p02 * x.p13 - x.p03 * x.p12

theorem plucker_nonneg (x : ChartCoordinates) (i : Fin 6) :
    0 ≤ plucker x i := by
  fin_cases i
  · norm_num [plucker]
  · exact x.p02_nonneg
  · exact x.p03_nonneg
  · exact x.p12_nonneg
  · exact x.p13_nonneg
  · exact x.p23_nonneg

private theorem pluckerMass_pos (x : ChartCoordinates) :
    0 < ∑ i : Fin 6, plucker x i := by
  apply Finset.sum_pos'
  · intro i hi
    exact plucker_nonneg x i
  · exact ⟨0, Finset.mem_univ _, by norm_num [plucker]⟩

/-- The image of the closed chart in the normalized positive Plücker model.
Normalization is by the sum of its six nonnegative coordinates. -/
noncomputable def normalizedPoint (x : ChartCoordinates) :
    NormalizedPositivePluckerPoint := by
  let s := ∑ i : Fin 6, plucker x i
  have hs : 0 < s := by dsimp [s]; exact pluckerMass_pos x
  refine ⟨fun i => plucker x i / s, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (plucker_nonneg x i) hs.le
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hs)
  · have hklein : plucker x 0 * plucker x 5 -
        plucker x 1 * plucker x 4 + plucker x 2 * plucker x 3 = 0 := by
      simp [plucker]
    have hs0 : s ≠ 0 := ne_of_gt hs
    change (plucker x 0 / s) * (plucker x 5 / s) -
      (plucker x 1 / s) * (plucker x 4 / s) +
      (plucker x 2 / s) * (plucker x 3 / s) = 0
    field_simp
    nlinarith [hklein]

/-! ## Support strata of the chart -/

/-- The exact support of the six Plücker coordinates of a chart point. -/
noncomputable def chartSupport (x : ChartCoordinates) : Finset (Fin 6) :=
  Finset.univ.filter fun i => 0 < plucker x i

/-- Normalization by a positive common denominator preserves exact
Plücker support, so the closed chart cells are cells of the existing
projective positive-Grassmannian model. -/
theorem normalizedPoint_support (x : ChartCoordinates) :
    positiveSupport (normalizedPoint x) = chartSupport x := by
  ext i
  simp only [positiveSupport, chartSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  dsimp [normalizedPoint]
  exact div_pos_iff_of_pos_right (pluckerMass_pos x)

/-- A chart positroid cell is the locus with one exact Plücker support. -/
def chartCell (I : Finset (Fin 6)) : Set ChartCoordinates :=
  {x | chartSupport x = I}

/-- Only nonempty support strata index the finite chart decomposition. -/
abbrev RealizedChartSupport :=
  {I : Finset (Fin 6) // ∃ x : ChartCoordinates, chartSupport x = I}

noncomputable instance realizedChartSupportFintype : Fintype RealizedChartSupport :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The support cells cover the entire closed `p₀₁ = 1` chart. -/
theorem chartCells_cover :
    (Set.univ : Set ChartCoordinates) =
      ⋃ I : RealizedChartSupport, chartCell I.1 := by
  ext x
  constructor
  · intro _
    exact Set.mem_iUnion.mpr
      ⟨⟨chartSupport x, ⟨x, rfl⟩⟩, rfl⟩
  · intro _
    exact Set.mem_univ x

/-- Distinct exact Plücker supports define disjoint cells. -/
theorem chartCells_disjoint {I J : RealizedChartSupport} (h : I ≠ J) :
    Disjoint (chartCell I.1) (chartCell J.1) := by
  rw [Set.disjoint_left]
  intro x hI hJ
  apply h
  exact Subtype.ext (hI.symm.trans hJ)

/-- The support indicators are a genuine finite partition of unity on the
closed affine chart. -/
theorem chartCell_indicator_sum (x : ChartCoordinates) :
    (∑ I : RealizedChartSupport,
      if chartSupport x = I.1 then (1 : ℝ) else 0) = 1 := by
  classical
  let I₀ : RealizedChartSupport := ⟨chartSupport x, ⟨x, rfl⟩⟩
  rw [Finset.sum_eq_single I₀]
  · simp [I₀]
  · intro I hI hne
    have hs : chartSupport x ≠ I.1 := by
      intro h
      apply hne
      exact Subtype.ext h.symm
    simp [hs]
  · intro hnot
    exact (hnot (Finset.mem_univ I₀)).elim

/-- In this chart, the two crossing bases `02` and `13` occur together exactly
when one of the exchanged basis pairs `01,23` or `03,12` occurs. -/
theorem middle_support_iff (x : ChartCoordinates) :
    (1 ∈ chartSupport x ∧ 4 ∈ chartSupport x) ↔
      (0 ∈ chartSupport x ∧ 5 ∈ chartSupport x) ∨
      (2 ∈ chartSupport x ∧ 3 ∈ chartSupport x) := by
  rw [← normalizedPoint_support x]
  exact support_plucker_exchange (normalizedPoint x)

/-! ## The positive-network top cell and its canonical form -/

/- The canonical form remains on the owner's positive-network coordinates;
this avoids assigning an unsupported dlog product to arbitrary Plücker entries. -/

/-- The existing positive-network chart embedded in the corrected closed
`p₀₁ = 1` Plücker chart. -/
def networkChartCoordinates (t : PositiveTopCoordinates) : ChartCoordinates := by
  refine ⟨t.a, t.a * t.b, t.c, t.c * (t.b + t.e),
    le_of_lt t.a_pos, le_of_lt (mul_pos t.a_pos t.b_pos), le_of_lt t.c_pos,
    le_of_lt (mul_pos t.c_pos (add_pos t.b_pos t.e_pos)), ?_⟩
  have h : t.a * (t.c * (t.b + t.e)) - (t.a * t.b) * t.c =
      t.a * t.c * t.e := by ring
  rw [h]
  exact le_of_lt (mul_pos (mul_pos t.a_pos t.c_pos) t.e_pos)

/-- The six Plücker coordinates of the positive-network chart agree exactly
with the existing `Gr(2,4)` top-cell owner. -/
theorem networkChartCoordinates_readout (t : PositiveTopCoordinates) :
    plucker (networkChartCoordinates t) = topCellPlucker t := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change t.a * (t.c * (t.b + t.e)) - (t.a * t.b) * t.c =
      t.a * t.c * t.e
    ring

/-- Every point of the positive-network chart belongs to the full-support
positroid cell of the closed affine chart. -/
theorem networkChartCoordinates_full_support (t : PositiveTopCoordinates) :
    chartSupport (networkChartCoordinates t) = Finset.univ := by
  ext i
  simp only [chartSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [networkChartCoordinates_readout]
  constructor
  · intro _
    trivial
  · intro _
    exact topCellPlucker_pos t i

/-! ## Identifying the full-support chart with the unit top-cell carrier -/

/-- The full-support locus of the closed affine Plücker chart. -/
abbrev FullSupportChartCoordinates :=
  {x : ChartCoordinates // chartSupport x = Finset.univ}

/-- Full support makes every Plücker coordinate strictly positive. -/
theorem fullSupport_plucker_pos (x : FullSupportChartCoordinates)
    (i : Fin 6) : 0 < plucker x.1 i := by
  have hi : i ∈ chartSupport x.1 := by
    rw [x.2]
    exact Finset.mem_univ i
  exact (Finset.mem_filter.mp hi).2

/-- Read a full-support closed-chart point as the existing unit-gauge
Plücker carrier. -/
def chartToUnitTopCellPoint (x : FullSupportChartCoordinates) :
    UnitTopCellPoint :=
  ⟨plucker x.1, by simp [plucker], fullSupport_plucker_pos x,
    by simp [plucker]⟩

/-- The unit-gauge Klein relation determines the final Plücker coordinate. -/
theorem unitTopCellPoint_lastCoordinate (P : UnitTopCellPoint) :
    P.coord 1 * P.coord 4 - P.coord 2 * P.coord 3 = P.coord 5 := by
  have h := P.klein
  rw [P.coord01] at h
  linarith

/-- Recover the closed-chart coordinates from a unit-gauge top-cell point. -/
noncomputable def unitTopCellPointToChart (P : UnitTopCellPoint) :
    FullSupportChartCoordinates := by
  have hlast := unitTopCellPoint_lastCoordinate P
  let y : ChartCoordinates :=
    ⟨P.coord 1, P.coord 2, P.coord 3, P.coord 4,
      le_of_lt (P.coord_pos 1), le_of_lt (P.coord_pos 2),
      le_of_lt (P.coord_pos 3), le_of_lt (P.coord_pos 4), by
        rw [hlast]
        exact le_of_lt (P.coord_pos 5)⟩
  refine ⟨y, ?_⟩
  have hread : plucker y = P.coord := by
    funext i
    fin_cases i <;> simp [y, plucker, hlast, P.coord01]
  ext i
  simpa [chartSupport, hread] using P.coord_pos i

/-- Plücker readout of the inverse chart map recovers all six coordinates. -/
theorem unitTopCellPointToChart_plucker (P : UnitTopCellPoint) :
    plucker (unitTopCellPointToChart P).1 = P.coord := by
  have hlast := unitTopCellPoint_lastCoordinate P
  funext i
  fin_cases i
  · simpa [unitTopCellPointToChart, plucker] using P.coord01.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa [unitTopCellPointToChart, plucker] using hlast

/-- The full-support part of the closed chart is equivalent to the existing
unit-gauge positive top-cell Plücker carrier. -/
noncomputable def fullSupportChartEquivUnitTopCell :
    FullSupportChartCoordinates ≃ UnitTopCellPoint where
  toFun := chartToUnitTopCellPoint
  invFun := unitTopCellPointToChart
  left_inv := by
    intro x
    apply Subtype.ext
    apply ChartCoordinates.ext <;> rfl
  right_inv := by
    intro P
    apply UnitTopCellPoint.ext
    exact unitTopCellPointToChart_plucker P

/-- The network chart followed by the closed-chart adapter agrees with the
existing positive-parameter top-cell equivalence. -/
theorem chartToUnitTopCellPoint_networkChartCoordinates
    (t : PositiveTopCoordinates) :
    chartToUnitTopCellPoint
      ⟨networkChartCoordinates t, networkChartCoordinates_full_support t⟩ =
        topCellChartEquiv t := by
  apply UnitTopCellPoint.ext
  exact networkChartCoordinates_readout t

/-- The embedded full-support cell carries the positive canonical form from
the existing network-coordinate owner. -/
theorem networkChart_topForm_positive (t : PositiveTopCoordinates) :
    0 < topCellCanonicalForm t (fun j i => if i = j then 1 else 0) := by
  rw [topCellCanonicalForm_standardFrame]
  exact topCellCanonicalDensity_pos t

end InfoGeometry.Canonical.Gr24UnitPluckerPositroidChart
