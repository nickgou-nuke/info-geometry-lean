import Mathlib
import InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm

/-!
# Canonical forms on the non-simplex positroid cells of `Gr(2,4)`

For supports containing the Plücker pair `02,13`, the Klein relation is not
termwise zero. In the projective chart `p02 = 1`, it solves for `p13` as
`p01*p23 + p03*p12`. The remaining supported coordinates are positive
coordinates on an open orthant. This file gives that chart its actual
alternating logarithmic top form and proves the solved-coordinate identity.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.Gr24KleinMiddlePositroidForms

open InfoGeometry.Topology.Gr24PositroidCanonicalForm
open InfoGeometry.Canonical.Gr24PositroidSupport
open InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm

noncomputable section

/-- A realized positroid support containing the middle Plücker pair `02,13`.
The pair is the projective pivot and the dependent Klein coordinate. -/
abbrev MiddleKleinSupport :=
  {I : InfoGeometry.Topology.Gr24PositroidCanonicalForm.PositroidSupport //
    (1 : Fin 6) ∈ I.1.1 ∧ (4 : Fin 6) ∈ I.1.1}

/-- Independent coordinates in the projective chart `p02 = 1`. -/
abbrev MiddleCellCoordinates (I : MiddleKleinSupport) :=
  {i : Fin 6 // i ∈ I.1.1 ∧ i ≠ 1 ∧ i ≠ 4}

/-- A point in the exact-support positroid cell with both middle Plücker
coordinates nonzero. -/
abbrev MiddleCellPoint (I : MiddleKleinSupport) :=
  {P : NormalizedPositivePluckerPoint // positiveSupport P = I.1.1}

/-- The chart coordinates are the supported Plücker ratios relative to the
positive pivot `p02`. -/
noncomputable def middleCellChartCoordinates (I : MiddleKleinSupport)
    (P : MiddleCellPoint I) : MiddleCellCoordinates I → ℝ :=
  fun i => P.1.coord i.1 / P.1.coord 1

theorem middleCellChartCoordinates_pos (I : MiddleKleinSupport)
    (P : MiddleCellPoint I) (i : MiddleCellCoordinates I) :
    0 < middleCellChartCoordinates I P i := by
  unfold middleCellChartCoordinates
  apply div_pos
  · exact supportStratum_coordinate_pos P.2 i.2.1
  · exact supportStratum_coordinate_pos P.2 I.2.1

/-- In the `p02 = 1` gauge, the Klein equation determines `p13` from the
four outer Plücker coordinates. -/
theorem middleCell_p13_ratio_eq_outer_products
    (I : MiddleKleinSupport) (P : MiddleCellPoint I) :
    P.1.coord 4 / P.1.coord 1 =
      (P.1.coord 0 / P.1.coord 1) * (P.1.coord 5 / P.1.coord 1) +
        (P.1.coord 2 / P.1.coord 1) * (P.1.coord 3 / P.1.coord 1) := by
  have hpivot : P.1.coord 1 ≠ 0 :=
    ne_of_gt (supportStratum_coordinate_pos P.2 I.2.1)
  field_simp [hpivot]
  nlinarith [P.1.klein]

/-- The independent positive coordinates form the chart's oriented frame. -/
noncomputable def middleCellFrame (I : MiddleKleinSupport) :
    MiddleCellCoordinates I → (MiddleCellCoordinates I → ℝ) :=
  Pi.basisFun ℝ (MiddleCellCoordinates I)

/-- Intrinsic logarithmic top form on a middle-pair positroid cell, expressed
in its independent positive Plücker-ratio coordinates. -/
noncomputable def middleCellCanonicalForm (I : MiddleKleinSupport)
    (P : MiddleCellPoint I) :
    ((MiddleCellCoordinates I → ℝ)
      [⋀^(MiddleCellCoordinates I)]→ₗ[ℝ] ℝ) := by
  classical
  let density : ℝ := ∏ i : MiddleCellCoordinates I,
    (middleCellChartCoordinates I P i)⁻¹
  exact density • (Pi.basisFun ℝ (MiddleCellCoordinates I)).det

/-- On its chart frame, the canonical form evaluates to the product of the
logarithmic factors of the independent coordinates. -/
theorem middleCellCanonicalForm_frame (I : MiddleKleinSupport)
    (P : MiddleCellPoint I) :
    middleCellCanonicalForm I P (middleCellFrame I) =
      ∏ i : MiddleCellCoordinates I,
        (middleCellChartCoordinates I P i)⁻¹ := by
  classical
  unfold middleCellCanonicalForm middleCellFrame
  change (∏ i : MiddleCellCoordinates I,
      (middleCellChartCoordinates I P i)⁻¹) *
      (Pi.basisFun ℝ (MiddleCellCoordinates I)).det
        (Pi.basisFun ℝ (MiddleCellCoordinates I)) = _
  rw [Module.Basis.det_self]
  simp

/-- The canonical coefficient is strictly positive on every point of the
middle-pair positroid cell. -/
theorem middleCellCanonicalForm_frame_pos (I : MiddleKleinSupport)
    (P : MiddleCellPoint I) :
    0 < middleCellCanonicalForm I P (middleCellFrame I) := by
  rw [middleCellCanonicalForm_frame]
  apply Finset.prod_pos
  intro i hi
  exact inv_pos.mpr (middleCellChartCoordinates_pos I P i)

/-- Every realized `Gr(2,4)` support is either a Klein-term-free simplex
support, or contains the middle pair and belongs to this chart family. -/
theorem positroidSupport_simplex_or_middle
    (I : InfoGeometry.Topology.Gr24PositroidCanonicalForm.PositroidSupport) :
    simplexPositroidSupport I.1 ∨
      ((1 : Fin 6) ∈ I.1 ∧ (4 : Fin 6) ∈ I.1) := by
  by_cases hmiddle : (1 : Fin 6) ∈ I.1 ∧ (4 : Fin 6) ∈ I.1
  · exact Or.inr hmiddle
  · left
    have hex := positroidSupport_exchange_characterization I
    intro k hpair
    fin_cases k
    · have hout : (0 : Fin 6) ∈ I.1 ∧ (5 : Fin 6) ∈ I.1 :=
        ⟨hpair (by simp [kleinComplementaryPairs]),
          hpair (by simp [kleinComplementaryPairs])⟩
      exact hmiddle (hex.mpr (Or.inl hout))
    · have hout : (1 : Fin 6) ∈ I.1 ∧ (4 : Fin 6) ∈ I.1 :=
        ⟨hpair (by simp [kleinComplementaryPairs]),
          hpair (by simp [kleinComplementaryPairs])⟩
      exact hmiddle hout
    · have hout : (2 : Fin 6) ∈ I.1 ∧ (3 : Fin 6) ∈ I.1 :=
        ⟨hpair (by simp [kleinComplementaryPairs]),
          hpair (by simp [kleinComplementaryPairs])⟩
      exact hmiddle (hex.mpr (Or.inr hout))

end

end InfoGeometry.Canonical.Gr24KleinMiddlePositroidForms
