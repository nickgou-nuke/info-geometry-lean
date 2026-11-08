import Mathlib
import InfoGeometry.Topology.Gr24PositroidCanonicalForm
import InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm
import InfoGeometry.Canonical.Gr24PositroidChartFaceForms

/-!
# Positroid decomposition and canonical forms for `Gr(2,4)`

This module joins the actual normalized Klein-quadric support decomposition
to Mathlib alternating forms on the positive top cell and on every exact
support face of the closed positive-network chart.  The assertions remain
within their proved domains: the global support partition covers the
nonnegative Grassmannian, while lower-dimensional canonical forms are
intrinsic to the chart faces that have explicit positive-coordinate
parameterizations.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.Gr24PositroidClassificationAndCanonicalForm

open InfoGeometry.Topology.Gr24PositroidCanonicalForm
open InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm
open InfoGeometry.Canonical.Gr24PositroidChartFaceForms
open InfoGeometry.Canonical.Gr24PositroidSupport
open InfoGeometry.Canonical.Gr24PositiveTopCell
open InfoGeometry.Projective.MatrixPluckerPositiveBridge

/-! ## Global positroid decomposition -/

/-- The six-bit support of every normalized nonnegative Klein-quadric point
is nonempty and satisfies the concrete rank-two Plücker exchange relation. -/
theorem support_is_positroid (P : NormalizedPositivePluckerPoint) :
    (positiveSupport P).Nonempty ∧ IsGr24PositroidSupport (positiveSupport P) := by
  constructor
  · by_contra h
    have hzero (i : Fin 6) : P.coord i = 0 := by
      have hnot : ¬ 0 < P.coord i := by
        intro hi
        exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      exact le_antisymm (le_of_not_gt hnot) (P.coord_nonneg i)
    have hsum : (∑ i : Fin 6, P.coord i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hzero i
    have hnorm := P.coord_sum_one
    rw [hsum] at hnorm
    norm_num at hnorm
  · simpa [IsGr24PositroidSupport] using support_plucker_exchange P

/-- Every nonempty support obeying rank-two exchange is realized by an
actual normalized nonnegative Plücker point. -/
theorem every_admissible_support_is_realized (I : Finset (Fin 6))
    (hne : I.Nonempty) (hex : IsGr24PositroidSupport I) :
    ∃ P : NormalizedPositivePluckerPoint, positiveSupport P = I :=
  (positroidSupport_iff_exchange I).2 ⟨hne, hex⟩

/-- The support indicators of the actual positroid strata form a finite
partition of unity on the normalized nonnegative Grassmannian. -/
theorem positroid_stratum_partition (P : NormalizedPositivePluckerPoint) :
    ∑ I : PositroidSupport, supportStratumIndicator I P = 1 :=
  supportStrata_indicator_sum P

/-- The exact-support strata are disjoint and cover the entire normalized
nonnegative Klein quadric. -/
theorem positroid_strata_cover :
    (⋃ I : PositroidSupport, supportStratum I.1) =
      (Set.univ : Set NormalizedPositivePluckerPoint) :=
  supportStrata_cover

/-! ## The positive top cell -/

/-- The positive-network parameterization lands in the full-support
positroid cell of the normalized nonnegative Klein quadric. -/
theorem topCellPoint_has_full_support (t : PositiveTopCoordinates) :
    positiveSupport (topCellPoint t) = Finset.univ :=
  topCellPoint_positive_support t

/-- The top-cell canonical form is an actual alternating four-form whose
coefficient on the standard orientation is the `dlog` density. -/
theorem top_cell_canonical_form_value (t : PositiveParameters) :
    canonicalTopForm t coordinateFrame = dlogDensity t :=
  canonicalTopForm_coordinateFrame t

/-- Its coefficient is strictly positive throughout the positive top cell. -/
theorem top_cell_canonical_form_positive (t : PositiveParameters) :
    0 < canonicalTopForm t coordinateFrame := by
  rw [top_cell_canonical_form_value]
  exact dlogDensity_pos t

/-- The logarithmic residue on each top-cell coordinate boundary is the
product of the remaining three positive logarithmic factors. -/
theorem top_cell_boundary_residue (t : PositiveParameters) (i : Fin 4) :
    t.1 i * canonicalTopForm t coordinateFrame = boundaryResidueDensity t i :=
  canonicalTopForm_log_residue t i

/-! ## Projective descent of the top-cell chart and canonical form

The chart form above is initially expressed in a gauge-fixed matrix chart.
The following construction recovers its positive coordinates directly from
the normalized Plücker point.  In particular, the resulting canonical form
depends only on the projective Grassmannian point, not on the chosen matrix
representative.
-/

/-- The normalized Plücker vector as a function on the projective quotient.
It descends because the quotient relation is equality of normalized vectors. -/
noncomputable def projectivePluckerCoordinates : ProjectiveTNNGr24 → Fin 6 → ℝ :=
  Quotient.lift normalizedPlucker (by
    intro M N hMN
    exact hMN)

@[simp] theorem projectivePluckerCoordinates_mk (M : NonnegativeFullRankRep) :
    projectivePluckerCoordinates
      (Quotient.mk projectivePluckerSetoid M) = normalizedPlucker M := rfl

/-- The projective full-support positroid cell, viewed as a subtype of the
projective nonnegative Grassmannian. -/
abbrev ProjectiveTopCell :=
  {q : ProjectiveTNNGr24 // ∀ i, projectiveSupport q i = true}

private theorem projectiveTopCell_coords_pos (q : ProjectiveTopCell)
    (i : Fin 6) : 0 < projectivePluckerCoordinates q.1 i := by
  have h : ∀ q : ProjectiveTNNGr24,
      (∀ i, projectiveSupport q i = true) →
      ∀ i, 0 < projectivePluckerCoordinates q i := by
    intro q hq
    revert hq
    refine Quotient.inductionOn q ?_
    intro M hM i
    have hsupport : pluckerSupport M i = true := by
      simpa [projectiveSupport_mk] using hM i
    have hpos : 0 < normalizedPlucker M i := by
      simpa [pluckerSupport] using hsupport
    simpa [projectivePluckerCoordinates_mk] using hpos
  exact h q.1 q.2 i

private theorem normalizedPlucker_ratio (M : NonnegativeFullRankRep)
    (i : Fin 6) (hden : matrixPluckerCoords M.1 1 ≠ 0) :
    normalizedPlucker M i / normalizedPlucker M 1 =
      matrixPluckerCoords M.1 i / matrixPluckerCoords M.1 1 := by
  unfold normalizedPlucker
  have hmass : pluckerMass M ≠ 0 := ne_of_gt (pluckerMass_pos M)
  field_simp [hmass, hden]

/-- Coordinates on the projective top cell recovered from ratios of
normalized Plücker coordinates.  In the fixed `Δ₀₂ = 1` chart, the four
coordinates are `Δ₁₂/Δ₀₂`, `Δ₀₁/Δ₀₂`, `Δ₀₃/Δ₀₂`, and `Δ₂₃/Δ₀₂`. -/
noncomputable def projectiveTopCellCoordinates (q : ProjectiveTopCell) :
    PositiveParameters := by
  refine ⟨fun i => match i.val with
    | 0 => projectivePluckerCoordinates q.1 3 / projectivePluckerCoordinates q.1 1
    | 1 => projectivePluckerCoordinates q.1 0 / projectivePluckerCoordinates q.1 1
    | 2 => projectivePluckerCoordinates q.1 2 / projectivePluckerCoordinates q.1 1
    | _ => projectivePluckerCoordinates q.1 5 / projectivePluckerCoordinates q.1 1,
    ?_⟩
  intro i
  have hden : 0 < projectivePluckerCoordinates q.1 1 :=
    projectiveTopCell_coords_pos q 1
  fin_cases i <;>
    exact div_pos (projectiveTopCell_coords_pos q _) hden

/-- The projective top-cell canonical form: the existing alternating `dlog`
form evaluated at the scale-invariant coordinates recovered from Plücker
ratios. -/
noncomputable def projectiveTopCellCanonicalForm (q : ProjectiveTopCell) :
    ((Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ) :=
  canonicalTopForm (projectiveTopCellCoordinates q)

/-- Its coefficient on the standard orientation is strictly positive. -/
theorem projectiveTopCellCanonicalForm_positive (q : ProjectiveTopCell) :
    0 < projectiveTopCellCanonicalForm q coordinateFrame := by
  rw [projectiveTopCellCanonicalForm, canonicalTopForm_coordinateFrame]
  exact dlogDensity_pos (projectiveTopCellCoordinates q)

/-- The ratio chart recovers the original parameters on every point of the
positive-network top-cell chart.  This identifies the projective form with
the native chart form rather than merely defining another density. -/
theorem projectiveTopCellCoordinates_chart (t : PositiveParameters) :
    projectiveTopCellCoordinates
      ⟨topCellProjectivePoint t, fun i => by
        simpa [topCellProjectivePoint] using
          congrFun (topCell_support_all_true t) i⟩ = t := by
  apply Subtype.ext
  funext i
  have hread (j : Fin 6) :
      matrixPluckerCoords (chartRepresentative t).1 j =
        match j with
        | 0 => t.1 1
        | 1 => 1
        | 2 => t.1 2
        | 3 => t.1 0
        | 4 => t.1 0 * t.1 2 + t.1 1 * t.1 3
        | 5 => t.1 3 := by
    change matrixPluckerCoords (chartMatrix t) j = _
    exact chartMatrix_plucker_readout t j
  have hden : matrixPluckerCoords (chartRepresentative t).1 1 ≠ 0 := by
    rw [hread]
    norm_num
  fin_cases i
  · change projectivePluckerCoordinates (topCellProjectivePoint t) 3 /
      projectivePluckerCoordinates (topCellProjectivePoint t) 1 = t.1 0
    rw [topCellProjectivePoint, projectivePluckerCoordinates_mk,
      normalizedPlucker_ratio _ _ hden, hread, hread]
    simp
  · change projectivePluckerCoordinates (topCellProjectivePoint t) 0 /
      projectivePluckerCoordinates (topCellProjectivePoint t) 1 = t.1 1
    rw [topCellProjectivePoint, projectivePluckerCoordinates_mk,
      normalizedPlucker_ratio _ _ hden, hread, hread]
    simp
  · change projectivePluckerCoordinates (topCellProjectivePoint t) 2 /
      projectivePluckerCoordinates (topCellProjectivePoint t) 1 = t.1 2
    rw [topCellProjectivePoint, projectivePluckerCoordinates_mk,
      normalizedPlucker_ratio _ _ hden, hread, hread]
    simp
  · change projectivePluckerCoordinates (topCellProjectivePoint t) 5 /
      projectivePluckerCoordinates (topCellProjectivePoint t) 1 = t.1 3
    rw [topCellProjectivePoint, projectivePluckerCoordinates_mk,
      normalizedPlucker_ratio _ _ hden, hread, hread]
    simp

/-- On the projective point represented by the positive-network chart, the
projective canonical form agrees with the native alternating `dlog` form. -/
theorem projectiveTopCellCanonicalForm_chart (t : PositiveParameters) :
    projectiveTopCellCanonicalForm
      ⟨topCellProjectivePoint t, fun i => by
        simpa [topCellProjectivePoint] using
          congrFun (topCell_support_all_true t) i⟩ = canonicalTopForm t := by
  rw [projectiveTopCellCanonicalForm, projectiveTopCellCoordinates_chart]

/-- The full-support positroid contribution of the projective canonical form
is the chart form, and the finite sum over all realized positroid cells
recovers it by the exact support partition of unity. -/
theorem projectiveTopCellCanonicalForm_cell_sum (t : PositiveParameters) :
    (∑ σ : RealizedSupport, cellwiseTopForm σ t) =
      projectiveTopCellCanonicalForm
        ⟨topCellProjectivePoint t, fun i => by
          simpa [topCellProjectivePoint] using
            congrFun (topCell_support_all_true t) i⟩ := by
  rw [canonicalTopForm_cell_sum, ← projectiveTopCellCanonicalForm_chart]

/-! ## Intrinsic forms on the explicit closed-chart positroid faces -/

/-- Each exact-support face is an actual projective positroid stratum, via
the explicit closed-chart Plücker representative. -/
theorem chartFacePoint_lies_in_positroidCell (I : Finset (Fin 4))
    (u : FaceParameters I) :
    closedChartProjectivePoint (facePoint I u).1 ∈
      positroidCell (chartFaceGlobalPositroidCell I) :=
  facePoint_projective_mem_positroidCell I u

/-- The intrinsic alternating form on a chart positroid face evaluates to
the logarithmic density in exactly its live coordinates. -/
theorem chart_face_canonical_form_value (I : Finset (Fin 4))
    (u : FaceParameters I) :
    positroidFaceCanonicalForm I u (positroidFaceFrame I) =
      positroidFaceDensity I u :=
  positroidFaceCanonicalForm_frame I u

/-- The face form is positive on its standard orientation. -/
theorem chart_face_canonical_form_positive (I : Finset (Fin 4))
    (u : FaceParameters I) :
    0 < positroidFaceCanonicalForm I u (positroidFaceFrame I) :=
  positroidFaceCanonicalForm_frame_pos I u

/-- Iterated logarithmic residues remove precisely the selected live
coordinates and agree with the boundary-face density. -/
theorem chart_face_iterated_residue (I J : Finset (Fin 4))
    (x : ClosedTopCoordinates) (hI : x ∈ positroidChartStratum I)
    (hJI : J ⊆ I) :
    (∏ i ∈ J, x.value i) *
      positroidFaceCanonicalForm I (faceParametersOf I ⟨x, hI⟩)
        (positroidFaceFrame I) = coordinateFaceDensity x (I \ J) :=
  positroidFaceCanonicalForm_iterated_residue I J x hI hJI

/-- On the closed network chart, the sum of coefficients of all exact-support
cell forms equals the intrinsic canonical density of the unique face through
the point.  This is a coefficient assembly, not an invalid sum of forms of
different exterior degrees. -/
theorem chart_face_canonical_coefficient_sum (x : ClosedTopCoordinates) :
    stratifiedPositroidCanonicalCoefficient x = faceDlogDensity x := by
  rw [positroidCanonicalCoefficient_cell_sum,
    faceDlogDensity_eq_chartFaceCanonicalDensity]

end InfoGeometry.Canonical.Gr24PositroidClassificationAndCanonicalForm
