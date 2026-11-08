/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Projective.ExteriorPowerPluckerBridge
import InfoGeometry.Projective.MatrixPluckerPositiveBridge
import InfoGeometry.Topology.Gr24PositroidCanonicalForm
import InfoGeometry.Topology.PlabicBoundaryMeasurement

/-!
# Projective positive Plücker support cells for `Gr(2,4)`

## i. Overview
The carrier is the nonzero nonnegative real Klein quadric modulo positive
rescaling.  The Klein equation makes every representative a decomposable
bivector, and hence an actual two-plane Plücker vector.  Its attainable
coordinate supports give a finite disjoint projective cell decomposition.

This is the positroid decomposition at the level of projective Plücker points
and basis supports.  Each point is also shown to admit a matrix representative
whose maximal minors are nonnegative, so the support cells are genuine
rank-two positroid supports.  The full-support cell is linked to the explicit
positive chart and logarithmic canonical form in `Gr24PositroidCanonicalForm`.

## ii. Key results
- `pluckerCoordinate_scale` & `scalePlucker_klein`
- Projective positive Plücker support cell classification on `Gr(2,4)`

## iii. Table of contents
- Plücker coordinate scaling and Klein quadric homogeneity
- Projective nonnegative Klein cone and support cells

## iv. References
- Alexander Postnikov, *Total positivity, Grassmannians, and networks* (2006)

#### BUCKET 1 — Proved Kernel Content
- `pluckerCoordinate_scale`, `scalePlucker_scalePlucker`, `scalePlucker_klein`
- Projective positive Plücker support cell classification and matrix representative existence on `Gr(2,4)`
- `boundaryMeasurementPositivePluckerPoint_has_full_support`

#### BUCKET 2 — Conditional / Interface Boundaries
- Positivity support theorems hold for points in the nonnegative Klein cone with positive chart parameters.

#### BUCKET 3 — Open / Unformalized
- Higher-rank `Gr₊(k,n)` CW-complex shellability is outside this `Gr(2,4)` projective support decomposition.
-/

open scoped BigOperators

namespace InfoGeometry.Topology.Gr24ProjectivePositroidDecomposition

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.Topology.Gr24PositroidCanonicalForm

/-- The ordered six Plücker coordinates of a bivector in `Λ² ℝ⁴`. -/
def pluckerCoordinate (P : Bivector4) : Fin 6 → ℝ
  | 0 => P.p01
  | 1 => P.p02
  | 2 => P.p03
  | 3 => P.p12
  | 4 => P.p13
  | 5 => P.p23

/-- Coordinatewise scalar multiplication on the six Plücker coordinates. -/
def scalePlucker (c : ℝ) (P : Bivector4) : Bivector4 :=
  ⟨c * P.p01, c * P.p02, c * P.p03,
    c * P.p12, c * P.p13, c * P.p23⟩

/-- Coordinatewise scalar multiplication scales each Plücker coordinate by `c`. -/
@[simp] theorem pluckerCoordinate_scale (c : ℝ) (P : Bivector4) (i : Fin 6) :
    pluckerCoordinate (scalePlucker c P) i = c * pluckerCoordinate P i := by
  fin_cases i <;> rfl

/-- Iterated scalar multiplication on Plücker coordinates multiplies the scalars. -/
@[simp] theorem scalePlucker_scalePlucker (a b : ℝ) (P : Bivector4) :
    scalePlucker a (scalePlucker b P) = scalePlucker (a * b) P := by
  cases P
  apply Bivector4.ext <;> simp only [scalePlucker] <;> ring

/-- The quadratic Klein form is homogeneous of degree 2 under `scalePlucker`. -/
theorem scalePlucker_klein (c : ℝ) (P : Bivector4) :
    kleinForm (scalePlucker c P) = c ^ 2 * kleinForm P := by
  cases P
  simp [scalePlucker, kleinForm]
  ring

/-- A nonzero point of the nonnegative Klein cone. -/
def PositivePluckerRepresentative : Type :=
  { bivector : Bivector4 //
    kleinForm bivector = 0 ∧
      (∀ i, 0 ≤ pluckerCoordinate bivector i) ∧
      (∃ i, pluckerCoordinate bivector i ≠ 0) }

namespace PositivePluckerRepresentative

/-- Underlying six-coordinate Plücker bivector. -/
def bivector (P : PositivePluckerRepresentative) : Bivector4 := P.1

/-- The representative lies on the Klein quadric `kleinForm bivector = 0`. -/
lemma klein_eq_zero (P : PositivePluckerRepresentative) :
    kleinForm P.bivector = 0 := by
  dsimp only [bivector]
  exact P.2.1

/-- All six Plücker coordinates are nonnegative. -/
lemma coordinates_nonnegative (P : PositivePluckerRepresentative) (i : Fin 6) :
    0 ≤ pluckerCoordinate P.bivector i := by
  dsimp only [bivector]
  exact P.2.2.1 i

/-- At least one Plücker coordinate is nonzero. -/
lemma coordinates_nonzero (P : PositivePluckerRepresentative) :
    ∃ i, pluckerCoordinate P.bivector i ≠ 0 := by
  dsimp only [bivector]
  exact P.2.2.2

end PositivePluckerRepresentative

/-- Two representatives describe the same oriented projective plane exactly
when they differ by a strictly positive scalar. -/
def positivePluckerSetoid : Setoid PositivePluckerRepresentative where
  r P Q := ∃ c : ℝ, 0 < c ∧ Q.bivector = scalePlucker c P.bivector
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro P
      refine ⟨1, by norm_num, ?_⟩
      cases P.bivector
      simp [scalePlucker]
    · intro P Q h
      rcases h with ⟨c, hc, hPQ⟩
      refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
      rw [hPQ]
      rw [scalePlucker_scalePlucker]
      have hcancel : c⁻¹ * c = 1 := inv_mul_cancel₀ (ne_of_gt hc)
      rw [hcancel]
      cases P.bivector
      simp [scalePlucker]
    · intro P Q R hPQ hQR
      rcases hPQ with ⟨a, ha, hPQ⟩
      rcases hQR with ⟨b, hb, hQR⟩
      refine ⟨b * a, mul_pos hb ha, ?_⟩
      rw [hQR, hPQ, scalePlucker_scalePlucker]

/-- Projective positive `Gr(2,4)` points in Plücker coordinates. -/
abbrev PositiveGrassmannianPoint := Quotient positivePluckerSetoid

/-- The support pattern of one six-coordinate Plücker vector. -/
noncomputable def pluckerSupport (P : Bivector4) : Fin 6 → Bool :=
  fun i => decide (0 < pluckerCoordinate P i)

/-- Strictly positive scalar rescaling preserves the Boolean positivity support of a Plücker bivector. -/
private theorem pluckerSupport_scale (P : Bivector4)
    (c : ℝ) (hc : 0 < c) :
    pluckerSupport P = pluckerSupport (scalePlucker c P) := by
  funext i
  simp only [pluckerSupport, pluckerCoordinate_scale]
  by_cases hi : 0 < pluckerCoordinate P i
  · have hci : 0 < c * pluckerCoordinate P i := mul_pos hc hi
    simp [hi, hci]
  · have hci : ¬ 0 < c * pluckerCoordinate P i := by
      intro h
      exact hi ((mul_pos_iff_of_pos_left hc).mp h)
    simp [hi, hci]

/-- Projective support is well-defined on positive-scale equivalence classes. -/
noncomputable def projectiveSupportSignature :
    PositiveGrassmannianPoint → (Fin 6 → Bool) :=
  Quotient.lift (fun P : PositivePluckerRepresentative => pluckerSupport P.bivector) (by
    intro P Q h
    rcases h with ⟨c, hc, hPQ⟩
    rw [hPQ]
    exact pluckerSupport_scale P.bivector c hc)

/-- A projective positroid cell consists of points with one fixed Plücker
basis support. -/
def positroidCell (σ : Fin 6 → Bool) : Set PositiveGrassmannianPoint :=
  {P | projectiveSupportSignature P = σ}

/-- Only attainable support patterns index cells; this discards the empty
Boolean patterns and makes every indexed cell nonempty by construction. -/
def AttainableSupport :=
  {σ : Fin 6 → Bool // ∃ P : PositiveGrassmannianPoint,
    projectiveSupportSignature P = σ}

/-- The projective positive Grassmannian is the disjoint union of its
nonempty Plücker-support (positroid) cells. -/
theorem positroidCells_cover :
    (Set.univ : Set PositiveGrassmannianPoint) =
      ⋃ σ : AttainableSupport, positroidCell σ.1 := by
  ext P
  constructor
  · intro _
    refine Set.mem_iUnion.mpr ⟨⟨projectiveSupportSignature P, P, rfl⟩, rfl⟩
  · intro _
    exact Set.mem_univ P

/-- Different Plücker supports give disjoint projective cells. -/
theorem positroidCell_disjoint {σ τ : Fin 6 → Bool} (hστ : σ ≠ τ) :
    Disjoint (positroidCell σ) (positroidCell τ) := by
  rw [Set.disjoint_left]
  intro P hσ hτ
  exact hστ (hσ.symm.trans hτ)

/-- Every point in the projective positive Plücker carrier is represented by
an actual decomposable two-vector with nonnegative minors. -/
theorem cell_point_has_positive_plane_realization
    (P : PositivePluckerRepresentative) :
    ∃ u v : Vec4, wedgeVec4 u v = P.bivector ∧
      ∀ i, 0 ≤ pluckerCoordinate (wedgeVec4 u v) i := by
  obtain ⟨u, v, huv⟩ :=
    (kleinForm_eq_zero_iff_exists_wedge P.bivector).mp P.klein_eq_zero
  refine ⟨u, v, huv, ?_⟩
  intro i
  rw [huv]
  exact P.coordinates_nonnegative i

/-! ## Matrix positroid realization

The Klein equation is not being used as a proxy for a positroid: the next
lemmas construct an actual `2 × 4` matrix whose maximal minors are the six
Plücker coordinates.  This realizes each support cell in the usual matrix
model of the nonnegative Grassmannian. -/

/-- The matrix with the two specified vectors as rows. -/
def matrixOfRows (u v : Vec4) : Matrix (Fin 2) (Fin 4) ℝ := fun r j =>
  if r = 0 then
    (match j with
      | 0 => u I4.t
      | 1 => u I4.x
      | 2 => u I4.y
      | 3 => u I4.z)
  else
    (match j with
      | 0 => v I4.t
      | 1 => v I4.x
      | 2 => v I4.y
      | 3 => v I4.z)

/-- Extracting the two rows of `matrixOfRows u v` recovers `u` and `v`. -/
private theorem rowVec4_matrixOfRows (u v : Vec4) :
    rowVec4 (matrixOfRows u v) 0 = u ∧
      rowVec4 (matrixOfRows u v) 1 = v := by
  constructor <;> funext i <;> cases i <;> rfl

/-- The ordered maximal minors of `matrixOfRows u v` equal the two-vector Plücker coordinates `pluckerCoords u v`. -/
private theorem matrixPluckerCoords_matrixOfRows (u v : Vec4) (i : Fin 6) :
    matrixPluckerCoords (matrixOfRows u v) i = pluckerCoords u v i := by
  have h := rowVec4_matrixOfRows u v
  simp only [matrixPluckerCoords, h.1, h.2]

/-- The indexed Plücker coordinates `pluckerCoords u v i` agree with `pluckerCoordinate (wedgeVec4 u v) i`. -/
private theorem pluckerCoords_eq_bivectorCoordinate (u v : Vec4) (i : Fin 6) :
    pluckerCoords u v i = pluckerCoordinate (wedgeVec4 u v) i := by
  have h := congrArg (fun P : Bivector4 => pluckerCoordinate P)
    (pluckerCoords_eq_wedgeVec4 u v)
  have h' : (fun j : Fin 6 => pluckerCoords u v j) =
      fun j => pluckerCoordinate (wedgeVec4 u v) j := by
    funext j
    have hj := congrFun h j
    fin_cases j <;> simpa [pluckerCoordinate] using hj
  exact congrFun h' i

/-- Every projective positive Plücker representative has a concrete `2 × 4`
matrix representative whose ordered maximal minors are nonnegative and agree
with the Plücker coordinates.  In particular its support is a rank-two
positroid support, not an arbitrary Boolean support pattern. -/
theorem positivePlucker_has_matrix_positroid_realization
    (P : PositivePluckerRepresentative) :
    ∃ M : Matrix (Fin 2) (Fin 4) ℝ,
      MatrixPluckerNonnegative M ∧
      ∀ i : Fin 6,
        matrixPluckerCoords M i = pluckerCoordinate P.bivector i := by
  obtain ⟨u, v, huv⟩ :=
    (kleinForm_eq_zero_iff_exists_wedge P.bivector).mp P.klein_eq_zero
  refine ⟨matrixOfRows u v, ?_, ?_⟩
  · intro i
    rw [matrixPluckerCoords_matrixOfRows, pluckerCoords_eq_bivectorCoordinate,
      huv]
    exact P.coordinates_nonnegative i
  · intro i
    rw [matrixPluckerCoords_matrixOfRows, pluckerCoords_eq_bivectorCoordinate,
      huv]

/-! ## Matrix chart to projective Plücker carrier

The realization above constructs a matrix from a projective Plücker point.  The
following construction closes the reverse direction for the strictly positive
`2 × 4` chart: its six ordered minors form a nonzero Klein bivector, hence a
representative in the projective positive Plücker carrier. -/

/-- The bivector whose coordinates are the six ordered maximal minors of a
`2 × 4` matrix. -/
def matrixPluckerBivector (M : Matrix2x4) : Bivector4 :=
  ⟨matrixPluckerCoords M 0, matrixPluckerCoords M 1,
    matrixPluckerCoords M 2, matrixPluckerCoords M 3,
    matrixPluckerCoords M 4, matrixPluckerCoords M 5⟩

/-- Reading the `i`-th Plücker coordinate of `matrixPluckerBivector M` returns `matrixPluckerCoords M i`. -/
@[simp] theorem matrixPluckerBivector_coordinate (M : Matrix2x4) (i : Fin 6) :
    pluckerCoordinate (matrixPluckerBivector M) i = matrixPluckerCoords M i := by
  fin_cases i <;> rfl

/-- Strict positivity of the matrix chart's six ordered minors gives a
nonzero positive Klein representative with those exact coordinates. -/
def positiveMatrixPluckerRepresentative (M : Matrix2x4)
    (hM : MatrixPluckerPositive M) : PositivePluckerRepresentative := by
  refine ⟨matrixPluckerBivector M, ⟨?_, ?_, ?_⟩⟩
  · change (matrixPluckerCoords M 0 * matrixPluckerCoords M 5 -
      matrixPluckerCoords M 1 * matrixPluckerCoords M 4 +
      matrixPluckerCoords M 2 * matrixPluckerCoords M 3) = 0
    exact matrixPluckerCoords_klein_relation M
  · intro i
    rw [matrixPluckerBivector_coordinate]
    exact le_of_lt (hM i)
  · refine ⟨0, ?_⟩
    rw [matrixPluckerBivector_coordinate]
    exact ne_of_gt (hM 0)

/-- The projective Plücker point represented by a strictly positive matrix chart
point. -/
def positiveMatrixPluckerPoint (M : Matrix2x4)
    (hM : MatrixPluckerPositive M) : PositiveGrassmannianPoint :=
  Quotient.mk positivePluckerSetoid (positiveMatrixPluckerRepresentative M hM)

/-- A strict matrix-chart point maps to the full-support projective positroid
cell. -/
theorem positiveMatrixPluckerPoint_has_full_support
    (M : Matrix2x4) (hM : MatrixPluckerPositive M) :
    projectiveSupportSignature (positiveMatrixPluckerPoint M hM) = fun _ => true := by
  funext i
  change pluckerSupport (matrixPluckerBivector M) i = true
  change decide
    (0 < pluckerCoordinate (matrixPluckerBivector M) i) = true
  rw [matrixPluckerBivector_coordinate]
  exact decide_eq_true_eq.mpr (hM i)

/-- Every strictly positive point of the finite `Gr(2,4)` matrix chart determines
a representative of a projective positive Klein point, with no loss in the six
minor coordinates. -/
theorem positiveGrassmannianInterior_has_projectivePluckerRepresentative
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∃ P : PositivePluckerRepresentative,
      P.bivector = matrixPluckerBivector M ∧
      ∀ i : Fin 6,
        pluckerCoordinate P.bivector i = matrixPluckerCoords M i := by
  let hcoords := positiveGrassmannianInterior_mem_matrixPluckerPositive M hM
  let P := positiveMatrixPluckerRepresentative M hcoords
  refine ⟨P, rfl, ?_⟩
  intro i
  exact matrixPluckerBivector_coordinate M i

/-! ## Explicit positive boundary-measurement parameter family

The family in `PlabicBoundaryMeasurement` is an explicit matrix family with
positive minors.  The next declarations carry those concrete matrices into the
projective positroid carrier and expose their coordinates.  This is a matrix
family comparison; it does not supply a graph-to-matrix boundary-measurement
construction. -/

/-- The four-parameter matrix family has strictly positive ordered Plücker
coordinates whenever all four parameters are positive. -/
theorem boundaryMeasurementMatrix_matrixPluckerPositive
    {t₁ t₂ t₃ t₄ : ℝ}
    (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃) (h4 : 0 < t₄) :
    MatrixPluckerPositive
      (PlabicBoundaryMeasurement.boundaryMeasurementMatrix t₁ t₂ t₃ t₄) := by
  intro i
  fin_cases i
  · simpa [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix] using h2
  · simp [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
  · simpa [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix] using h3
  · simpa [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix] using h1
  · simpa [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix, mul_comm] using
      add_pos (mul_pos h1 h3) (mul_pos h2 h4)
  · simpa [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix] using h4

/-- Positive parameters in the explicit matrix family give a full-support
projective positive Klein point. -/
def boundaryMeasurementPositivePluckerPoint
    (t₁ t₂ t₃ t₄ : ℝ)
    (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃) (h4 : 0 < t₄) :
    PositiveGrassmannianPoint :=
  positiveMatrixPluckerPoint
    (PlabicBoundaryMeasurement.boundaryMeasurementMatrix t₁ t₂ t₃ t₄)
    (boundaryMeasurementMatrix_matrixPluckerPositive h1 h2 h3 h4)

/-- Every positive boundary-measurement chart point has full six-coordinate positivity support. -/
theorem boundaryMeasurementPositivePluckerPoint_has_full_support
    (t₁ t₂ t₃ t₄ : ℝ)
    (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃) (h4 : 0 < t₄) :
    projectiveSupportSignature
      (boundaryMeasurementPositivePluckerPoint t₁ t₂ t₃ t₄ h1 h2 h3 h4) =
        fun _ => true := by
  dsimp only [boundaryMeasurementPositivePluckerPoint]
  exact positiveMatrixPluckerPoint_has_full_support _ _

/-- Explicit six-tuple of ordered maximal minors of `boundaryMeasurementMatrix t₁ t₂ t₃ t₄`. -/
theorem boundaryMeasurementMatrix_plucker_coordinates
    (t₁ t₂ t₃ t₄ : ℝ) :
    matrixPluckerCoords
      (PlabicBoundaryMeasurement.boundaryMeasurementMatrix t₁ t₂ t₃ t₄) =
        ![t₂, 1, t₃, t₁, t₁ * t₃ + t₂ * t₄, t₄] := by
  funext i
  fin_cases i
  · simp [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
  · simp [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
  · simp [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
  · simp [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
  · simp [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix, mul_comm]
  · simp [matrixPluckerCoords_apply,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]

/-- A support cell of the projective decomposition is a genuine positroid
cell: one matrix representative has precisely that set of positive maximal
minors. -/
theorem positroidCell_has_matrix_realization
    (I : AttainableSupport) :
    ∃ M : Matrix (Fin 2) (Fin 4) ℝ,
      MatrixPluckerNonnegative M ∧
      ∃ P : PositivePluckerRepresentative,
        projectiveSupportSignature
          (Quotient.mk positivePluckerSetoid P) = I.1 ∧
        ∀ i : Fin 6,
          (matrixPluckerCoords M i > 0) ↔ I.1 i = true := by
  rcases I.2 with ⟨Q, hQ⟩
  obtain ⟨P, rfl⟩ := Quotient.exists_rep Q
  obtain ⟨M, hM_nonneg, hM_coord⟩ :=
    positivePlucker_has_matrix_positroid_realization P
  have hsig : pluckerSupport P.bivector = I.1 := by
    simpa [projectiveSupportSignature] using hQ
  refine ⟨M, hM_nonneg, P, hQ, ?_⟩
  intro i
  rw [hM_coord i]
  change (0 < pluckerCoordinate P.bivector i) ↔ I.1 i = true
  rw [← hsig]
  simp [pluckerSupport]

/-! ## Comparison with the normalized gauge-slice model -/

/-- Regard the six coordinates of a normalized positive Klein point as the
Plücker coordinates of a bivector. -/
def normalizedPointBivector (P : NormalizedPositivePluckerPoint) : Bivector4 :=
  ⟨P.coord 0, P.coord 1, P.coord 2, P.coord 3, P.coord 4, P.coord 5⟩

/-- Reading the `i`-th Plücker coordinate of `normalizedPointBivector P` returns `P.coord i`. -/
@[simp] theorem normalizedPointBivector_coordinate
    (P : NormalizedPositivePluckerPoint) (i : Fin 6) :
    pluckerCoordinate (normalizedPointBivector P) i = P.coord i := by
  fin_cases i <;> rfl

/-- Every normalized point gives a nonzero representative of the positive
Klein cone.  The sum-one gauge condition supplies nonzeroness. -/
def normalizedPointRepresentative (P : NormalizedPositivePluckerPoint) :
    PositivePluckerRepresentative := by
  refine ⟨normalizedPointBivector P, ⟨?_, ?_, ?_⟩⟩
  · exact P.klein
  · intro i
    simpa only [normalizedPointBivector_coordinate] using P.coord_nonneg i
  · by_contra h
    have h' : ¬ ∃ i : Fin 6, P.coord i ≠ 0 := by
      simpa only [normalizedPointBivector_coordinate] using h
    have hz : ∀ i : Fin 6, P.coord i = 0 := by
      intro i
      exact not_ne_iff.mp (not_exists.mp h' i)
    have hsum : (∑ i : Fin 6, P.coord i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hz i
    have hone := P.coord_sum_one
    rw [hsum] at hone
    norm_num at hone

/-- The normalized gauge slice maps canonically into the quotient by positive
projective rescaling. -/
noncomputable def normalizedPointToProjective
    (P : NormalizedPositivePluckerPoint) : PositiveGrassmannianPoint :=
  Quotient.mk positivePluckerSetoid (normalizedPointRepresentative P)

/-- The projective support signature agrees coordinate-for-coordinate with the
support used by the normalized model. -/
theorem normalizedPoint_projective_support
    (P : NormalizedPositivePluckerPoint) :
    projectiveSupportSignature (normalizedPointToProjective P) =
      fun i => decide (i ∈ positiveSupport P) := by
  funext i
  change pluckerSupport (normalizedPointRepresentative P).bivector i =
    decide (i ∈ positiveSupport P)
  simp only [pluckerSupport, pluckerCoordinate, normalizedPointRepresentative,
    normalizedPointBivector]
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  fin_cases i <;> rfl

/-- Gauge-fix a normalized full-support Plücker point by its positive `p01`
coordinate.  The result is a point of the unit top-cell chart. -/
noncomputable def normalizedFullSupportToUnitTopCell
    (P : NormalizedPositivePluckerPoint)
    (hfull : positiveSupport P = Finset.univ) : UnitTopCellPoint := by
  have hpos : ∀ i : Fin 6, 0 < P.coord i := by
    intro i
    have hi : i ∈ positiveSupport P := by rw [hfull]; simp
    exact (Finset.mem_filter.mp hi).2
  refine ⟨fun i => P.coord i / P.coord 0, ?_, ?_, ?_⟩
  · exact div_self (ne_of_gt (hpos 0))
  · intro i
    exact div_pos (hpos i) (hpos 0)
  · have h0 : P.coord 0 ≠ 0 := ne_of_gt (hpos 0)
    change (P.coord 0 / P.coord 0) * (P.coord 5 / P.coord 0) -
      (P.coord 1 / P.coord 0) * (P.coord 4 / P.coord 0) +
      (P.coord 2 / P.coord 0) * (P.coord 3 / P.coord 0) = 0
    field_simp
    nlinarith [P.klein]

/-- The `p01 = 1` chart is exhaustive on the projective full-support cell:
every normalized full-support point is represented by one positive network
coordinate tuple.  The associated canonical form is
`topCellCanonicalForm` in these coordinates. -/
theorem normalizedFullSupport_has_topCellCoordinates
    (P : NormalizedPositivePluckerPoint)
    (hfull : positiveSupport P = Finset.univ) :
    ∃! x : PositiveTopCoordinates,
      topCellChartPoint x = normalizedFullSupportToUnitTopCell P hfull := by
  let U := normalizedFullSupportToUnitTopCell P hfull
  refine ⟨topCellParameters U, (topCellChartEquiv).right_inv U, ?_⟩
  intro x hx
  exact (topCellChartEquiv).injective
    (hx.trans ((topCellChartEquiv).right_inv U).symm)

/-- The explicit positive-network chart lands in the full-support projective
positroid cell under the gauge-slice-to-quotient map. -/
theorem topCellPoint_projective_support (x : PositiveTopCoordinates) :
    projectiveSupportSignature
      (normalizedPointToProjective (topCellPoint x)) = fun _ => true := by
  rw [normalizedPoint_projective_support, topCellPoint_positive_support]
  funext i
  simp

end InfoGeometry.Topology.Gr24ProjectivePositroidDecomposition
