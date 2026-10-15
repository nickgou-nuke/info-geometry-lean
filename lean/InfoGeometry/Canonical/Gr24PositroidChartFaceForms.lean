import Mathlib
import InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm

/-!
# Differential forms on the coordinate faces of the positive `Gr(2,4)` chart

For the closed positive-network chart, a point determines its live positive
coordinates.  The corresponding stratum has precisely that many coordinates.
This file assigns the intrinsic logarithmic top form to that stratum as an
actual Mathlib exterior form, and proves the coordinate residue identity.

This is a chart-level positroid-face construction.  It does not assert that
the chosen `p01 = 1` chart covers boundary strata outside that projective
chart, nor does it identify the result with a global BCFW form.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.Gr24PositroidChartFaceForms

open InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm
open InfoGeometry.Canonical.Gr24PositiveTopCell
open InfoGeometry.Canonical.Gr24PositroidSupport

noncomputable section

/-- The coordinate tangent space of the face through `x`, indexed by its
strictly positive network coordinates. -/
abbrev FaceCoordinates (x : ClosedTopCoordinates) :=
  {i : Fin 4 // i ∈ chartCoordinateSupport x}

/-- Positive coordinates on one fixed chart face. -/
abbrev FaceParameters (I : Finset (Fin 4)) :=
  {u : {i : Fin 4 // i ∈ I} → ℝ // ∀ i, 0 < u i}

/-- The exact-support stratum in the closed network chart. -/
abbrev ChartFaceCell (I : Finset (Fin 4)) :=
  {x : ClosedTopCoordinates // chartCoordinateSupport x = I}

/-- Extend the positive coordinates of a face by zero off its support. -/
def facePoint (I : Finset (Fin 4)) (u : FaceParameters I) : ChartFaceCell I := by
  let x : ClosedTopCoordinates := {
    value := fun j => if hj : j ∈ I then u.1 ⟨j, hj⟩ else 0
    nonneg := by
      intro j
      by_cases hj : j ∈ I
      · simpa [hj] using (u.2 ⟨j, hj⟩).le
      · simp [hj]
  }
  have hs : chartCoordinateSupport x = I := by
    ext j
    simp only [chartCoordinateSupport, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hj : j ∈ I
    · simp [x, hj, u.2 ⟨j, hj⟩]
    · simp [x, hj]
  exact ⟨x, hs⟩

/-- Every finite chart face is nonempty: set each live coordinate to one. -/
noncomputable def faceParametersOne (I : Finset (Fin 4)) : FaceParameters I :=
  ⟨fun _ => 1, fun _ => by norm_num⟩

/-- The chart face parametrization is onto the exact-support stratum. -/
theorem facePoint_surjective (I : Finset (Fin 4)) (x : ChartFaceCell I) :
    ∃ u : FaceParameters I, facePoint I u = x := by
  let u : FaceParameters I := ⟨fun i => x.1.value i,
    fun i => chartCoordinateSupport_pos x.1 (x.2.symm ▸ i.2)⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  apply ClosedTopCoordinates.ext
  funext j
  by_cases hj : j ∈ I
  · simp [facePoint, u, hj]
  · have hnot : j ∉ chartCoordinateSupport x.1 := by
      rw [x.2]
      exact hj
    have hz := chartCoordinate_eq_zero_of_not_mem x.1 hnot
    simp [facePoint, u, hj, hz]

/-- Positive face coordinates recover the point uniquely on a fixed support. -/
theorem facePoint_injective (I : Finset (Fin 4)) :
    Function.Injective (facePoint I) := by
  intro u v huv
  apply Subtype.ext
  funext i
  have h := congrArg (fun x : ChartFaceCell I => x.1.value i.1) huv
  simpa [facePoint, i.2] using h

/-- Read the live coordinates of a point in a fixed-support face. -/
def faceParametersOf (I : Finset (Fin 4)) (x : ChartFaceCell I) :
    FaceParameters I :=
  ⟨fun i => x.1.value i,
    fun i => chartCoordinateSupport_pos x.1 (x.2.symm ▸ i.2)⟩

/-- The exact-support chart face is equivalent to a positive orthant with one
coordinate for each live chart coordinate. -/
noncomputable def faceChartEquiv (I : Finset (Fin 4)) :
    FaceParameters I ≃ ChartFaceCell I where
  toFun := facePoint I
  invFun := faceParametersOf I
  left_inv u := by
    apply Subtype.ext
    funext i
    simp [facePoint, faceParametersOf]
  right_inv x := by
    apply Subtype.ext
    apply ClosedTopCoordinates.ext
    funext j
    by_cases hj : j ∈ I
    · simp [facePoint, faceParametersOf, hj]
    · have hnot : j ∉ chartCoordinateSupport x.1 := by
        rw [x.2]
        exact hj
      have hz := chartCoordinate_eq_zero_of_not_mem x.1 hnot
      simp [facePoint, faceParametersOf, hj, hz]

/-- The standard oriented frame on the tangent space of a chart face. -/
def faceCoordinateFrame (x : ClosedTopCoordinates) : FaceCoordinates x → FaceCoordinates x → ℝ :=
  fun i j => if i = j then 1 else 0

/-- Intrinsic logarithmic density on a chart face.  Only positive/live
coordinates occur, so every inverse is defined. -/
noncomputable def faceDlogDensity (x : ClosedTopCoordinates) : ℝ :=
  ∏ i : FaceCoordinates x, (x.value i.1)⁻¹

/-- Reindexing the product over the face's actual tangent-coordinate subtype
recovers the finite-support chart density. -/
theorem faceDlogDensity_eq_chartFaceCanonicalDensity (x : ClosedTopCoordinates) :
    faceDlogDensity x = chartFaceCanonicalDensity x := by
  unfold faceDlogDensity chartFaceCanonicalDensity coordinateFaceDensity
  exact (Finset.prod_subtype (chartCoordinateSupport x)
    (fun _ => Iff.rfl) (fun i : Fin 4 => (x.value i)⁻¹)).symm

private theorem pos_mul_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro hab
    constructor
    · by_contra hna
      have hza : a = 0 := le_antisymm (le_of_not_gt hna) ha
      rw [hza, zero_mul] at hab
      exact (lt_irrefl 0) hab
    · by_contra hnb
      have hzb : b = 0 := le_antisymm (le_of_not_gt hnb) hb
      rw [hzb, mul_zero] at hab
      exact (lt_irrefl 0) hab
  · rintro ⟨ha, hb⟩
    exact mul_pos ha hb

private theorem pos_add_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < a + b ↔ 0 < a ∨ 0 < b := by
  constructor
  · intro hab
    by_cases hapos : 0 < a
    · exact Or.inl hapos
    · right
      have hza : a = 0 := le_antisymm (le_of_not_gt hapos) ha
      rw [hza, zero_add] at hab
      exact hab
  · rintro (h | h)
    · exact add_pos_of_pos_of_nonneg h hb
    · exact add_pos_of_nonneg_of_pos ha h

private theorem decide_eq_of_iff {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) :
    decide P = decide Q := by
  classical
  simp [h]

/-! ## The chart-face refinement of the global positroid decomposition

Each exact-support face of the closed network chart maps to an actual
projective Plücker-support cell.  This is a refinement: different network
faces can map to the same positroid support, so the theorem does not claim a
global parametrization of every positroid cell by one network face.
-/

/-- The Plücker support determined by the live coordinates of a closed
network-chart face.  The six entries follow from
`(1, x₀, x₀x₁, x₂, x₂(x₁+x₃), x₀x₂x₃)`. -/
def chartFacePositroidSupport (I : Finset (Fin 4)) : Fin 6 → Bool
  | 0 => true
  | 1 => decide (0 ∈ I)
  | 2 => decide (0 ∈ I ∧ 1 ∈ I)
  | 3 => decide (2 ∈ I)
  | 4 => decide (2 ∈ I ∧ (1 ∈ I ∨ 3 ∈ I))
  | 5 => decide (0 ∈ I ∧ 2 ∈ I ∧ 3 ∈ I)

/-- The exact Plücker support of a closed-chart point is determined by its
live network coordinates. -/
theorem closedChartProjectivePoint_support_eq_faceSupport
    (x : ClosedTopCoordinates) :
    projectiveSupport (closedChartProjectivePoint x) =
      chartFacePositroidSupport (chartCoordinateSupport x) := by
  classical
  rw [closedChartProjectivePoint_support]
  funext i
  fin_cases i
  · simp [chartFacePositroidSupport, closedChartPlucker]
  · change decide (0 < x.value 0) = decide (0 ∈ chartCoordinateSupport x)
    apply decide_eq_of_iff
    simp [chartCoordinateSupport]
  · change decide (0 < x.value 0 * x.value 1) =
      decide (0 ∈ chartCoordinateSupport x ∧ 1 ∈ chartCoordinateSupport x)
    apply decide_eq_of_iff
    rw [pos_mul_iff_of_nonneg (x.nonneg 0) (x.nonneg 1)]
    simp [chartCoordinateSupport]
  · change decide (0 < x.value 2) = decide (2 ∈ chartCoordinateSupport x)
    apply decide_eq_of_iff
    simp [chartCoordinateSupport]
  · change decide (0 < x.value 2 * (x.value 1 + x.value 3)) =
      decide (2 ∈ chartCoordinateSupport x ∧
        (1 ∈ chartCoordinateSupport x ∨ 3 ∈ chartCoordinateSupport x))
    apply decide_eq_of_iff
    rw [pos_mul_iff_of_nonneg (x.nonneg 2)
      (add_nonneg (x.nonneg 1) (x.nonneg 3)),
      pos_add_iff_of_nonneg (x.nonneg 1) (x.nonneg 3)]
    simp [chartCoordinateSupport]
  · change decide (0 < (x.value 0 * x.value 2) * x.value 3) =
      decide (0 ∈ chartCoordinateSupport x ∧ 2 ∈ chartCoordinateSupport x ∧
        3 ∈ chartCoordinateSupport x)
    apply decide_eq_of_iff
    rw [pos_mul_iff_of_nonneg (mul_nonneg (x.nonneg 0) (x.nonneg 2))
      (x.nonneg 3), pos_mul_iff_of_nonneg (x.nonneg 0) (x.nonneg 2)]
    simp [chartCoordinateSupport, and_assoc]

/-- The global projective positroid cell reached by a network-coordinate
support face. -/
noncomputable def chartFaceGlobalPositroidCell (I : Finset (Fin 4)) :
    RealizedSupport := by
  let x := (facePoint I (faceParametersOne I)).1
  refine ⟨chartFacePositroidSupport I, ?_⟩
  refine ⟨closedChartProjectivePoint x, ?_⟩
  rw [closedChartProjectivePoint_support_eq_faceSupport]
  change chartFacePositroidSupport
    (chartCoordinateSupport (facePoint I (faceParametersOne I)).1) = _
  rw [(facePoint I (faceParametersOne I)).2]

/-- Every point on a fixed exact-support chart face belongs to the global
projective positroid cell selected by its Plücker support. -/
theorem facePoint_projective_mem_positroidCell (I : Finset (Fin 4))
    (u : FaceParameters I) :
    closedChartProjectivePoint (facePoint I u).1 ∈
      positroidCell (chartFaceGlobalPositroidCell I) := by
  change projectiveSupport (closedChartProjectivePoint (facePoint I u).1) =
    (chartFaceGlobalPositroidCell I).1
  rw [closedChartProjectivePoint_support_eq_faceSupport]
  simp [chartFaceGlobalPositroidCell, (facePoint I u).2]

/-- The Plücker support of a chart face is determined by its live network
coordinates.  This is the explicit support map underlying the positroid-cell
membership theorem above. -/
theorem facePoint_projective_support (I : Finset (Fin 4))
    (u : FaceParameters I) :
    projectiveSupport (closedChartProjectivePoint (facePoint I u).1) =
      chartFacePositroidSupport I := by
  rw [closedChartProjectivePoint_support_eq_faceSupport]
  simp [(facePoint I u).2]

/-- The codimension-one chart face obtained by setting a live network
coordinate to zero.  The nonnegativity proof uses the old value away from
the selected coordinate. -/
def coordinateBoundary (x : ClosedTopCoordinates) (i : Fin 4) :
    ClosedTopCoordinates where
  value := Function.update x.value i 0
  nonneg j := by
    by_cases h : j = i
    · subst j
      simp
    · simpa [Function.update_of_ne h] using x.nonneg j

/-- Setting a live coordinate to zero removes exactly that coordinate from
the chart support.  This identifies the boundary point's exact stratum,
rather than just asserting that it lies on some boundary. -/
theorem chartCoordinateSupport_coordinateBoundary
    (x : ClosedTopCoordinates) (i : Fin 4)
    (_hi : i ∈ chartCoordinateSupport x) :
    chartCoordinateSupport (coordinateBoundary x i) =
      (chartCoordinateSupport x).erase i := by
  ext j
  simp only [chartCoordinateSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_erase]
  by_cases hji : j = i
  · subst j
    simp [coordinateBoundary, Function.update]
  · simp [coordinateBoundary, Function.update, hji]

/-- The canonical density on the newly exposed boundary face is the product
of the logarithmic factors left after removing the vanishing coordinate. -/
theorem coordinateBoundary_faceDlogDensity
    (x : ClosedTopCoordinates) (i : Fin 4)
    (hi : i ∈ chartCoordinateSupport x) :
    faceDlogDensity (coordinateBoundary x i) =
      coordinateFaceDensity x ((chartCoordinateSupport x).erase i) := by
  rw [faceDlogDensity_eq_chartFaceCanonicalDensity,
    chartFaceCanonicalDensity]
  rw [chartCoordinateSupport_coordinateBoundary x i hi]
  unfold coordinateFaceDensity
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [coordinateBoundary, Function.update, hji]

/-- The canonical top form of the chart face, as an actual alternating
`Finset.card (chartCoordinateSupport x)`-form on its tangent coordinate space.
Its coefficient is the product of the live logarithmic factors. -/
noncomputable def chartFaceCanonicalForm (x : ClosedTopCoordinates) :
    ((FaceCoordinates x → ℝ) [⋀^(FaceCoordinates x)]→ₗ[ℝ] ℝ) :=
  faceDlogDensity x • (Pi.basisFun ℝ (FaceCoordinates x)).det

/-- The coordinate frame evaluates the intrinsic face form to its dlog
density. -/
theorem chartFaceCanonicalForm_coordinateFrame (x : ClosedTopCoordinates) :
    chartFaceCanonicalForm x (faceCoordinateFrame x) = faceDlogDensity x := by
  have hframe : faceCoordinateFrame x = Pi.basisFun ℝ (FaceCoordinates x) := by
    funext i
    funext j
    simp [faceCoordinateFrame, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [chartFaceCanonicalForm, hframe]
  change faceDlogDensity x * (Pi.basisFun ℝ (FaceCoordinates x)).det
      (Pi.basisFun ℝ (FaceCoordinates x)) = faceDlogDensity x
  rw [Module.Basis.det_self]
  simp

/-- In the coordinates of its exact-support face, the genuine alternating
chart form has coefficient equal to the product of the live logarithmic
factors.  The product is over `I` only, so coordinates that vanish on the
boundary do not contribute. -/
theorem facePoint_chartFaceCanonicalForm_value (I : Finset (Fin 4))
    (u : FaceParameters I) :
    chartFaceCanonicalForm (facePoint I u).1
        (faceCoordinateFrame (facePoint I u).1) =
      coordinateFaceDensity (facePoint I u).1 I := by
  rw [chartFaceCanonicalForm_coordinateFrame]
  rw [faceDlogDensity_eq_chartFaceCanonicalDensity,
    chartFaceCanonicalDensity]
  rw [(facePoint I u).2]

/-- The face form is nonzero on its oriented coordinate frame. -/
theorem chartFaceCanonicalForm_coordinateFrame_pos (x : ClosedTopCoordinates) :
    0 < chartFaceCanonicalForm x (faceCoordinateFrame x) := by
  rw [chartFaceCanonicalForm_coordinateFrame]
  rw [faceDlogDensity_eq_chartFaceCanonicalDensity]
  exact chartFaceCanonicalDensity_pos x

/-- Taking a logarithmic residue in a live coordinate removes exactly that
coordinate from the coefficient.  This is the face-to-boundary compatibility
law for the chart's canonical forms. -/
theorem chartFaceCanonicalForm_residue_coefficient
    (x : ClosedTopCoordinates) (i : Fin 4)
    (hi : i ∈ chartCoordinateSupport x) :
    x.value i * faceDlogDensity x =
      coordinateFaceDensity x ((chartCoordinateSupport x).erase i) := by
  rw [faceDlogDensity_eq_chartFaceCanonicalDensity,
    chartFaceCanonicalDensity]
  rw [coordinateFaceDensity_factor x (chartCoordinateSupport x) hi]
  have hpos : 0 < x.value i := chartCoordinateSupport_pos x hi
  calc
    x.value i * ((x.value i)⁻¹ *
        coordinateFaceDensity x ((chartCoordinateSupport x).erase i)) =
        (x.value i * (x.value i)⁻¹) *
          coordinateFaceDensity x ((chartCoordinateSupport x).erase i) := by ring
    _ = coordinateFaceDensity x ((chartCoordinateSupport x).erase i) := by
      rw [mul_inv_cancel₀ (ne_of_gt hpos), one_mul]

/-- The residue coefficient is exactly the canonical density of the
codimension-one positroid chart face obtained by setting the live coordinate
to zero. -/
theorem chartFaceCanonicalForm_residue_eq_boundary_density
    (x : ClosedTopCoordinates) (i : Fin 4)
    (hi : i ∈ chartCoordinateSupport x) :
    x.value i * faceDlogDensity x =
      faceDlogDensity (coordinateBoundary x i) := by
  rw [chartFaceCanonicalForm_residue_coefficient x i hi,
    coordinateBoundary_faceDlogDensity x i hi]

/-! ## Actual positroid supports on two boundary faces of the chart

The positive-network coordinates are ordered `(a,b,c,e)`.  In the Plücker
readout, setting `b = 0` removes precisely `p₀₃`, and setting `e = 0`
removes precisely `p₂₃`.  These are actual projective support strata, unlike
arbitrary zeroings of coordinates in a redundant boundary parameterization.
The residue identities above describe the logarithmic chart-face densities;
the support readouts identify the projective positroid strata reached by these
two boundaries.  This section does not assert a global canonical form on every
positroid stratum.
-/

/-- The closed-network representative of a positive top-cell parameter. -/
def closedNetworkPoint (t : PositiveParameters) : ClosedTopCoordinates where
  value := t.1
  nonneg i := (t.2 i).le

/-- The positroid support of the boundary stratum `p₀₃ = 0` in the `p₀₁ = 1` chart. -/
def p03BoundarySupport : Finset (Fin 6) := {0, 1, 3, 4, 5}

/-- The positroid support of the boundary stratum `p₂₃ = 0` in the `p₀₁ = 1` chart. -/
def p23BoundarySupport : Finset (Fin 6) := {0, 1, 2, 3, 4}

/-- The positroid support reached when the network coordinate `a` vanishes.
The remaining nonzero Plücker coordinates are `p₀₁`, `p₁₂`, and `p₁₃`. -/
def aBoundarySupport : Finset (Fin 6) := {0, 3, 4}

/-- The positroid support reached when the network coordinate `c` vanishes.
The remaining nonzero Plücker coordinates are `p₀₁`, `p₀₂`, and `p₀₃`. -/
def cBoundarySupport : Finset (Fin 6) := {0, 1, 2}

/-- Plücker readout on the `a = 0` boundary of the network chart. -/
def aBoundaryPlucker (t : PositiveParameters) : Fin 6 → ℝ :=
  ![1, 0, 0, t.1 2, t.1 2 * (t.1 1 + t.1 3), 0]

/-- Plücker readout on the `c = 0` boundary of the network chart. -/
def cBoundaryPlucker (t : PositiveParameters) : Fin 6 → ℝ :=
  ![1, t.1 0, t.1 0 * t.1 1, 0, 0, 0]

/-- Plücker readout after setting the first network coordinate to zero. -/
theorem aBoundary_plucker_readout (t : PositiveParameters) :
    closedChartPlucker (coordinateBoundary (closedNetworkPoint t) 0) =
      aBoundaryPlucker t := by
  funext i
  fin_cases i <;>
    simp [closedChartPlucker, coordinateBoundary, closedNetworkPoint,
      Function.update, aBoundaryPlucker]

/-- Plücker readout after setting the third network coordinate to zero. -/
theorem cBoundary_plucker_readout (t : PositiveParameters) :
    closedChartPlucker (coordinateBoundary (closedNetworkPoint t) 2) =
      cBoundaryPlucker t := by
  funext i
  fin_cases i <;>
    simp [closedChartPlucker, coordinateBoundary, closedNetworkPoint,
      Function.update, cBoundaryPlucker]

/-- The `a = 0` boundary lies in the actual projective positroid cell with
support `{01,12,13}`. -/
theorem aBoundary_projective_support (t : PositiveParameters) :
    projectiveSupport (closedChartProjectivePoint
      (coordinateBoundary (closedNetworkPoint t) 0)) =
        fun i => decide (i ∈ aBoundarySupport) := by
  have hc := t.2 2
  rw [closedChartProjectivePoint_support, aBoundary_plucker_readout]
  funext i
  fin_cases i <;> simp [aBoundaryPlucker, aBoundarySupport, hc,
    mul_pos hc (add_pos (t.2 1) (t.2 3))]

/-- The `c = 0` boundary lies in the actual projective positroid cell with
support `{01,02,03}`. -/
theorem cBoundary_projective_support (t : PositiveParameters) :
    projectiveSupport (closedChartProjectivePoint
      (coordinateBoundary (closedNetworkPoint t) 2)) =
        fun i => decide (i ∈ cBoundarySupport) := by
  have ha := t.2 0
  rw [closedChartProjectivePoint_support, cBoundary_plucker_readout]
  funext i
  fin_cases i <;> simp [cBoundaryPlucker, cBoundarySupport, ha,
    mul_pos ha (t.2 1)]

/-- The top-form residue at `a = 0` is the logarithmic density of that
three-coordinate positroid boundary. -/
theorem a_residue_is_boundary_density (t : PositiveParameters) :
    t.1 0 * faceDlogDensity (closedNetworkPoint t) =
      faceDlogDensity (coordinateBoundary (closedNetworkPoint t) 0) := by
  change (closedNetworkPoint t).value 0 *
      faceDlogDensity (closedNetworkPoint t) = _
  apply chartFaceCanonicalForm_residue_eq_boundary_density
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2 0⟩

/-- The top-form residue at `c = 0` is the logarithmic density of that
three-coordinate positroid boundary. -/
theorem c_residue_is_boundary_density (t : PositiveParameters) :
    t.1 2 * faceDlogDensity (closedNetworkPoint t) =
      faceDlogDensity (coordinateBoundary (closedNetworkPoint t) 2) := by
  change (closedNetworkPoint t).value 2 *
      faceDlogDensity (closedNetworkPoint t) = _
  apply chartFaceCanonicalForm_residue_eq_boundary_density
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2 2⟩

/-- Plücker readout on the `b = 0` boundary of the network chart. -/
def p03BoundaryPlucker (t : PositiveParameters) : Fin 6 → ℝ :=
  ![1, t.1 0, 0, t.1 2, t.1 2 * t.1 3, t.1 0 * t.1 2 * t.1 3]

/-- Plücker readout on the `e = 0` boundary of the network chart. -/
def p23BoundaryPlucker (t : PositiveParameters) : Fin 6 → ℝ :=
  ![1, t.1 0, t.1 0 * t.1 1, t.1 2, t.1 2 * t.1 1, 0]

theorem bBoundary_plucker_readout (t : PositiveParameters) :
    closedChartPlucker (coordinateBoundary (closedNetworkPoint t) 1) =
      p03BoundaryPlucker t := by
  funext i
  fin_cases i <;>
    simp [closedChartPlucker, coordinateBoundary, closedNetworkPoint,
      Function.update, p03BoundaryPlucker]

theorem eBoundary_plucker_readout (t : PositiveParameters) :
    closedChartPlucker (coordinateBoundary (closedNetworkPoint t) 3) =
      p23BoundaryPlucker t := by
  funext i
  fin_cases i <;>
    simp [closedChartPlucker, coordinateBoundary, closedNetworkPoint,
      Function.update, p23BoundaryPlucker]

/-- Setting the network coordinate `b` to zero lands in the actual
projective positroid cell whose only missing Plücker coordinate is `p₀₃`. -/
theorem bBoundary_projective_support (t : PositiveParameters) :
    projectiveSupport (closedChartProjectivePoint
      (coordinateBoundary (closedNetworkPoint t) 1)) =
        fun i => decide (i ∈ p03BoundarySupport) := by
  have ha := t.2 0
  have hb := t.2 1
  have hc := t.2 2
  have he := t.2 3
  rw [closedChartProjectivePoint_support]
  rw [bBoundary_plucker_readout]
  funext i
  fin_cases i <;> simp [p03BoundaryPlucker, p03BoundarySupport, ha, hc, he]

/-- Setting the network coordinate `e` to zero lands in the actual
projective positroid cell whose only missing Plücker coordinate is `p₂₃`. -/
theorem eBoundary_projective_support (t : PositiveParameters) :
    projectiveSupport (closedChartProjectivePoint
      (coordinateBoundary (closedNetworkPoint t) 3)) =
        fun i => decide (i ∈ p23BoundarySupport) := by
  have ha := t.2 0
  have hb := t.2 1
  have hc := t.2 2
  rw [closedChartProjectivePoint_support]
  rw [eBoundary_plucker_readout]
  funext i
  fin_cases i <;> simp [p23BoundaryPlucker, p23BoundarySupport, ha, hb, hc]

/-- The top-cell logarithmic residue at `b = 0` is the logarithmic density of
the chart face whose projective support omits `p₀₃`. -/
theorem b_residue_is_p03_boundary_density (t : PositiveParameters) :
    t.1 1 * faceDlogDensity (closedNetworkPoint t) =
      faceDlogDensity (coordinateBoundary (closedNetworkPoint t) 1) := by
  change (closedNetworkPoint t).value 1 * faceDlogDensity (closedNetworkPoint t) = _
  apply chartFaceCanonicalForm_residue_eq_boundary_density
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2 1⟩

/-- The top-cell logarithmic residue at `e = 0` is the logarithmic density of
the chart face whose projective support omits `p₂₃`. -/
theorem e_residue_is_p23_boundary_density (t : PositiveParameters) :
    t.1 3 * faceDlogDensity (closedNetworkPoint t) =
      faceDlogDensity (coordinateBoundary (closedNetworkPoint t) 3) := by
  change (closedNetworkPoint t).value 3 * faceDlogDensity (closedNetworkPoint t) = _
  apply chartFaceCanonicalForm_residue_eq_boundary_density
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2 3⟩

/-! ## A complete stratification and intrinsic forms for this network chart

The global projective support owner partitions the whole nonnegative
Grassmannian.  The fixed network chart has a finer, explicit decomposition:
one stratum for each subset of its four nonnegative coordinates.  Each such
stratum is parametrized by its positive coordinates and carries its own
top-degree logarithmic form.  The forms have different degrees, as they
should; this section does not add them as if they were ambient four-forms.
-/

/-- The exact-support stratum with live network coordinates `I`. -/
def positroidChartStratum (I : Finset (Fin 4)) : Set ClosedTopCoordinates :=
  {x | chartCoordinateSupport x = I}

/-- Indicator of a fixed-support chart stratum. -/
noncomputable def chartStratumIndicator (I : Finset (Fin 4))
    (x : ClosedTopCoordinates) : ℝ := by
  classical
  exact if x ∈ positroidChartStratum I then 1 else 0

/-- The chart strata cover every point: its live-coordinate support is one of
the sixteen subsets of the four network coordinates. -/
theorem chartStratum_cover (x : ClosedTopCoordinates) :
    ∃ I : Finset (Fin 4), x ∈ positroidChartStratum I :=
  ⟨chartCoordinateSupport x, rfl⟩

/-- Distinct exact-support strata are disjoint. -/
theorem chartStrata_pairwise_disjoint {I J : Finset (Fin 4)} (hIJ : I ≠ J) :
    Disjoint (positroidChartStratum I) (positroidChartStratum J) := by
  rw [Set.disjoint_left]
  intro x hxI hxJ
  exact hIJ (hxI.symm.trans hxJ)

/-- The finite indicator partition of unity for all exact-support strata of
the closed four-coordinate network chart. -/
theorem chartStratum_indicator_sum (x : ClosedTopCoordinates) :
    (∑ I : Finset (Fin 4), chartStratumIndicator I x) = 1 := by
  classical
  let I₀ := chartCoordinateSupport x
  have hterm (I : Finset (Fin 4)) :
      chartStratumIndicator I x = if I = I₀ then 1 else 0 := by
    by_cases hI : I = I₀
    · subst I
      simp [chartStratumIndicator, positroidChartStratum, I₀]
    · have hx : x ∉ positroidChartStratum I := by
        intro hx
        exact hI (hx.symm.trans rfl)
      simp [chartStratumIndicator, hx, hI]
  calc
    (∑ I : Finset (Fin 4), chartStratumIndicator I x) =
        ∑ I : Finset (Fin 4), if I = I₀ then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      exact hterm I
    _ = 1 := by simp

/-- Coordinates internal to a single positroid chart stratum. -/
abbrev PositroidFaceCoordinates (I : Finset (Fin 4)) :=
  {i : Fin 4 // i ∈ I}

/-- The intrinsic logarithmic density on the positive orthant parametrizing a
fixed-support chart stratum. -/
noncomputable def positroidFaceDensity (I : Finset (Fin 4))
    (u : FaceParameters I) : ℝ :=
  ∏ i : PositroidFaceCoordinates I, (u.1 i)⁻¹

/-- The intrinsic canonical form of a chart positroid stratum, of degree
`|I|`.  Its coefficients are the logarithmic volume form in precisely the
positive coordinates of that stratum. -/
noncomputable def positroidFaceCanonicalForm (I : Finset (Fin 4))
    (u : FaceParameters I) :
    ((PositroidFaceCoordinates I → ℝ)
      [⋀^(PositroidFaceCoordinates I)]→ₗ[ℝ] ℝ) :=
  positroidFaceDensity I u •
    (Pi.basisFun ℝ (PositroidFaceCoordinates I)).det

/-- The intrinsic form at a closed-chart point is exactly the canonical form
of its actual positroid face, with coordinates read from that point.  This
identifies the variable-dimensional exterior form with the fixed-support
construction; it is stronger than an equality of scalar densities. -/
theorem chartFaceCanonicalForm_eq_positroidFaceCanonicalForm
    (x : ClosedTopCoordinates) :
    chartFaceCanonicalForm x =
      positroidFaceCanonicalForm (chartCoordinateSupport x)
        (faceParametersOf (chartCoordinateSupport x)
          ⟨x, rfl⟩) := by
  unfold chartFaceCanonicalForm positroidFaceCanonicalForm
  congr 1

/-- The standard oriented frame on the fixed-support coordinate space. -/
def positroidFaceFrame (I : Finset (Fin 4)) :
    PositroidFaceCoordinates I → PositroidFaceCoordinates I → ℝ :=
  fun i j => if i = j then 1 else 0

/-- The intrinsic face form evaluates to its dlog density on the oriented
coordinate frame. -/
theorem positroidFaceCanonicalForm_frame (I : Finset (Fin 4))
    (u : FaceParameters I) :
    positroidFaceCanonicalForm I u (positroidFaceFrame I) =
      positroidFaceDensity I u := by
  have hframe : positroidFaceFrame I =
      Pi.basisFun ℝ (PositroidFaceCoordinates I) := by
    funext i
    funext j
    simp [positroidFaceFrame, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [positroidFaceCanonicalForm, hframe]
  change positroidFaceDensity I u *
      (Pi.basisFun ℝ (PositroidFaceCoordinates I)).det
        (Pi.basisFun ℝ (PositroidFaceCoordinates I)) = _
  rw [Module.Basis.det_self]
  simp

/-- Every positroid chart face has a strictly positive canonical-form
coefficient on its positive coordinate domain. -/
theorem positroidFaceDensity_pos (I : Finset (Fin 4))
    (u : FaceParameters I) : 0 < positroidFaceDensity I u := by
  unfold positroidFaceDensity
  apply Finset.prod_pos
  intro i hi
  exact inv_pos.mpr (u.2 i)

/-- The face form therefore has a strictly positive value on its canonical
orientation. -/
theorem positroidFaceCanonicalForm_frame_pos (I : Finset (Fin 4))
    (u : FaceParameters I) :
    0 < positroidFaceCanonicalForm I u (positroidFaceFrame I) := by
  rw [positroidFaceCanonicalForm_frame]
  exact positroidFaceDensity_pos I u

/-- The iterated logarithmic residue of the canonical form on an exact
support face is the canonical density on the face obtained by deleting the
residue coordinates.  The left side evaluates the actual exterior form on its
oriented frame; it is not a sum of scalar representatives of forms of
different degrees. -/
theorem positroidFaceCanonicalForm_iterated_residue
    (I J : Finset (Fin 4)) (x : ClosedTopCoordinates)
    (hI : x ∈ positroidChartStratum I) (hJI : J ⊆ I) :
    (∏ i ∈ J, x.value i) *
      positroidFaceCanonicalForm I
        (faceParametersOf I ⟨x, hI⟩) (positroidFaceFrame I) =
      coordinateFaceDensity x (I \ J) := by
  have hpos : ∀ i ∈ I, 0 < x.value i := by
    intro i hi
    exact chartCoordinateSupport_pos x (hI ▸ hi)
  have hdensity :
      positroidFaceDensity I (faceParametersOf I ⟨x, hI⟩) =
        coordinateFaceDensity x I := by
    change (∏ i : {j : Fin 4 // j ∈ I}, (x.value i.1)⁻¹) =
      ∏ i ∈ I, (x.value i)⁻¹
    exact (Finset.prod_subtype I (fun _ => Iff.rfl)
      (fun i : Fin 4 => (x.value i)⁻¹)).symm
  rw [positroidFaceCanonicalForm_frame, hdensity]
  exact coordinateFaceDensity_iterated_residue x I J hJI hpos

/-- The fixed-support chart parametrization realizes the corresponding
projective positroid cell, so the face forms above are attached to actual
Plücker support strata rather than Boolean labels alone. -/
theorem facePoint_mem_globalPositroidCell (I : Finset (Fin 4))
    (u : FaceParameters I) :
    closedChartProjectivePoint (facePoint I u).1 ∈
      positroidCell (chartFaceGlobalPositroidCell I) :=
  facePoint_projective_mem_positroidCell I u

/-! ## The chart-face canonical-form atlas over global positroid cells

The global projective support decomposition and the exact-support chart
decomposition are compatible: over the chosen `p01 = 1` network chart, each
point of a global positroid cell belongs to exactly one chart face.  The
intrinsic form on that face is `positroidFaceCanonicalForm`; its degree is
the dimension of the face, so forms on different strata are not added as
ambient forms of a fixed degree.
-/

/-- Chart faces lying over one actual projective positroid support cell. -/
abbrev ChartFacesOver (σ : RealizedSupport) :=
  {I : Finset (Fin 4) // chartFaceGlobalPositroidCell I = σ}

/-- Every point of a global positroid cell that lies in this network chart
belongs to exactly one chart face over that same global cell.  This is the
local canonical-form atlas statement: the unique face carries the intrinsic
form `positroidFaceCanonicalForm I u` on its positive-coordinate domain. -/
theorem closedChartPoint_unique_face_over_positroidCell
    (σ : RealizedSupport) (x : ClosedTopCoordinates)
    (hx : closedChartProjectivePoint x ∈ positroidCell σ) :
    ∃! I : ChartFacesOver σ, x ∈ positroidChartStratum I.1 := by
  let I₀ := chartCoordinateSupport x
  have hsupport : chartFacePositroidSupport I₀ = σ.1 := by
    have hchart := closedChartProjectivePoint_support_eq_faceSupport x
    change projectiveSupport (closedChartProjectivePoint x) = σ.1 at hx
    exact hchart.symm.trans hx
  have hface : chartFaceGlobalPositroidCell I₀ = σ := by
    apply Subtype.ext
    exact hsupport
  refine ⟨⟨I₀, hface⟩, ?_, ?_⟩
  · change chartCoordinateSupport x = I₀
    rfl
  · intro I hI
    apply Subtype.ext
    change chartCoordinateSupport x = I.1 at hI
    exact hI.symm

/-! ## Canonical coefficient assembled over the exact positroid faces

Each face has its own exterior degree.  The coefficient-level assembly below
therefore sums the values of the intrinsic face forms on their respective
coordinate frames; it does not coerce the forms into one ambient degree.
-/

/-- The canonical coefficient contributed by support `I` at a closed-chart
point.  It vanishes off that exact face and otherwise is the coefficient of
the intrinsic face form already defined above. -/
noncomputable def positroidCellCanonicalCoefficient (I : Finset (Fin 4))
    (x : ClosedTopCoordinates) : ℝ := by
  classical
  exact if h : x ∈ positroidChartStratum I then
    positroidFaceCanonicalForm I (faceParametersOf I ⟨x, h⟩)
      (positroidFaceFrame I)
  else 0

/-- On its own exact-support stratum, the cell coefficient is the positive
logarithmic density of that cell's canonical form. -/
theorem positroidCellCanonicalCoefficient_on_cell
    (I : Finset (Fin 4)) (x : ClosedTopCoordinates)
    (hx : x ∈ positroidChartStratum I) :
    positroidCellCanonicalCoefficient I x =
      positroidFaceDensity I (faceParametersOf I ⟨x, hx⟩) := by
  rw [positroidCellCanonicalCoefficient, dif_pos hx,
    positroidFaceCanonicalForm_frame]

/-- The canonical coefficient assembly on the closed network chart: at each
point exactly one realized face contributes, and the result is the logarithmic
density on its actual tangent-coordinate support. -/
noncomputable def stratifiedPositroidCanonicalCoefficient
    (x : ClosedTopCoordinates) : ℝ :=
  ∑ I : Finset (Fin 4), positroidCellCanonicalCoefficient I x

/-- Cellwise canonical coefficients assemble to the density of the unique
face containing the point. -/
theorem positroidCanonicalCoefficient_cell_sum (x : ClosedTopCoordinates) :
    stratifiedPositroidCanonicalCoefficient x = chartFaceCanonicalDensity x := by
  classical
  let I₀ := chartCoordinateSupport x
  have hterm (I : Finset (Fin 4)) :
      positroidCellCanonicalCoefficient I x =
        if I = I₀ then chartFaceCanonicalDensity x else 0 := by
    by_cases hI : I = I₀
    · subst I
      have hx : x ∈ positroidChartStratum I₀ := rfl
      rw [positroidCellCanonicalCoefficient_on_cell I₀ x hx]
      have hdensity :
          positroidFaceDensity I₀ (faceParametersOf I₀ ⟨x, hx⟩) =
            chartFaceCanonicalDensity x := by
        unfold positroidFaceDensity faceParametersOf chartFaceCanonicalDensity
          coordinateFaceDensity
        exact (Finset.prod_subtype I₀ (fun _ => Iff.rfl)
          (fun i : Fin 4 => (x.value i)⁻¹)).symm
      simp [hdensity]
    · have hx : x ∉ positroidChartStratum I := by
        intro hx
        exact hI (hx.symm.trans rfl)
      simp [positroidCellCanonicalCoefficient, hx, hI]
  rw [stratifiedPositroidCanonicalCoefficient]
  calc
    (∑ I : Finset (Fin 4), positroidCellCanonicalCoefficient I x) =
        ∑ I : Finset (Fin 4), if I = I₀ then chartFaceCanonicalDensity x else 0 := by
      apply Finset.sum_congr rfl
      intro I _
      exact hterm I
    _ = chartFaceCanonicalDensity x := by simp

/-- The assembled coefficient is strictly positive; this follows from the
positive coordinates on the unique face, including the zero-dimensional face
where the empty product is one. -/
theorem stratifiedPositroidCanonicalCoefficient_pos (x : ClosedTopCoordinates) :
    0 < stratifiedPositroidCanonicalCoefficient x := by
  rw [positroidCanonicalCoefficient_cell_sum]
  exact chartFaceCanonicalDensity_pos x

/-! ## Canonical forms grouped by the global projective positroid support

The previous coefficient sum is indexed by the four network coordinates.  A
chart face can map to a global positroid support shared by other chart faces,
so we also assemble the actual variable-degree exterior forms by their global
support.  At a fixed chart point all terms have the same tangent space; the
support indicator selects its unique projective positroid cell.
-/

/-- The intrinsic chart-face exterior form, assigned to the global projective
positroid cell containing the chart point and zero on all other cells.  The
form has the degree of the point's exact chart face. -/
noncomputable def globalPositroidCellCanonicalForm (σ : RealizedSupport)
    (x : ClosedTopCoordinates) :
    ((FaceCoordinates x → ℝ) [⋀^(FaceCoordinates x)]→ₗ[ℝ] ℝ) :=
  cellIndicator σ (closedChartProjectivePoint x) • chartFaceCanonicalForm x

/-- On its actual global support cell, the cellwise canonical form is the
intrinsic chart-face form. -/
theorem globalPositroidCellCanonicalForm_on_cell
    (σ : RealizedSupport) (x : ClosedTopCoordinates)
    (hx : closedChartProjectivePoint x ∈ positroidCell σ) :
    globalPositroidCellCanonicalForm σ x = chartFaceCanonicalForm x := by
  simp [globalPositroidCellCanonicalForm, cellIndicator, hx]

/-- A global positroid cell not containing the chart point contributes the
zero form. -/
theorem globalPositroidCellCanonicalForm_off_cell
    (σ : RealizedSupport) (x : ClosedTopCoordinates)
    (hx : closedChartProjectivePoint x ∉ positroidCell σ) :
    globalPositroidCellCanonicalForm σ x = 0 := by
  simp [globalPositroidCellCanonicalForm, cellIndicator, hx]

/-- The chart-restricted canonical form is the finite sum of its
global-positroid-cell contributions.  This is an equality of actual
alternating forms, not only of their scalar densities. -/
theorem chartFaceCanonicalForm_globalPositroidCell_sum
    (x : ClosedTopCoordinates) :
    (∑ σ : RealizedSupport, globalPositroidCellCanonicalForm σ x) =
      chartFaceCanonicalForm x := by
  classical
  unfold globalPositroidCellCanonicalForm
  rw [← Finset.sum_smul, positroid_cell_indicator_sum]
  simp

/-- Evaluating the global-cell form sum on the oriented face frame recovers
the positive logarithmic density of the unique face containing the point. -/
theorem chartFaceCanonicalForm_globalPositroidCell_sum_value
    (x : ClosedTopCoordinates) :
    (∑ σ : RealizedSupport, globalPositroidCellCanonicalForm σ x)
      (faceCoordinateFrame x) = chartFaceCanonicalDensity x := by
  rw [chartFaceCanonicalForm_globalPositroidCell_sum,
    chartFaceCanonicalForm_coordinateFrame,
    faceDlogDensity_eq_chartFaceCanonicalDensity]

end

end InfoGeometry.Canonical.Gr24PositroidChartFaceForms
