import Mathlib
import InfoGeometry.Topology.Gr24PositroidCanonicalForm
import InfoGeometry.Canonical.Gr24PositroidSupportDecomposition
import InfoGeometry.Canonical.Gr24PositiveTopCellCanonicalForm

/-!
# The finite positroid partition and the `Gr(2,4)` top-cell form

The nonnegative projective `Gr(2,4)` carrier is partitioned by the realized
supports of its six normalized Plücker coordinates.  This file makes that
partition an explicit finite indicator identity and connects its all-positive
stratum to the existing four-coordinate logarithmic canonical form.

The canonical form is a form on the four-dimensional top cell.  The lower
positroid strata have smaller dimensions and are not assigned copies of that
top-degree form here.
-/

namespace InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm

open InfoGeometry.Canonical.Gr24PositroidSupport
open InfoGeometry.Canonical.Gr24PositiveTopCell
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.Topology.Gr24PositroidCanonicalForm

/-- Indicator of one realized positroid support stratum. -/
noncomputable def cellIndicator (σ : RealizedSupport)
    (q : ProjectiveTNNGr24) : ℝ := by
  classical
  exact if h : q ∈ positroidCell σ then 1 else 0

/-- Every projective nonnegative `Gr(2,4)` point has a unique realized
Plücker support, hence belongs to exactly one positroid stratum. -/
theorem existsUnique_positroidCell (q : ProjectiveTNNGr24) :
    ∃! σ : RealizedSupport, q ∈ positroidCell σ := by
  refine ⟨⟨projectiveSupport q, ⟨q, rfl⟩⟩, ?_, ?_⟩
  · rfl
  · intro σ hσ
    apply Subtype.ext
    exact hσ.symm

/-- Finite partition-of-unity identity for the positroid decomposition:
the sum of the indicators of all realized support cells is one at every point.
-/
theorem positroid_cell_indicator_sum (q : ProjectiveTNNGr24) :
    (∑ σ : RealizedSupport, cellIndicator σ q) = 1 := by
  classical
  obtain ⟨σ₀, hσ₀, hunique⟩ := existsUnique_positroidCell q
  have hterm (σ : RealizedSupport) :
      cellIndicator σ q = if σ = σ₀ then 1 else 0 := by
    by_cases hσ : σ = σ₀
    · subst σ
      change projectiveSupport q = σ₀.1 at hσ₀
      simp [cellIndicator, positroidCell, hσ₀]
    · have hnot : q ∉ positroidCell σ := by
        intro hq
        apply hσ
        apply Subtype.ext
        change projectiveSupport q = σ.1 at hq
        change projectiveSupport q = σ₀.1 at hσ₀
        exact hq.symm.trans hσ₀
      simp [cellIndicator, hσ, hnot]
  calc
    (∑ σ : RealizedSupport, cellIndicator σ q) =
        ∑ σ : RealizedSupport, if σ = σ₀ then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact hterm σ
    _ = 1 := by simp

/-! ## Cellwise assembly of the ambient top form

The positroid strata have different dimensions, so their intrinsic canonical
forms have different degrees. The parameter `t` determines both the projective
point and the differential form; the global support partition selects the
unique cell containing that point. Boundary strata are handled by the
lower-degree logarithmic residue forms in the chart owner.
-/

/-- A concrete positive parameter point used to name the full-support cell. -/
def unitPositiveParameters : PositiveParameters :=
  ⟨fun _ => 1, fun _ => by norm_num⟩

/-- The all-positive Plücker support, realized by the top-cell chart. -/
noncomputable def topPositroidSupport : RealizedSupport :=
  ⟨fun _ => true,
    ⟨Quotient.mk projectivePluckerSetoid
        (chartRepresentative unitPositiveParameters),
      topCell_support_all_true unitPositiveParameters⟩⟩

/-! The point and form arguments are tied together here. The former version
allowed an unrelated projective point and chart parameter, which did not
define a cellwise form on that point. -/

/-- The projective point represented by the top-cell chart parameter. -/
noncomputable def topCellProjectivePoint (t : PositiveParameters) :
    ProjectiveTNNGr24 :=
  Quotient.mk projectivePluckerSetoid (chartRepresentative t)

/-- Contribution of support cell `σ` to the top-degree form at the actual
projective point represented by `t`. The exact-support partition selects one
cell, and only that cell contributes. -/
noncomputable def cellwiseTopForm (σ : RealizedSupport)
    (t : PositiveParameters) :
    ((Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ) :=
  cellIndicator σ (topCellProjectivePoint t) • canonicalTopForm t

/-- The cellwise top-form contributions sum to the canonical form at the
projective point represented by their own chart coordinates. -/
theorem canonicalTopForm_cell_sum (t : PositiveParameters) :
    (∑ σ : RealizedSupport, cellwiseTopForm σ t) = canonicalTopForm t := by
  classical
  unfold cellwiseTopForm
  rw [← Finset.sum_smul, positroid_cell_indicator_sum]
  simp

/-- Evaluation of the assembled form on the chart orientation gives its
logarithmic canonical density. -/
theorem topCell_canonicalForm_cell_sum (t : PositiveParameters) :
    (∑ σ : RealizedSupport, cellwiseTopForm σ t) coordinateFrame =
      dlogDensity t := by
  rw [canonicalTopForm_cell_sum, canonicalTopForm_coordinateFrame]

/-- Every point in the chart parameterized top cell lies in the all-positive
positroid stratum. -/
theorem chartRepresentative_mem_topPositroidCell (t : PositiveParameters) :
    topCellProjectivePoint t ∈
      positroidCell topPositroidSupport := by
  change projectiveSupport
      (Quotient.mk projectivePluckerSetoid (chartRepresentative t)) =
        topPositroidSupport.1
  rw [topCell_support_all_true]
  rfl

/-- On a chart point, the all-positive support cell contributes the top form. -/
theorem topCell_cellwiseTopForm (t : PositiveParameters) :
    cellwiseTopForm topPositroidSupport t =
        canonicalTopForm t := by
  have h := chartRepresentative_mem_topPositroidCell t
  simp [cellwiseTopForm, cellIndicator, h]

/-- On a chart point, every other realized support cell contributes zero. -/
theorem otherCell_cellwiseTopForm_eq_zero (t : PositiveParameters)
    {σ : RealizedSupport} (hσ : σ ≠ topPositroidSupport) :
    cellwiseTopForm σ t = 0 := by
  have hpoint := chartRepresentative_mem_topPositroidCell t
  change projectiveSupport
    (Quotient.mk projectivePluckerSetoid (chartRepresentative t)) =
      topPositroidSupport.1 at hpoint
  have hsupport : σ.1 ≠ topPositroidSupport.1 := by
    intro h
    exact hσ (Subtype.ext h)
  have hnot : topCellProjectivePoint t ∉ positroidCell σ := by
    change projectiveSupport (topCellProjectivePoint t) ≠ σ.1
    intro h
    apply hsupport
    exact h.symm.trans hpoint
  simp [cellwiseTopForm, cellIndicator, hnot]

/-- The canonical top form evaluates on its oriented coordinate frame as the
positive logarithmic density `∏ᵢ tᵢ⁻¹`. -/
theorem topCell_canonicalForm_value (t : PositiveParameters) :
    canonicalTopForm t coordinateFrame = dlogDensity t :=
  canonicalTopForm_coordinateFrame t

/-- The top-cell canonical-form coefficient is strictly positive throughout
the top positroid chart. -/
theorem topCell_canonicalForm_positive (t : PositiveParameters) :
    0 < canonicalTopForm t coordinateFrame := by
  rw [topCell_canonicalForm_value]
  exact dlogDensity_pos t

/-! ## The chart boundary and its logarithmic residue forms

The projective support owner gives the global finite positroid partition.
Here we describe the part visible in the `p01 = 1` positive-network chart.
The closed chart has nonnegative parameters; fixing their exact support gives
its coordinate-face stratification.  The canonical form on a face is the
logarithmic form in the coordinates that remain positive, and taking a
coordinate residue removes exactly one logarithmic factor.
-/

/-- Nonnegative closure of the four positive-network coordinates. -/
@[ext]
structure ClosedTopCoordinates where
  value : Fin 4 → ℝ
  nonneg : ∀ i, 0 ≤ value i

/-- The exact set of live coordinates of a point in the closed chart. -/
noncomputable def chartCoordinateSupport (x : ClosedTopCoordinates) : Finset (Fin 4) :=
  Finset.univ.filter fun i => 0 < x.value i

/-- The logarithmic density of a coordinate face, using only its live
coordinates.  This is the coefficient of the face's oriented `dlog` form. -/
noncomputable def coordinateFaceDensity (x : ClosedTopCoordinates)
    (I : Finset (Fin 4)) : ℝ :=
  ∏ i ∈ I, (x.value i)⁻¹

/-- The logarithmic density on the actual coordinate face of `x`, using only
its live coordinates. -/
noncomputable def chartFaceCanonicalDensity (x : ClosedTopCoordinates) : ℝ :=
  coordinateFaceDensity x (chartCoordinateSupport x)

/-- The face density loses precisely the logarithmic factor indexed by a
coordinate whose boundary residue is taken. -/
theorem coordinateFaceDensity_factor (x : ClosedTopCoordinates)
    (I : Finset (Fin 4)) {i : Fin 4} (hi : i ∈ I) :
    coordinateFaceDensity x I =
      (x.value i)⁻¹ * coordinateFaceDensity x (I.erase i) := by
  unfold coordinateFaceDensity
  exact (Finset.mul_prod_erase I (fun j : Fin 4 => (x.value j)⁻¹) hi).symm

/-- Iterated logarithmic residues remove any finite set of live coordinates.
The positivity hypothesis is essential: it guarantees that every factor
cancelled against its inverse belongs to the actual open face. -/
theorem coordinateFaceDensity_iterated_residue (x : ClosedTopCoordinates)
    (I J : Finset (Fin 4)) (hJI : J ⊆ I)
    (hpos : ∀ i ∈ I, 0 < x.value i) :
    (∏ i ∈ J, x.value i) * coordinateFaceDensity x I =
      coordinateFaceDensity x (I \ J) := by
  classical
  induction J using Finset.induction_on generalizing I with
  | empty => simp [coordinateFaceDensity]
  | @insert i J hi ih =>
      have hiI : i ∈ I := hJI (Finset.mem_insert_self i J)
      have hJ : J ⊆ I.erase i := by
        intro j hj
        exact Finset.mem_erase.mpr
          ⟨fun hji => hi (hji ▸ hj), hJI (Finset.mem_insert_of_mem hj)⟩
      have hposErase : ∀ j ∈ I.erase i, 0 < x.value j := by
        intro j hj
        exact hpos j (Finset.mem_of_mem_erase hj)
      have hset : I \ insert i J = (I.erase i) \ J := by
        ext j
        simp [Finset.mem_erase, and_assoc, and_left_comm, and_comm]
      rw [Finset.prod_insert hi, coordinateFaceDensity_factor x I hiI]
      have hcancel : x.value i * (x.value i)⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt (hpos i hiI))
      calc
        (x.value i * (∏ j ∈ J, x.value j)) *
            ((x.value i)⁻¹ * coordinateFaceDensity x (I.erase i)) =
            (∏ j ∈ J, x.value j) * coordinateFaceDensity x (I.erase i) := by
              calc
                (x.value i * (∏ j ∈ J, x.value j)) *
                    ((x.value i)⁻¹ * coordinateFaceDensity x (I.erase i)) =
                    (x.value i * (x.value i)⁻¹) *
                      ((∏ j ∈ J, x.value j) * coordinateFaceDensity x (I.erase i)) := by ring
                _ = (∏ j ∈ J, x.value j) * coordinateFaceDensity x (I.erase i) := by
                  rw [hcancel, one_mul]
        _ = coordinateFaceDensity x ((I.erase i) \ J) :=
          ih (I.erase i) hJ hposErase
        _ = coordinateFaceDensity x (I \ insert i J) := by rw [hset]

/-- Every coordinate in the exact support of a closed-chart point is
strictly positive, so its logarithmic face density is well-defined. -/
theorem chartCoordinateSupport_pos (x : ClosedTopCoordinates)
    {i : Fin 4} (hi : i ∈ chartCoordinateSupport x) : 0 < x.value i := by
  exact (Finset.mem_filter.mp hi).2

/-- Every realized coordinate face has strictly positive canonical density. -/
theorem chartFaceCanonicalDensity_pos (x : ClosedTopCoordinates) :
    0 < chartFaceCanonicalDensity x := by
  unfold chartFaceCanonicalDensity coordinateFaceDensity
  apply Finset.prod_pos
  intro i hi
  exact inv_pos.mpr (chartCoordinateSupport_pos x hi)

/-- A coordinate outside the exact support is zero by nonnegativity. -/
theorem chartCoordinate_eq_zero_of_not_mem (x : ClosedTopCoordinates)
    {i : Fin 4} (hi : i ∉ chartCoordinateSupport x) : x.value i = 0 := by
  apply le_antisymm (le_of_not_gt ?_) (x.nonneg i)
  intro hpos
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩)

/-- The nonnegative Plücker chart map in lexicographic order
`01, 02, 03, 12, 13, 23`. -/
def closedChartPlucker (x : ClosedTopCoordinates) : Fin 6 → ℝ
  | 0 => 1
  | 1 => x.value 0
  | 2 => x.value 0 * x.value 1
  | 3 => x.value 2
  | 4 => x.value 2 * (x.value 1 + x.value 3)
  | 5 => x.value 0 * x.value 2 * x.value 3

/-- Exact Plücker support of a point in the closed top-cell chart. -/
noncomputable def closedChartPluckerSupport (x : ClosedTopCoordinates) : Finset (Fin 6) :=
  Finset.univ.filter fun i => 0 < closedChartPlucker x i

/-- All six coordinates of the closed chart are nonnegative. -/
theorem closedChartPlucker_nonneg (x : ClosedTopCoordinates) (i : Fin 6) :
    0 ≤ closedChartPlucker x i := by
  fin_cases i
  · norm_num [closedChartPlucker]
  · exact x.nonneg 0
  · exact mul_nonneg (x.nonneg 0) (x.nonneg 1)
  · exact x.nonneg 2
  · exact mul_nonneg (x.nonneg 2) (add_nonneg (x.nonneg 1) (x.nonneg 3))
  · exact mul_nonneg (mul_nonneg (x.nonneg 0) (x.nonneg 2)) (x.nonneg 3)

/-- The closed chart remains on the Klein quadric, including all its boundary
faces. -/
theorem closedChartPlucker_klein (x : ClosedTopCoordinates) :
    closedChartPlucker x 0 * closedChartPlucker x 5 -
      closedChartPlucker x 1 * closedChartPlucker x 4 +
      closedChartPlucker x 2 * closedChartPlucker x 3 = 0 := by
  simp [closedChartPlucker]
  ring

/-- A matrix representative for the closed `p01 = 1` network chart.  Its
ordered minors are exactly the six coordinates in `closedChartPlucker`. -/
def closedChartMatrix (x : ClosedTopCoordinates) :
    InfoGeometry.Projective.MatrixPluckerPositiveBridge.Matrix2x4 :=
  fun i j =>
    match i, j with
    | 0, 0 => 1
    | 1, 0 => 0
    | 0, 1 => 0
    | 1, 1 => 1
    | 0, 2 => -x.value 2
    | 1, 2 => x.value 0
    | 0, 3 => -x.value 2 * (x.value 1 + x.value 3)
    | 1, 3 => x.value 0 * x.value 1
    | _, _ => 0

/-- The chart matrix realizes the advertised Plücker vector, including the
Klein relation in the `13` minor. -/
theorem closedChartMatrix_plucker (x : ClosedTopCoordinates) (i : Fin 6) :
    matrixPluckerCoords (closedChartMatrix x) i = closedChartPlucker x i := by
  fin_cases i <;>
    simp [closedChartMatrix, closedChartPlucker,
      InfoGeometry.Projective.MatrixPluckerPositiveBridge.matrixPluckerCoords_apply] <;> ring

/-- Every point of the closed network chart is an actual projective
nonnegative `Gr(2,4)` point, not just a formal Plücker tuple. -/
noncomputable def closedChartRepresentative (x : ClosedTopCoordinates) :
    NonnegativeFullRankRep := by
  let M : InfoGeometry.Projective.MatrixPluckerPositiveBridge.Matrix2x4 :=
    closedChartMatrix x
  have hminor : MatrixPluckerNonnegative M := by
    intro i
    rw [closedChartMatrix_plucker]
    exact closedChartPlucker_nonneg x i
  have hchart : M ∈ positiveGrassmannianChart (k := 2) (n := 4) :=
    matrixPluckerNonnegative_mem_positiveGrassmannianChart M hminor
  have hnonzero : ∃ i : Fin 6, 0 < matrixPluckerCoords M i := by
    refine ⟨0, ?_⟩
    rw [closedChartMatrix_plucker]
    simp [closedChartPlucker]
  exact ⟨M, hchart, hnonzero⟩

/-- The projective point represented by the closed chart matrix. -/
noncomputable def closedChartProjectivePoint (x : ClosedTopCoordinates) :
    ProjectiveTNNGr24 :=
  Quotient.mk projectivePluckerSetoid (closedChartRepresentative x)

/-- The global projective positroid support of a closed-chart point is exactly
the support of its six explicit Plücker coordinates. -/
theorem closedChartProjectivePoint_support (x : ClosedTopCoordinates) :
    projectiveSupport (closedChartProjectivePoint x) =
      fun i => decide (0 < closedChartPlucker x i) := by
  classical
  rw [closedChartProjectivePoint, projectiveSupport_mk]
  funext i
  simp only [pluckerSupport, normalizedPlucker]
  have hmass := pluckerMass_pos (closedChartRepresentative x)
  have hminor :
      matrixPluckerCoords (closedChartRepresentative x).1 i =
        closedChartPlucker x i := by
    change matrixPluckerCoords (closedChartMatrix x) i = closedChartPlucker x i
    exact closedChartMatrix_plucker x i
  have hiff :
      (0 < matrixPluckerCoords (closedChartRepresentative x).1 i /
        pluckerMass (closedChartRepresentative x)) ↔
        0 < closedChartPlucker x i := by
    rw [div_pos_iff_of_pos_right hmass, hminor]
  exact congrArg (fun p : Prop => decide p) (propext hiff)

/-- Full Plücker support in this chart is equivalent to all four network
coordinates being live.  Thus the unique four-dimensional positroid stratum
is exactly the existing positive top-cell chart. -/
theorem closedChart_full_support_iff (x : ClosedTopCoordinates) :
    closedChartPluckerSupport x = Finset.univ ↔
      ∀ i, 0 < x.value i := by
  constructor
  · intro hs i
    have h01 : 0 < closedChartPlucker x 1 := by
      have hi : (1 : Fin 6) ∈ closedChartPluckerSupport x := by
        rw [hs]
        simp
      exact (Finset.mem_filter.mp hi).2
    have h12 : 0 < closedChartPlucker x 3 := by
      have hi : (3 : Fin 6) ∈ closedChartPluckerSupport x := by
        rw [hs]
        simp
      exact (Finset.mem_filter.mp hi).2
    have h03 : 0 < closedChartPlucker x 2 := by
      have hi : (2 : Fin 6) ∈ closedChartPluckerSupport x := by
        rw [hs]
        simp
      exact (Finset.mem_filter.mp hi).2
    have h23 : 0 < closedChartPlucker x 5 := by
      have hi : (5 : Fin 6) ∈ closedChartPluckerSupport x := by
        rw [hs]
        simp
      exact (Finset.mem_filter.mp hi).2
    simp only [closedChartPlucker] at h01 h12 h03 h23
    fin_cases i
    · exact h01
    · exact (mul_pos_iff_of_pos_left h01).mp h03
    · exact h12
    · exact (mul_pos_iff_of_pos_left (mul_pos h01 h12)).mp h23
  · intro h
    ext i
    simp only [closedChartPluckerSupport, Finset.mem_filter,
      Finset.mem_univ, true_and]
    fin_cases i
    · norm_num [closedChartPlucker]
    · simpa [closedChartPlucker] using h 0
    · simpa [closedChartPlucker] using mul_pos (h 0) (h 1)
    · simpa [closedChartPlucker] using h 2
    · simpa [closedChartPlucker] using mul_pos (h 2) (add_pos (h 1) (h 3))
    · simpa [closedChartPlucker] using mul_pos (mul_pos (h 0) (h 2)) (h 3)

/-- On a strictly positive chart point, the four-coordinate face density is
the coefficient of the existing top-cell canonical form. -/
theorem topCellDensity_eq_coordinateFaceDensity (t : PositiveParameters) :
    coordinateFaceDensity ⟨t.1, fun i => le_of_lt (t.2 i)⟩ Finset.univ =
      dlogDensity t := by
  simp [coordinateFaceDensity, dlogDensity]

/-- Realized Plücker supports in the closed positive-network chart. -/
noncomputable def ClosedChartSupport :=
  {I : Finset (Fin 6) //
    ∃ y : ClosedTopCoordinates, closedChartPluckerSupport y = I}

noncomputable instance closedChartSupportFintype : Fintype ClosedChartSupport :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The chart's support cells form an exact finite partition.  This is the
cell decomposition statement for the closed `p01 = 1` chart; its full-support
cell carries the top form, while lower-dimensional cells carry the residue
forms given by `coordinateFaceDensity_factor`. -/
theorem closedChart_support_indicator_sum (x : ClosedTopCoordinates) :
    (∑ I : ClosedChartSupport,
      (if closedChartPluckerSupport x = I.1 then (1 : ℝ) else 0)) = 1 := by
  classical
  let I₀ : ClosedChartSupport :=
    ⟨closedChartPluckerSupport x, ⟨x, rfl⟩⟩
  rw [Finset.sum_eq_single I₀]
  · simp [I₀]
  · intro I hI hne
    have hsupport : closedChartPluckerSupport x ≠ I.1 := by
      intro h
      apply hne
      exact Subtype.ext h.symm
    simp [hsupport]
  · intro hnot
    exact (hnot (Finset.mem_univ I₀)).elim

/-! ## Intrinsic logarithmic forms on simplex positroid cells

Some positroid supports make every monomial in the Klein relation vanish
term-by-term.  On precisely those strata the projective cell is an open
simplex in its positive Plücker coordinates.  Fixing one positive Plücker
coordinate as the projective pivot gives the usual simplex `dlog` form.  This
is a cell form on the actual normalized Plücker stratum, rather than an
ambient top-degree form selected by an indicator.
-/

/-- The three complementary Plücker pairs appearing in the Klein relation. -/
def kleinComplementaryPairs : Fin 3 → Finset (Fin 6)
  | 0 => {0, 5}
  | 1 => {1, 4}
  | 2 => {2, 3}

/-- A support on which the Klein equation is identically zero: it contains
neither endpoint pair of any quadratic monomial in that equation. -/
def simplexPositroidSupport (I : Finset (Fin 6)) : Prop :=
  ∀ k : Fin 3, ¬ kleinComplementaryPairs k ⊆ I

/-- The support labels for which the Plücker relation imposes no equation on
their positive coordinates. -/
abbrev SimplexCellSupport :=
  {I : Finset (Fin 6) // simplexPositroidSupport I}

/-- A point in the exact projective positroid stratum with support `I`. -/
abbrev SimplexPositroidCell (I : SimplexCellSupport) :=
  {P : NormalizedPositivePluckerPoint // positiveSupport P = I.1}

/-- Gauge-fixed Plücker weights on a support whose Klein relation vanishes
term by term.  These are the coordinates of an actual open projective
simplex: supported coordinates are positive, unsupported coordinates vanish,
and the projective scale is fixed by `sum_one`. -/
@[ext]
structure PositiveSimplexPluckerWeights (I : SimplexCellSupport) where
  coord : Fin 6 → ℝ
  positive : ∀ i ∈ I.1, 0 < coord i
  zero : ∀ i ∉ I.1, coord i = 0
  sum_one : ∑ i : Fin 6, coord i = 1

/-- On a support where a complementary Klein pair is absent, its product
vanishes for every weight vector supported on that cell. -/
private theorem positiveSimplexWeights_pairProduct_zero
    (I : SimplexCellSupport) (w : PositiveSimplexPluckerWeights I)
    (k : Fin 3) :
    (∏ i ∈ kleinComplementaryPairs k, w.coord i) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i ∈ kleinComplementaryPairs k, i ∉ I.1 := by
    by_contra h
    push Not at h
    exact I.2 k h
  exact Finset.prod_eq_zero hi.1 (w.zero i hi.2)

/-- A positive projective simplex weight vector on a Klein-term-free support
is a normalized nonnegative Plücker point. -/
noncomputable def positiveSimplexWeightsToPoint
    (I : SimplexCellSupport) (w : PositiveSimplexPluckerWeights I) :
    SimplexPositroidCell I := by
  refine ⟨⟨w.coord, ?_, w.sum_one, ?_⟩, ?_⟩
  · intro i
    by_cases hi : i ∈ I.1
    · exact (w.positive i hi).le
    · rw [w.zero i hi]
  · have hp0 := positiveSimplexWeights_pairProduct_zero I w 0
    have hp1 := positiveSimplexWeights_pairProduct_zero I w 1
    have hp2 := positiveSimplexWeights_pairProduct_zero I w 2
    have h05 : w.coord 0 * w.coord 5 = 0 := by
      simpa [kleinComplementaryPairs] using hp0
    have h14 : w.coord 1 * w.coord 4 = 0 := by
      simpa [kleinComplementaryPairs] using hp1
    have h23 : w.coord 2 * w.coord 3 = 0 := by
      simpa [kleinComplementaryPairs] using hp2
    change w.coord 0 * w.coord 5 - w.coord 1 * w.coord 4 +
      w.coord 2 * w.coord 3 = 0
    rw [h05, h14, h23]
    norm_num
  · apply Finset.ext
    intro i
    by_cases hi : i ∈ I.1
    · simp [positiveSupport, hi, w.positive i hi]
    · simp [positiveSupport, hi, w.zero i hi]

/-- Read the normalized Plücker coordinates of an actual simplex positroid
cell as positive weights on its exact support. -/
noncomputable def pointToPositiveSimplexWeights
  (I : SimplexCellSupport) (P : SimplexPositroidCell I) :
    PositiveSimplexPluckerWeights I where
  coord := P.1.coord
  positive := fun _ hi => supportStratum_coordinate_pos P.2 hi
  zero := fun _ hi => supportStratum_coordinate_eq_zero P.2 hi
  sum_one := P.1.coord_sum_one

/-- The exact-support positroid stratum is canonically the open simplex of
positive Plücker weights on that support, with its projective scale fixed by
the sum-one gauge.  The Klein equation imposes no additional relation here
because every complementary product has a missing support coordinate. -/
noncomputable def simplexPositroidCell_equiv_positiveWeights
    (I : SimplexCellSupport) :
    SimplexPositroidCell I ≃ PositiveSimplexPluckerWeights I where
  toFun := pointToPositiveSimplexWeights I
  invFun := positiveSimplexWeightsToPoint I
  left_inv P := by
    apply Subtype.ext
    apply NormalizedPositivePluckerPoint.ext
    rfl
  right_inv w := by
    apply PositiveSimplexPluckerWeights.ext
    rfl

/-- The independent Plücker-coordinate directions after fixing pivot `p`. -/
abbrev SimplexCellCoordinates (I : SimplexCellSupport)
    (p : {p : Fin 6 // p ∈ I.1}) :=
  {i : Fin 6 // i ∈ I.1.erase p.1}

/-- The oriented coordinate frame for the projective simplex chart obtained
by omitting the pivot coordinate. -/
noncomputable def simplexCellFrame (I : SimplexCellSupport)
    (p : {p : Fin 6 // p ∈ I.1}) :
    SimplexCellCoordinates I p → (SimplexCellCoordinates I p → ℝ) :=
  Pi.basisFun ℝ (SimplexCellCoordinates I p)

/-- The intrinsic canonical form on a simplex positroid cell.  Its coefficient
is the product of inverse positive Plücker coordinates, including the pivot
coordinate determined by projective normalization. -/
noncomputable def simplexPositroidCanonicalForm
    (I : SimplexCellSupport) (p : {p : Fin 6 // p ∈ I.1})
    (P : SimplexPositroidCell I) :
    ((SimplexCellCoordinates I p → ℝ)
      [⋀^SimplexCellCoordinates I p]→ₗ[ℝ] ℝ) := by
  classical
  let density : ℝ := (P.1.coord p.1)⁻¹ *
    ∏ i : SimplexCellCoordinates I p, (P.1.coord i.1)⁻¹
  exact density • (Pi.basisFun ℝ (SimplexCellCoordinates I p)).det

/-- On the omitted-pivot coordinate frame, the simplex cell form evaluates
to the product `∏ᵢ pᵢ⁻¹` over the exact support. -/
theorem simplexPositroidCanonicalForm_frame
    (I : SimplexCellSupport) (p : {p : Fin 6 // p ∈ I.1})
    (P : SimplexPositroidCell I) :
    simplexPositroidCanonicalForm I p P (simplexCellFrame I p) =
      (P.1.coord p.1)⁻¹ *
        ∏ i : SimplexCellCoordinates I p, (P.1.coord i.1)⁻¹ := by
  classical
  unfold simplexPositroidCanonicalForm
  change ((P.1.coord p)⁻¹ *
      ∏ i : SimplexCellCoordinates I p, (P.1.coord i.1)⁻¹) *
      (Pi.basisFun ℝ (SimplexCellCoordinates I p)).det
        (Pi.basisFun ℝ (SimplexCellCoordinates I p)) = _
  rw [Module.Basis.det_self]
  simp

/-- On the oriented chart frame, the simplex-cell canonical coefficient is
the product of inverse Plücker coordinates over the whole support.  In
particular, it is independent of which positive Plücker coordinate is used
as the projective pivot. -/
theorem simplexPositroidCanonicalForm_frame_eq_supportProduct
    (I : SimplexCellSupport) (p : {p : Fin 6 // p ∈ I.1})
    (P : SimplexPositroidCell I) :
    simplexPositroidCanonicalForm I p P (simplexCellFrame I p) =
      ∏ i ∈ I.1, (P.1.coord i)⁻¹ := by
  classical
  rw [simplexPositroidCanonicalForm_frame]
  have hsubtype :
      (∏ i : SimplexCellCoordinates I p, (P.1.coord i.1)⁻¹) =
        ∏ i ∈ I.1.erase p.1, (P.1.coord i)⁻¹ := by
    exact (Finset.prod_subtype (I.1.erase p.1) (fun _ => Iff.rfl)
      (fun i : Fin 6 => (P.1.coord i)⁻¹)).symm
  rw [hsubtype]
  exact Finset.mul_prod_erase I.1 (fun i : Fin 6 => (P.1.coord i)⁻¹) p.2

/-- Changing the projective pivot changes the coordinate frame but not the
canonical coefficient of a simplex positroid cell. -/
theorem simplexPositroidCanonicalForm_frame_pivot_independent
    (I : SimplexCellSupport) (p q : {p : Fin 6 // p ∈ I.1})
    (P : SimplexPositroidCell I) :
    simplexPositroidCanonicalForm I p P (simplexCellFrame I p) =
      simplexPositroidCanonicalForm I q P (simplexCellFrame I q) := by
  rw [simplexPositroidCanonicalForm_frame_eq_supportProduct,
    simplexPositroidCanonicalForm_frame_eq_supportProduct]

/-- In positive simplex coordinates, the intrinsic canonical coefficient is
the reciprocal product of the supported Plücker weights. -/
theorem simplexPositroidCanonicalForm_positiveWeights_frame
    (I : SimplexCellSupport) (p : {p : Fin 6 // p ∈ I.1})
    (w : PositiveSimplexPluckerWeights I) :
    simplexPositroidCanonicalForm I p
        ((simplexPositroidCell_equiv_positiveWeights I).symm w)
        (simplexCellFrame I p) =
      ∏ i ∈ I.1, (w.coord i)⁻¹ := by
  rw [simplexPositroidCanonicalForm_frame_eq_supportProduct]
  rfl

/-- Every simplex-cell Plücker coordinate is positive, so its canonical
coefficient is strictly positive. -/
theorem simplexPositroidCanonicalForm_frame_pos
    (I : SimplexCellSupport) (p : {p : Fin 6 // p ∈ I.1})
    (P : SimplexPositroidCell I) :
    0 < simplexPositroidCanonicalForm I p P (simplexCellFrame I p) := by
  rw [simplexPositroidCanonicalForm_frame]
  apply mul_pos
  · have hmem : p.1 ∈ positiveSupport P.1 := by rw [P.2]; exact p.2
    exact inv_pos.mpr ((Finset.mem_filter.mp hmem).2)
  · apply Finset.prod_pos
    intro i hi
    have hmem : i.1 ∈ positiveSupport P.1 := by
      rw [P.2]
      exact Finset.mem_of_mem_erase i.2
    exact inv_pos.mpr ((Finset.mem_filter.mp hmem).2)

/-- The Klein relation vanishes termwise on a simplex positroid support. -/
theorem simplexPositroidCell_klein_terms_zero
    (I : SimplexCellSupport)
    (P : SimplexPositroidCell I) (k : Fin 3) :
    let pair := kleinComplementaryPairs k
    (∏ i ∈ pair, P.1.coord i) = 0 := by
  classical
  dsimp
  obtain ⟨i, hi⟩ : ∃ i ∈ kleinComplementaryPairs k, i ∉ I.1 := by
    by_contra h
    push Not at h
    exact I.2 k h
  have hzero : P.1.coord i = 0 := by
    apply supportStratum_coordinate_eq_zero P.2
    exact hi.2
  exact Finset.prod_eq_zero hi.1 hzero

end InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm
