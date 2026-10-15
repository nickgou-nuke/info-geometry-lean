import Mathlib
import InfoGeometry.Projective.ExteriorPowerPluckerBridge
import InfoGeometry.Projective.MatrixPluckerPositiveBridge
import InfoGeometry.Topology.Gr24PositroidCanonicalForm

/-!
# Projective positive Plücker support cells for `Gr(2,4)`

The carrier is the nonzero nonnegative real Klein quadric modulo positive
rescaling.  The Klein equation makes every representative a decomposable
bivector, and hence an actual two-plane Plücker vector.  Its attainable
coordinate supports give a finite disjoint projective cell decomposition.

This is the positroid decomposition at the level of projective Plücker points
and basis supports.  Each point is also shown to admit a matrix representative
whose maximal minors are nonnegative, so the support cells are genuine
rank-two positroid supports.  The full-support cell is linked to the explicit
positive chart and logarithmic canonical form in `Gr24PositroidCanonicalForm`.
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

@[simp] theorem pluckerCoordinate_scale (c : ℝ) (P : Bivector4) (i : Fin 6) :
    pluckerCoordinate (scalePlucker c P) i = c * pluckerCoordinate P i := by
  fin_cases i <;> rfl

@[simp] theorem scalePlucker_scalePlucker (a b : ℝ) (P : Bivector4) :
    scalePlucker a (scalePlucker b P) = scalePlucker (a * b) P := by
  cases P
  apply Bivector4.ext <;> simp only [scalePlucker] <;> ring

theorem scalePlucker_klein (c : ℝ) (P : Bivector4) :
    kleinForm (scalePlucker c P) = c ^ 2 * kleinForm P := by
  cases P
  simp [scalePlucker, kleinForm]
  ring

/-- A nonzero point of the nonnegative Klein cone. -/
structure PositivePluckerRepresentative where
  bivector : Bivector4
  klein_eq_zero : kleinForm bivector = 0
  coordinates_nonnegative : ∀ i, 0 ≤ pluckerCoordinate bivector i
  coordinates_nonzero : ∃ i, pluckerCoordinate bivector i ≠ 0

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

private theorem rowVec4_matrixOfRows (u v : Vec4) :
    rowVec4 (matrixOfRows u v) 0 = u ∧
      rowVec4 (matrixOfRows u v) 1 = v := by
  constructor <;> funext i <;> cases i <;> rfl

private theorem matrixPluckerCoords_matrixOfRows (u v : Vec4) (i : Fin 6) :
    matrixPluckerCoords (matrixOfRows u v) i = pluckerCoords u v i := by
  have h := rowVec4_matrixOfRows u v
  simp only [matrixPluckerCoords, h.1, h.2]

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

@[simp] theorem normalizedPointBivector_coordinate
    (P : NormalizedPositivePluckerPoint) (i : Fin 6) :
    pluckerCoordinate (normalizedPointBivector P) i = P.coord i := by
  fin_cases i <;> rfl

/-- Every normalized point gives a nonzero representative of the positive
Klein cone.  The sum-one gauge condition supplies nonzeroness. -/
def normalizedPointRepresentative (P : NormalizedPositivePluckerPoint) :
    PositivePluckerRepresentative := by
  refine ⟨normalizedPointBivector P, ?_, ?_, ?_⟩
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
