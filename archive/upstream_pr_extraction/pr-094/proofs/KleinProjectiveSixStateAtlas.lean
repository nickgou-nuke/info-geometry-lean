import proofs.KleinProjectiveSixState
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# The six affine charts of the topological projective six-state fibre

The algebraic quotient from `KleinProjectiveSixState` is equipped with its
native quotient topology.  For every homogeneous coordinate we construct the
standard affine chart, modelled on the remaining five complex coordinates.
-/

noncomputable section
namespace KleinProjectiveSixStateAtlas

open Topology
open KleinProjectiveSixState

abbrev Index := Fin 2 × Fin 3
abbrev Vec := Index → ℂ
abbrev NonzeroVec := {v : Vec // v ≠ 0}
abbrev ProjectiveSixState := KleinProjectiveSixState.ProjectiveSixState

/-- The five affine coordinates complementary to `i`. -/
abbrev AffineFive (i : Index) := {j : Index // j ≠ i} → ℂ

def homogeneousChartRep (i : Index) (v : NonzeroVec) : AffineFive i :=
  fun j ↦ v.1 j.1 / v.1 i

private theorem homogeneousChartRep_respects (i : Index) {v w : NonzeroVec}
    (h : projectiveRel v w) :
    homogeneousChartRep i v = homogeneousChartRep i w := by
  rcases h with ⟨c, hc, hw⟩
  funext j
  change v.1 j.1 / v.1 i = w.1 j.1 / w.1 i
  rw [hw]
  change v.1 j.1 / v.1 i = (c * v.1 j.1) / (c * v.1 i)
  rw [mul_div_mul_left _ _ hc]

/-- Standard homogeneous-coordinate quotient map. -/
def projectiveChartMap (i : Index) : ProjectiveSixState → AffineFive i :=
  Quotient.lift (homogeneousChartRep i)
    (fun _ _ h ↦ homogeneousChartRep_respects i h)

private theorem coordinateNonzero_respects (i : Index) {v w : NonzeroVec}
    (h : projectiveRel v w) : (v.1 i ≠ 0) = (w.1 i ≠ 0) := by
  rcases h with ⟨c, hc, hw⟩
  apply propext
  rw [hw]
  simp [hc]

def projectiveChartSource (i : Index) : Set ProjectiveSixState :=
  {q | Quotient.lift (fun v : NonzeroVec ↦ v.1 i ≠ 0)
    (fun _ _ h ↦ coordinateNonzero_respects i h) q}

@[simp] theorem projectiveMk_mem_chartSource (i : Index) (v : NonzeroVec) :
    projectiveMk v ∈ projectiveChartSource i ↔ v.1 i ≠ 0 := Iff.rfl

def normalizedVec (i : Index) (z : AffineFive i) : Vec :=
  fun j ↦ if h : j = i then 1 else z ⟨j, h⟩

theorem normalizedVec_at (i : Index) (z : AffineFive i) :
    normalizedVec i z i = 1 := by simp [normalizedVec]

def normalizedNonzero (i : Index) (z : AffineFive i) : NonzeroVec :=
  ⟨normalizedVec i z, by
    intro h
    have hi := congrFun h i
    simp [normalizedVec] at hi⟩

def affineToProjective (i : Index) : AffineFive i → ProjectiveSixState :=
  fun z ↦ projectiveMk (normalizedNonzero i z)

theorem projectiveChartMap_affineToProjective (i : Index) (z : AffineFive i) :
    projectiveChartMap i (affineToProjective i z) = z := by
  funext j
  change normalizedVec i z j.1 / normalizedVec i z i = z j
  simp [normalizedVec, j.2]

theorem affineToProjective_mem_source (i : Index) (z : AffineFive i) :
    affineToProjective i z ∈ projectiveChartSource i := by
  simp [affineToProjective, normalizedNonzero, normalizedVec]

theorem affineToProjective_projectiveChartMap_mk (i : Index) (v : NonzeroVec)
    (hv : v.1 i ≠ 0) :
    affineToProjective i (projectiveChartMap i (projectiveMk v)) = projectiveMk v := by
  apply Quotient.sound
  refine ⟨v.1 i, hv, ?_⟩
  apply funext
  intro j
  by_cases hji : j = i
  · subst j
    simp [normalizedNonzero, normalizedVec]
  · simp only [Pi.smul_apply, normalizedNonzero, normalizedVec, hji]
    change v.1 j = v.1 i * (v.1 j / v.1 i)
    field_simp

theorem affineToProjective_projectiveChartMap (i : Index) (q : ProjectiveSixState)
    (hq : q ∈ projectiveChartSource i) :
    affineToProjective i (projectiveChartMap i q) = q := by
  refine Quotient.inductionOn q ?_ hq
  intro v hv
  exact affineToProjective_projectiveChartMap_mk i v hv

theorem chartSource_cover (q : ProjectiveSixState) :
    ∃ i : Index, q ∈ projectiveChartSource i := by
  refine Quotient.inductionOn q ?_
  intro v
  have hv : ∃ i, v.1 i ≠ 0 := by
    by_contra h
    push_neg at h
    exact v.2 (funext h)
  rcases hv with ⟨i, hi⟩
  exact ⟨i, hi⟩

theorem isOpen_projectiveChartSource (i : Index) :
    IsOpen (projectiveChartSource i) := by
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen {v : NonzeroVec | v.1 i ≠ 0}
  exact isOpen_ne.preimage ((continuous_apply i).comp continuous_subtype_val)

private theorem homogeneousChartRep_continuousOn (i : Index) :
    ContinuousOn (homogeneousChartRep i)
      (projectiveMk ⁻¹' projectiveChartSource i) := by
  rw [continuousOn_pi]
  intro j
  exact (((continuous_apply j.1).comp continuous_subtype_val).continuousOn.div
    (((continuous_apply i).comp continuous_subtype_val).continuousOn)
    (fun v hv ↦ hv))

theorem projectiveChartMap_continuousOn (i : Index) :
    ContinuousOn (projectiveChartMap i) (projectiveChartSource i) := by
  rw [isQuotientMap_quotient_mk'.continuousOn_isOpen_iff
    (isOpen_projectiveChartSource i)]
  exact homogeneousChartRep_continuousOn i

private theorem normalizedVec_continuous (i : Index) :
    Continuous (normalizedVec i) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · simpa [normalizedVec, hji] using
      (continuous_const : Continuous fun _ : AffineFive i ↦ (1 : ℂ))
  · simpa [normalizedVec, hji] using
      (continuous_apply (⟨j, hji⟩ : {j : Index // j ≠ i}) :
        Continuous fun z : AffineFive i ↦ z ⟨j, hji⟩)

theorem affineToProjective_continuous (i : Index) :
    Continuous (affineToProjective i) := by
  apply continuous_quot_mk.comp
  exact (normalizedVec_continuous i).subtype_mk _

/-- The `i`th standard affine chart of topological `CP⁵`. -/
def projectiveChart (i : Index) :
    OpenPartialHomeomorph ProjectiveSixState (AffineFive i) where
  toPartialEquiv :=
    { toFun := projectiveChartMap i
      invFun := affineToProjective i
      source := projectiveChartSource i
      target := Set.univ
      map_source' := fun _ _ ↦ Set.mem_univ _
      map_target' := fun z _ ↦ affineToProjective_mem_source i z
      left_inv' := fun q hq ↦ affineToProjective_projectiveChartMap i q hq
      right_inv' := fun z _ ↦ projectiveChartMap_affineToProjective i z }
  open_source := isOpen_projectiveChartSource i
  open_target := isOpen_univ
  continuousOn_toFun := projectiveChartMap_continuousOn i
  continuousOn_invFun := (affineToProjective_continuous i).continuousOn

theorem projectiveChart_atlas_cover (q : ProjectiveSixState) :
    ∃ i : Index, q ∈ (projectiveChart i).source :=
  chartSource_cover q

theorem projectiveSixState_is_locally_affineFive (q : ProjectiveSixState) :
    ∃ (i : Index) (e : OpenPartialHomeomorph ProjectiveSixState (AffineFive i)),
      q ∈ e.source ∧ e.target = Set.univ := by
  obtain ⟨i, hi⟩ := projectiveChart_atlas_cover q
  exact ⟨i, projectiveChart i, hi, rfl⟩

abbrev CP5Model := Fin 5 → ℂ

private theorem complement_card_five (i : Index) :
    Fintype.card {j : Index // j ≠ i} = 5 := by
  rcases i with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> native_decide

def complementEquivFin5 (i : Index) : {j : Index // j ≠ i} ≃ Fin 5 :=
  Fintype.equivFinOfCardEq (complement_card_five i)

def affineFiveHomeomorph (i : Index) : AffineFive i ≃ₜ CP5Model :=
  Homeomorph.piCongrLeft (Y := fun _ : Fin 5 ↦ ℂ) (complementEquivFin5 i)

/-- The six charts with a common fixed model `ℂ⁵`. -/
def fixedProjectiveChart (i : Index) :
    OpenPartialHomeomorph ProjectiveSixState CP5Model :=
  (projectiveChart i).transHomeomorph (affineFiveHomeomorph i)

theorem fixedProjectiveChart_source (i : Index) :
    (fixedProjectiveChart i).source = projectiveChartSource i := rfl

noncomputable def chartIndex (q : ProjectiveSixState) : Index :=
  Classical.choose (chartSource_cover q)

theorem mem_chartIndex_source (q : ProjectiveSixState) :
    q ∈ (fixedProjectiveChart (chartIndex q)).source := by
  rw [fixedProjectiveChart_source]
  exact Classical.choose_spec (chartSource_cover q)

/-- Native Mathlib `ChartedSpace` structure on the six-state `CP⁵` quotient. -/
instance projectiveSixStateChartedSpace : ChartedSpace CP5Model ProjectiveSixState where
  atlas := Set.range fixedProjectiveChart
  chartAt q := fixedProjectiveChart (chartIndex q)
  mem_chart_source := mem_chartIndex_source
  chart_mem_atlas q := ⟨chartIndex q, rfl⟩

theorem cp5_atlas_eq_six_charts :
    atlas CP5Model ProjectiveSixState = Set.range fixedProjectiveChart := rfl

end KleinProjectiveSixStateAtlas
end noncomputable section
