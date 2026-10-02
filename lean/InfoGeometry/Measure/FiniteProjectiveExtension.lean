import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

/-!
# Extension of consistent finite-coordinate marginals

Finite discrete coordinates make cylinders compact and closed. Consequently,
a decreasing sequence of cylinders with empty intersection is eventually empty.
This supplies the continuity needed to extend Mathlib's projective family content
to a unique finite measure. Independence is not assumed.

This is a projective-limit measure construction, not a construction of a smooth
manifold or a replacement for the repository's algebraic colimit owners.
-/

noncomputable section

namespace InfoGeometry.Measure.FiniteProjectiveExtension

open Filter MeasureTheory
open scoped ENNReal Topology

variable {ι : Type*} {α : ι → Type*}
variable [∀ index, MeasurableSpace (α index)] [∀ index, Finite (α index)]

theorem exists_empty_of_antitone_cylinders
    {sets : ℕ → Set (∀ index, α index)}
    (cylinders : ∀ stage, sets stage ∈ measurableCylinders α)
    (decreasing : Antitone sets) (empty_intersection : (⋂ stage, sets stage) = ∅) :
    ∃ stage, sets stage = ∅ := by
  classical
  letI : ∀ index, TopologicalSpace (α index) := fun _ => ⊥
  letI : ∀ index, DiscreteTopology (α index) := fun index => discreteTopology_bot (α index)
  have closed (stage : ℕ) : IsClosed (sets stage) := by
    obtain ⟨indices, base, _, representation⟩ :=
      (mem_measurableCylinders _).mp (cylinders stage)
    rw [representation]
    exact IsClosed.preimage (Finset.continuous_restrict indices) (isClosed_discrete base)
  by_contra never_empty
  have nonempty (stage : ℕ) : (sets stage).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr (fun empty => never_empty ⟨stage, empty⟩)
  have common := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed sets
    (fun stage => decreasing (Nat.le_succ stage)) nonempty (closed 0).isCompact closed
  rw [empty_intersection] at common
  exact Set.not_nonempty_empty common

variable {marginals : ∀ indices : Finset ι, Measure (∀ index : indices, α index)}

theorem content_tendsto_zero (consistent : IsProjectiveMeasureFamily marginals)
    {sets : ℕ → Set (∀ index, α index)}
    (cylinders : ∀ stage, sets stage ∈ measurableCylinders α)
    (decreasing : Antitone sets) (empty_intersection : (⋂ stage, sets stage) = ∅) :
    Tendsto (fun stage => projectiveFamilyContent consistent (sets stage)) atTop (𝓝 0) := by
  obtain ⟨stage, empty⟩ :=
    exists_empty_of_antitone_cylinders cylinders decreasing empty_intersection
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop stage] with later after
  have empty_later : sets later = ∅ :=
    Set.eq_empty_iff_forall_not_mem.mpr (fun point member => by
      have earlier := decreasing after member
      simpa only [empty, Set.mem_empty_iff_false] using earlier)
  simp [empty_later]

variable [∀ indices, IsFiniteMeasure (marginals indices)]

theorem content_sigmaSubadditive (consistent : IsProjectiveMeasureFamily marginals) :
    (projectiveFamilyContent consistent).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun sets cylinders union_cylinder disjoint => ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent consistent) (fun _ _ => projectiveFamilyContent_ne_top consistent)
    (fun cylinders => content_tendsto_zero consistent cylinders)
    cylinders union_cylinder disjoint

def extension (consistent : IsProjectiveMeasureFamily marginals) :
    Measure (∀ index, α index) :=
  (projectiveFamilyContent consistent).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge (content_sigmaSubadditive consistent)

theorem extension_cylinder (consistent : IsProjectiveMeasureFamily marginals)
    (indices : Finset ι) {base : Set (∀ index : indices, α index)}
    (measurable_base : MeasurableSet base) :
    extension consistent (cylinder indices base) = marginals indices base := by
  unfold extension
  rw [AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
    (cylinder_mem_measurableCylinders _ _ measurable_base)]
  exact projectiveFamilyContent_cylinder consistent measurable_base

theorem extension_isProjectiveLimit (consistent : IsProjectiveMeasureFamily marginals) :
    IsProjectiveLimit (extension consistent) marginals := by
  intro indices
  ext base measurable_base
  rw [Measure.map_apply (measurable_restrict indices) measurable_base]
  exact extension_cylinder consistent indices measurable_base

instance extension_isFiniteMeasure (consistent : IsProjectiveMeasureFamily marginals) :
    IsFiniteMeasure (extension consistent) :=
  (extension_isProjectiveLimit consistent).isFiniteMeasure

instance extension_isProbabilityMeasure [∀ indices, IsProbabilityMeasure (marginals indices)]
    (consistent : IsProjectiveMeasureFamily marginals) :
    IsProbabilityMeasure (extension consistent) :=
  (extension_isProjectiveLimit consistent).isProbabilityMeasure

theorem existsUnique_projectiveLimit (consistent : IsProjectiveMeasureFamily marginals) :
    ∃! limit : Measure (∀ index, α index), IsProjectiveLimit limit marginals := by
  refine ⟨extension consistent, extension_isProjectiveLimit consistent, ?_⟩
  intro limit limit_marginals
  exact limit_marginals.unique (extension_isProjectiveLimit consistent)

end InfoGeometry.Measure.FiniteProjectiveExtension
