/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SmoothVolumePreservingGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Smooth symmetry, measure orbits and external mass scaling

The native group of smooth homeomorphisms acts on native measures by
pushforward. Its stabilizer is exactly the previously constructed smooth
measure-preserving subgroup, restricted to the smooth group. The actual orbit
is therefore a native coset quotient. No transitivity on all smooth densities,
infinite-dimensional manifold or Lie-groupoid structure is assumed.

Pushforward preserves total mass. Consequently a nonzero finite measure can
be carried to a scalar multiple of itself only when the scalar is one.
External scalar multiplication commutes with this action but is not a
nontrivial motion inside such a finite-mass orbit.
-/

noncomputable section

namespace InfoGeometry.Canonical

open MeasureTheory
open scoped ContDiff ENNReal

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The native subgroup of homeomorphisms smooth in both directions. -/
def smoothDiffeomorphismSubgroup : Subgroup (E ≃ₜ E) where
  carrier := {e | ContDiff ℝ ∞ (e : E → E) ∧ ContDiff ℝ ∞ (e.symm : E → E)}
  one_mem' := ⟨contDiff_id, contDiff_id⟩
  mul_mem' := by
    intro f g hf hg
    exact ⟨hf.1.comp hg.1, hg.2.comp hf.2⟩
  inv_mem' := by
    intro f hf
    exact ⟨hf.2, hf.1⟩

variable {E} [MeasurableSpace E] [BorelSpace E]

/-- Pushforward is the actual measure action of the smooth group. -/
instance smoothDiffeomorphismMeasureAction :
    MulAction (smoothDiffeomorphismSubgroup E) (Measure E) where
  smul g μ := μ.map (g.val : E → E)
  one_smul μ := Measure.map_id
  mul_smul g h μ := by
    change μ.map (g.val ∘ h.val) = (μ.map h.val).map g.val
    exact (Measure.map_map g.val.continuous.measurable h.val.continuous.measurable).symm

@[simp] theorem smoothDiffeomorphism_smul_eq_map
    (g : smoothDiffeomorphismSubgroup E) (μ : Measure E) :
    g • μ = μ.map (g.val : E → E) := rfl

/-- The existing volume-preserving subgroup is contained in the smooth group. -/
theorem smoothVolumePreserving_le_smooth (μ : Measure E) :
    smoothVolumePreservingSubgroup μ ≤ smoothDiffeomorphismSubgroup E :=
  fun _ h => ⟨h.1, h.2.1⟩

/-- The stabilizer of a measure is exactly the existing smooth
measure-preserving subgroup, viewed inside the smooth group. -/
theorem measure_stabilizer_eq_comap (μ : Measure E) :
    MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ =
      (smoothVolumePreservingSubgroup μ).comap
        (smoothDiffeomorphismSubgroup E).subtype := by
  ext g
  change (μ.map (g.val : E → E) = μ) ↔
    ContDiff ℝ ∞ (g.val : E → E) ∧
      ContDiff ℝ ∞ (g.val.symm : E → E) ∧ MeasurePreserving g.val μ μ
  constructor
  · intro h
    exact ⟨g.property.1, g.property.2, g.val.continuous.measurable, h⟩
  · exact fun h => h.2.2.map_eq

/-- Actual pushforward orbits, with the existing SDiff stabilizer, are native
coset spaces. This does not identify the orbit with all positive densities. -/
def measureOrbitEquivQuotient (μ : Measure E) :
    MulAction.orbit (smoothDiffeomorphismSubgroup E) μ ≃
      (smoothDiffeomorphismSubgroup E) ⧸
        (smoothVolumePreservingSubgroup μ).comap
          (smoothDiffeomorphismSubgroup E).subtype := by
  rw [← measure_stabilizer_eq_comap]
  exact MulAction.orbitEquivQuotientStabilizer (smoothDiffeomorphismSubgroup E) μ

/-- Every element of the actual orbit has the same total mass. -/
theorem measureOrbit_totalMass (μ : Measure E)
    (ν : MulAction.orbit (smoothDiffeomorphismSubgroup E) μ) :
    ν.val Set.univ = μ Set.univ := by
  rcases ν.property with ⟨g, hg⟩
  rw [← hg]
  change μ.map (g.val : E → E) Set.univ = μ Set.univ
  rw [Measure.map_apply g.val.continuous.measurable MeasurableSet.univ,
    Set.preimage_univ]

/-- External mass scaling commutes with smooth pushforward. -/
theorem smoothDiffeomorphism_smul_measure_scale
    (g : smoothDiffeomorphismSubgroup E) (c : ℝ≥0∞) (μ : Measure E) :
    g • (c • μ) = c • (g • μ) :=
  Measure.map_smul c g.val.continuous.measurable.aemeasurable

/-- A finite nonzero measure cannot change its total mass within its orbit. -/
theorem scale_eq_one_of_mem_measureOrbit (μ : Measure E) [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) (c : ℝ≥0∞)
    (hc : c • μ ∈ MulAction.orbit (smoothDiffeomorphismSubgroup E) μ) : c = 1 := by
  have hmass := measureOrbit_totalMass μ ⟨c • μ, hc⟩
  have hmass0 : μ Set.univ ≠ 0 := by
    exact fun h => hμ (Measure.measure_univ_eq_zero.mp h)
  apply (ENNReal.mul_left_inj hmass0 (measure_ne_top μ Set.univ)).mp
  simpa only [Measure.smul_apply, smul_eq_mul, one_mul] using hmass

/-- Exact characterization of scalar multiples that belong to a finite,
nonzero smooth measure orbit. -/
theorem scale_mem_measureOrbit_iff (μ : Measure E) [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) (c : ℝ≥0∞) :
    c • μ ∈ MulAction.orbit (smoothDiffeomorphismSubgroup E) μ ↔ c = 1 := by
  constructor
  · exact scale_eq_one_of_mem_measureOrbit μ hμ c
  · intro hc
    subst c
    exact ⟨1, by simp⟩

end InfoGeometry.Canonical
