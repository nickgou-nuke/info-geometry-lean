/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldInformationGeometry
import InfoGeometry.Canonical.OperatorErlangenCompatibility
import InfoGeometry.Canonical.SmoothFlowGenerator
import InfoGeometry.Canonical.SmoothVectorFieldSpanSymmetry
import InfoGeometry.Erlangen.SymmetryClosure

/-!
# Arnold's volume-preserving flow and Erlangen symmetry closure

The algebraically generated subgroup of a family of measure-preserving flows
lies in the existing SDiff subgroup. Its Erlangen closure for the **measure
action** also lies in that subgroup. Equality with all of SDiff is not assumed:
additional common invariant measures can impose further constraints.

Joint stabilization is expressed by intersections and by restricting the
conjugation action to the measure stabilizer. The resulting orbit quotients
are native homogeneous coset spaces, without a normality or manifold claim.
The final section applies the construction and generator equivariance to the
actual real Arnold flow already defined in `ArnoldInformationGeometry`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure

open MeasureTheory
open FlowConjugation SmoothDiffeomorphismPushforward SmoothFlowGenerator
open InfoGeometry.Erlangen.SymmetryClosure
open scoped FlowConjugation SmoothDiffeomorphismPushforward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every selected time map preserves the measure exactly when the generated
subgroup lies in its stabilizer. -/
theorem generatedFlowSubgroup_le_measure_stabilizer_iff
    (μ : Measure E) (F : Set (Multiplicative ℝ →* smoothDiffeomorphismSubgroup E)) :
    generatedFlowSubgroup F ≤ MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ ↔
      ∀ Φ ∈ F, ∀ t, Φ t • μ = μ :=
  generatedFlowSubgroup_le_iff F (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ)

/-- The chosen measure is an actual fixed point of the generated action. -/
theorem measure_mem_fixedPoints_generatedFlowSubgroup
    (μ : Measure E) (F : Set (Multiplicative ℝ →* smoothDiffeomorphismSubgroup E))
    (hF : ∀ Φ ∈ F, ∀ t, Φ t • μ = μ) :
    μ ∈ MulAction.fixedPoints (generatedFlowSubgroup F) (Measure E) :=
  (mem_fixedPoints_iff_le_stabilizer _ μ).mpr
    ((generatedFlowSubgroup_le_measure_stabilizer_iff μ F).mpr hF)

/-- Volume invariance bounds the Erlangen closure for the measure carrier by
the actual SDiff subgroup, viewed inside the acting smooth group. -/
theorem sdiff_erlangen_closure_of_volume_invariant_flows
    (μ : Measure E) (F : Set (Multiplicative ℝ →* smoothDiffeomorphismSubgroup E))
    (hF : ∀ Φ ∈ F, ∀ t, Φ t • μ = μ) :
    subgroupClosure (smoothDiffeomorphismSubgroup E) (Measure E) (generatedFlowSubgroup F) ≤
      (smoothVolumePreservingSubgroup μ).comap
        (smoothDiffeomorphismSubgroup E).subtype := by
  rw [← measure_stabilizer_eq_comap]
  exact (subgroupClosure_le_stabilizer_iff _ μ).mpr
    ((generatedFlowSubgroup_le_measure_stabilizer_iff μ F).mpr hF)

/-- The generated flow subgroup itself lies in the same SDiff carrier. -/
theorem generatedFlowSubgroup_le_sdiff
    (μ : Measure E) (F : Set (Multiplicative ℝ →* smoothDiffeomorphismSubgroup E))
    (hF : ∀ Φ ∈ F, ∀ t, Φ t • μ = μ) :
    generatedFlowSubgroup F ≤ (smoothVolumePreservingSubgroup μ).comap
      (smoothDiffeomorphismSubgroup E).subtype :=
  (le_subgroupClosure (X := Measure E) (generatedFlowSubgroup F)).trans
    (sdiff_erlangen_closure_of_volume_invariant_flows μ F hF)

/-- Adjoining a flow to a measure gives an intersection of actual stabilizers. -/
theorem measure_flow_stabilizer_eq_inf (μ : Measure E)
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) :
    MulAction.stabilizer (smoothDiffeomorphismSubgroup E) (μ, Φ) =
      MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ ⊓
        Subgroup.centralizer (Set.range Φ) := by
  rw [stabilizer_prod_eq_inf, stabilizer_eq_centralizer_range]

/-- Joint measure/flow symmetries form a subgroup of SDiff. -/
theorem measure_flow_stabilizer_le_sdiff (μ : Measure E)
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) :
    MulAction.stabilizer (smoothDiffeomorphismSubgroup E) (μ, Φ) ≤
      (smoothVolumePreservingSubgroup μ).comap
        (smoothDiffeomorphismSubgroup E).subtype := by
  rw [measure_flow_stabilizer_eq_inf, ← measure_stabilizer_eq_comap]
  exact inf_le_left

/-- The joint invariant carrier retains both constraints under closure. -/
theorem joint_erlangen_closure_le_measure_flow_stabilizer_iff
    (μ : Measure E) (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E)
    (H : Subgroup (smoothDiffeomorphismSubgroup E)) :
    subgroupClosure (smoothDiffeomorphismSubgroup E)
        (Measure E × (Multiplicative ℝ →* smoothDiffeomorphismSubgroup E)) H ≤
        MulAction.stabilizer (smoothDiffeomorphismSubgroup E) (μ, Φ) ↔
      H ≤ MulAction.stabilizer (smoothDiffeomorphismSubgroup E) (μ, Φ) :=
  subgroupClosure_le_stabilizer_iff H (μ, Φ)

/-- The orbit of a flow under SDiff is a coset space of its restricted
centralizer. No quotient-group structure is asserted. -/
def sdiffFlowOrbitEquivQuotient (μ : Measure E)
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) :
    MulAction.orbit (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ) Φ ≃
      (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ) ⧸
        (Subgroup.centralizer (Set.range Φ)).comap
          (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ).subtype := by
  rw [← stabilizer_eq_centralizer_range, ← stabilizer_restrict_eq_comap]
  exact MulAction.orbitEquivQuotientStabilizer
    (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ) Φ

/-- Include a restricted flow symmetry in the ambient joint stabilizer. -/
theorem sdiff_flow_symmetry_map_eq_joint_stabilizer (μ : Measure E)
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) :
    (MulAction.stabilizer (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ) Φ).map
        (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ).subtype =
      MulAction.stabilizer (smoothDiffeomorphismSubgroup E) (μ, Φ) := by
  rw [stabilizer_prod_eq_inf]
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.property, hh⟩
  · rintro ⟨hμ, hΦ⟩
    exact ⟨⟨g, hμ⟩, hΦ, rfl⟩

section Arnold

open InfoGeometry.Canonical.NavierStokesShearReconstruction
open ArnoldBeltramiFlow ArnoldInformationGeometry

/-- The existing physical flow has its stated velocity as actual derivative
at time zero. -/
theorem hasDerivAt_smoothFlowHom_zero (s : ℝ) (x : Space) :
    HasDerivAt (fun t : ℝ => (smoothFlowHom s (Multiplicative.ofAdd t)).val x)
      (velocity s x) 0 := by
  change HasDerivAt (fun t : ℝ => flow s t x) (velocity s x) 0
  simpa only [flow_zero] using hasDerivAt_flow s 0 x

/-- Coordinate changes transport the actual Arnold generator by the chain rule. -/
theorem hasDerivAt_conjugate_arnold (s : ℝ)
    (g : smoothDiffeomorphismSubgroup Space) (y : Space) :
    HasDerivAt (fun t : ℝ => ((g • smoothFlowHom s) (Multiplicative.ofAdd t)).val y)
      (pushforward g (velocity s) y) 0 :=
  hasDerivAt_conjugateFlow (smoothFlowHom s) (velocity s)
    (hasDerivAt_smoothFlowHom_zero s) g y

/-- The physical flow's centralizer preserves its actual velocity. -/
theorem arnold_flow_symmetry_le_velocity_symmetry (s : ℝ) :
    Subgroup.centralizer (Set.range (smoothFlowHom s)) ≤
      vectorFieldSymmetrySubgroup (velocity s) := by
  rw [← stabilizer_eq_centralizer_range]
  exact flowSymmetry_le_vectorFieldSymmetry (smoothFlowHom s) (velocity s)
    (hasDerivAt_smoothFlowHom_zero s)

/-- Every time map preserves the Arnold velocity under derivative pushforward. -/
theorem arnold_flow_pushforward_velocity (s : ℝ) (t : Multiplicative ℝ) :
    pushforward (smoothFlowHom s t) (velocity s) = velocity s :=
  flow_pushforward_generator (smoothFlowHom s) (velocity s)
    (hasDerivAt_smoothFlowHom_zero s) t

/-- The whole displayed family, allowing every real parameter, generates a
subgroup whose measure-action Erlangen closure still preserves volume. -/
theorem arnold_family_erlangen_closure_le_sdiff :
    subgroupClosure (smoothDiffeomorphismSubgroup Space) (Measure Space)
        (generatedFlowSubgroup (Set.range smoothFlowHom)) ≤
      (smoothVolumePreservingSubgroup (volume : Measure Space)).comap
        (smoothDiffeomorphismSubgroup Space).subtype := by
  apply sdiff_erlangen_closure_of_volume_invariant_flows
  rintro Φ ⟨s, rfl⟩ t
  exact smoothFlowHom_fixes_volume s t

/-- Each time map is a joint volume/flow symmetry, without requiring the
Beltrami unit-sign condition. -/
theorem arnold_time_map_mem_joint_stabilizer (s : ℝ) (t : Multiplicative ℝ) :
    smoothFlowHom s t ∈ MulAction.stabilizer (smoothDiffeomorphismSubgroup Space)
      ((volume : Measure Space), smoothFlowHom s) := by
  rw [stabilizer_prod_eq_inf]
  exact ⟨smoothFlowHom_mem_stabilizer s t,
    flow_value_mem_stabilizer (smoothFlowHom s) t⟩

end Arnold

end InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure
