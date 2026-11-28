/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldBeltramiSmoothFlow
import InfoGeometry.Canonical.FlowConjugation
import InfoGeometry.Canonical.FlowErlangenClosure
import InfoGeometry.Canonical.SmoothVectorFieldPushforward

/-!
# Arnold's volume-preserving flows and Erlangen symmetry closure

The actual smooth group acts on measures, vector fields and algebraic
one-parameter motions. These are different action carriers. A common invariant
measure confines the measure-action Galois closure to its SDiff stabilizer.
Differentiating a conjugated motion intertwines the flow action and the
Fréchet pushforward action on its generator.

The concrete instance uses the existing real Beltrami flow and its proved
particle ODE. Restricted flow symmetry inside SDiff is the intersection of
the image centralizer with the volume stabilizer, with an actual orbit/coset
equivalence. No transitivity on all densities, quotient-manifold structure,
ODE uniqueness, or equality of an arbitrary closure with SDiff is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure

open MeasureTheory
open FlowConjugation FlowErlangenClosure
open scoped VectorFieldPushforward

attribute [local instance] flowConjugationAction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Generators

/-- The analytic intertwining theorem with the actual flow conjugation action. -/
theorem hasDerivAt_flow_action_zero
    (g : smoothDiffeomorphismSubgroup E)
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) (X : E → E)
    (hΦ : ∀ x : E, HasDerivAt
      (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0)
    (y : E) :
    HasDerivAt (fun t : ℝ => ((g • Φ) (Multiplicative.ofAdd t)).val y)
      ((g • X) y) 0 :=
  hasDerivAt_conjugatedFlow_zero g Φ X hΦ y

/-- A symmetry of every time map is a symmetry of the derivative generator.
The reverse inclusion would require a separate uniqueness argument. -/
theorem flow_stabilizer_le_generator_stabilizer
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) (X : E → E)
    (hΦ : ∀ x : E, HasDerivAt
      (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0) :
    MulAction.stabilizer (smoothDiffeomorphismSubgroup E) Φ ≤
      MulAction.stabilizer (smoothDiffeomorphismSubgroup E) X := by
  intro g hg
  apply smoothDiffeomorphism_fixes_generator_of_fixes_flow g Φ X hΦ
  intro t
  exact DFunLike.congr_fun hg t

/-- Klein transport for the genuine derivative action on fields. -/
theorem klein_abbildung_vectorField_symmetry_conjugation
    (g : smoothDiffeomorphismSubgroup E) (X : E → E) :
    MulAction.stabilizer (smoothDiffeomorphismSubgroup E) (g • X) =
      (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) X).map
        (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g X

/-- The actual orbit of a field under derivative pushforward is a native
coset quotient by its symmetry subgroup. -/
def vectorFieldOrbitEquivQuotient (X : E → E) :
    MulAction.orbit (smoothDiffeomorphismSubgroup E) X ≃
      (smoothDiffeomorphismSubgroup E) ⧸
        MulAction.stabilizer (smoothDiffeomorphismSubgroup E) X :=
  MulAction.orbitEquivQuotientStabilizer (smoothDiffeomorphismSubgroup E) X

end Generators

section Measures

variable [MeasurableSpace E] [BorelSpace E]

/-- Fixing the reference measure as an Erlangen absolute is exactly the
existing SDiff subgroup restricted to the smooth acting group. -/
theorem fixing_reference_measure_eq_sdiff (μ : Measure E) :
    fixingSubgroup (smoothDiffeomorphismSubgroup E) ({μ} : Set (Measure E)) =
      (smoothVolumePreservingSubgroup μ).comap
        (smoothDiffeomorphismSubgroup E).subtype := by
  rw [FlowErlangenClosure.fixingSubgroup_singleton, measure_stabilizer_eq_comap]

/-- A subgroup and its measure-action closure have exactly the same SDiff
containment condition. This is not equality of the closure with SDiff. -/
theorem measure_symmetryClosure_le_sdiff_iff
    (μ : Measure E) (H : Subgroup (smoothDiffeomorphismSubgroup E)) :
    symmetryClosure (smoothDiffeomorphismSubgroup E) (Measure E) H ≤
        (smoothVolumePreservingSubgroup μ).comap
          (smoothDiffeomorphismSubgroup E).subtype ↔
      H ≤ (smoothVolumePreservingSubgroup μ).comap
        (smoothDiffeomorphismSubgroup E).subtype := by
  rw [← measure_stabilizer_eq_comap]
  exact symmetryClosure_le_stabilizer_iff H μ

/-- SDiff itself is closed for the measure-action Erlangen closure. -/
theorem sdiff_measure_symmetryClosure (μ : Measure E) :
    symmetryClosure (smoothDiffeomorphismSubgroup E) (Measure E)
        ((smoothVolumePreservingSubgroup μ).comap
          (smoothDiffeomorphismSubgroup E).subtype) =
      (smoothVolumePreservingSubgroup μ).comap
        (smoothDiffeomorphismSubgroup E).subtype := by
  rw [← measure_stabilizer_eq_comap, symmetryClosure_stabilizer]

/-- Any family of measure-invariant motions has its generated subgroup and
its measure-action Erlangen closure inside SDiff. No existence theorem for
flows of arbitrary divergence-free fields is assumed. -/
theorem sdiff_erlangen_closure_of_volume_invariant_flows
    {ι Time : Type*} [Monoid Time] (μ : Measure E)
    (Φ : ι → Time →* smoothDiffeomorphismSubgroup E)
    (hfix : ∀ i t, Φ i t • μ = μ) :
    flowFamilySubgroup Φ ≤
        symmetryClosure (smoothDiffeomorphismSubgroup E) (Measure E) (flowFamilySubgroup Φ) ∧
      symmetryClosure (smoothDiffeomorphismSubgroup E) (Measure E) (flowFamilySubgroup Φ) ≤
        (smoothVolumePreservingSubgroup μ).comap
          (smoothDiffeomorphismSubgroup E).subtype := by
  rw [← measure_stabilizer_eq_comap]
  exact flowFamilySubgroup_le_symmetryClosure_le_stabilizer Φ μ hfix

/-- Restricting pointwise flow symmetry to SDiff takes the actual subgroup
intersection when mapped back to the smooth group. -/
theorem flow_symmetry_within_sdiff_map
    (μ : Measure E) (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) :
    ((Subgroup.centralizer (Set.range Φ)).subgroupOf
        (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ)).map
        (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ).subtype =
      Subgroup.centralizer (Set.range Φ) ⊓
        (smoothVolumePreservingSubgroup μ).comap
          (smoothDiffeomorphismSubgroup E).subtype := by
  rw [Subgroup.subgroupOf_map_subtype, measure_stabilizer_eq_comap]

/-- The restricted symmetry subgroup sits inside SDiff as an ambient
subgroup of the smooth diffeomorphism group. -/
theorem flow_symmetry_within_sdiff_le
    (μ : Measure E) (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) :
    ((Subgroup.centralizer (Set.range Φ)).subgroupOf
        (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ)).map
        (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ).subtype ≤
      (smoothVolumePreservingSubgroup μ).comap
        (smoothDiffeomorphismSubgroup E).subtype := by
  rw [flow_symmetry_within_sdiff_map]
  exact inf_le_right

/-- Actual orbits under SDiff, with centralizer intersection as the
isotropy subgroup. This is an equivalence of types. -/
def sdiffFlowOrbitEquivCentralizerQuotient
    (μ : Measure E) (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) :
    MulAction.orbit (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ) Φ ≃
      (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ) ⧸
        (Subgroup.centralizer (Set.range Φ)).subgroupOf
          (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ) := by
  rw [← flow_stabilizer_eq_centralizer]
  exact MulAction.orbitEquivQuotientStabilizer
    (MulAction.stabilizer (smoothDiffeomorphismSubgroup E) μ) Φ

end Measures

section Beltrami

open NavierStokesShearReconstruction ArnoldBeltramiFlow ArnoldInformationGeometry

/-- The concrete generator hypothesis comes from the proved particle ODE. -/
theorem smoothFlowHom_hasDerivAt_zero (s : ℝ) (x : Space) :
    HasDerivAt (fun t : ℝ => (smoothFlowHom s (Multiplicative.ofAdd t)).val x)
      (velocity s x) 0 := by
  change HasDerivAt (fun t : ℝ => flow s t x) (velocity s x) 0
  simpa only [velocity_flow] using hasDerivAt_flow s 0 x

/-- The entire displayed Beltrami family has measure-action closure inside
the actual volume-preserving subgroup. -/
theorem beltrami_flowFamily_closure_le_sdiff :
    symmetryClosure (smoothDiffeomorphismSubgroup Space) (Measure Space)
        (flowFamilySubgroup smoothFlowHom) ≤
      (smoothVolumePreservingSubgroup (volume : Measure Space)).comap
        (smoothDiffeomorphismSubgroup Space).subtype :=
  (sdiff_erlangen_closure_of_volume_invariant_flows volume smoothFlowHom
    smoothFlowHom_fixes_volume).2

/-- A group centralizer of the actual Beltrami motion preserves its
velocity field under the actual derivative pushforward. -/
theorem beltrami_centralizer_le_velocity_stabilizer (s : ℝ) :
    Subgroup.centralizer (Set.range (smoothFlowHom s)) ≤
      MulAction.stabilizer (smoothDiffeomorphismSubgroup Space) (velocity s) := by
  rw [← flow_stabilizer_eq_centralizer]
  exact flow_stabilizer_le_generator_stabilizer
    (smoothFlowHom s) (velocity s) (smoothFlowHom_hasDerivAt_zero s)

/-- Every time map fixes its own velocity generator. The commutation used
here follows from the actual homomorphism and commutative real time. -/
theorem beltrami_flow_fixes_velocity (s : ℝ) (t : Multiplicative ℝ) :
    smoothFlowHom s t • velocity s = velocity s := by
  apply flow_stabilizer_le_generator_stabilizer (smoothFlowHom s) (velocity s)
    (smoothFlowHom_hasDerivAt_zero s)
  rw [mem_flow_stabilizer_iff]
  intro r
  rw [← map_mul, ← map_mul, mul_comm t r]

/-- The same concrete time map fixes the measure and the field. These two
invariants live in the native product action, with derivative action on the
field factor. -/
theorem beltrami_flow_fixes_volume_velocity (s : ℝ) (t : Multiplicative ℝ) :
    smoothFlowHom s t • ((volume : Measure Space), velocity s) =
      ((volume : Measure Space), velocity s) := by
  exact Prod.ext (smoothFlowHom_fixes_volume s t) (beltrami_flow_fixes_velocity s t)

/-- Choosing both volume and velocity as invariant data gives a closure
inside their actual stabilizer intersection. This illustrates why the
invariant carrier is part of the closure construction. -/
theorem beltrami_joint_closure_le_volume_velocity_stabilizer (s : ℝ) :
    symmetryClosure (smoothDiffeomorphismSubgroup Space)
        (Measure Space × (Space → Space)) (smoothFlowHom s).range ≤
      MulAction.stabilizer (smoothDiffeomorphismSubgroup Space) (volume : Measure Space) ⊓
        MulAction.stabilizer (smoothDiffeomorphismSubgroup Space) (velocity s) := by
  have hfix : ((volume : Measure Space), velocity s) ∈
      MulAction.fixedPoints (smoothFlowHom s).range (Measure Space × (Space → Space)) := by
    rintro ⟨g, hg⟩
    rcases hg with ⟨t, rfl⟩
    exact beltrami_flow_fixes_volume_velocity s t
  have hbound := symmetryClosure_le_stabilizer_of_fixed hfix
  intro g hg
  exact ⟨congrArg Prod.fst (hbound hg), congrArg Prod.snd (hbound hg)⟩

end Beltrami

end InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure
