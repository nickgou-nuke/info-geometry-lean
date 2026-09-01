import InfoGeometry.Twistor.Pin55ExteriorSpinorNativeAction
import InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
import InfoGeometry.Canonical.ProjectiveFoundation

/-!
# Full Pin(5,5) equivariance of projective pure spinors and their annihilator Grassmannian

This owner closes the next Cartan-style edge after native exterior-spinor
annihilator equivariance.

The ingredients are all repository-native:

* `realPin55ExteriorSpinorLinearEquiv` gives the full real split Pin action on
  the Chevalley/Fock carrier `ExteriorAlgebra ℝ V5`;
* `realPin55_annihilator_equivariant` transports annihilator submodules;
* `LinearEquiv.finrank_map_eq` preserves their dimension;
* `ProjectivePureSpinor` is already well-defined under nonzero scaling;
* `ProjectiveFoundation.ProjectiveRepresentation` supplies the genuine
  projective action associated to a linear representation;
* `projectivePureSpinorGrassmannianPoint` is the canonical maximal-neutral
  Grassmannian readout.

Thus purity is preserved by the full `RealPin55` action, this action descends
to projective pure-spinor rays, and the annihilator/Grassmannian readout is
exactly equivariant.

No converse classification of all maximal-neutral 5-planes by pure spinor
rays is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.Pin55ProjectivePureSpinorGrassmannianEquivariance

open scoped LinearAlgebra.Projectivization
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.ProjectiveFoundation
open InfoGeometry.Twistor.Pin55PureSpinorAnnihilatorEquivariance
open InfoGeometry.Twistor.Pin55ExteriorSpinorNativeAction

/-- The native full real split Pin action as a genuine linear representation
on the exterior-spinor carrier. -/
noncomputable def realPin55ExteriorSpinorRepresentation :
    RealPin55 →* (Spinor ≃ₗ[ℝ] Spinor) where
  toFun := realPin55ExteriorSpinorLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro ψ
    change realPin55ExteriorSpinorEnd (1 : RealPin55) ψ = ψ
    rw [realPin55ExteriorSpinorEnd_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro ψ
    change realPin55ExteriorSpinorEnd (g * h) ψ =
      realPin55ExteriorSpinorEnd g (realPin55ExteriorSpinorEnd h ψ)
    rw [realPin55ExteriorSpinorEnd_mul]
    rfl

@[simp] theorem realPin55ExteriorSpinorRepresentation_apply
    (g : RealPin55) (ψ : Spinor) :
    realPin55ExteriorSpinorRepresentation g ψ =
      realPin55ExteriorSpinorLinearEquiv g ψ := by
  rfl

/-- Full real split Pin preserves the concrete split `(5,5)` pure-spinor
predicate. -/
theorem realPin55_isPureSpinor
    (g : RealPin55) {ψ : Spinor} (hψ : IsPureSpinor ψ) :
    IsPureSpinor (realPin55ExteriorSpinorLinearEquiv g ψ) := by
  refine ⟨?_, ?_⟩
  · exact (realPin55ExteriorSpinorLinearEquiv g).map_ne_zero_iff.mpr hψ.1
  · rw [realPin55_annihilator_equivariant]
    rw [(realPin55NeutralTransport g).finrank_map_eq]
    exact hψ.2

/-- The ordinary linear representation, viewed through the repository's
projective-representation interface with trivial multiplier. -/
noncomputable def realPin55ProjectiveRepresentation :
    ProjectiveRepresentation ℝ RealPin55 Spinor :=
  ProjectiveRepresentation.ofLinearHom realPin55ExteriorSpinorRepresentation

/-- The induced full Pin action on real projective spinor space. -/
noncomputable def realPin55ProjectiveSpinorMap
    (g : RealPin55) : ℙ ℝ Spinor → ℙ ℝ Spinor :=
  realPin55ProjectiveRepresentation.projectivizationMap g

@[simp] theorem realPin55ProjectiveSpinorMap_mk
    (g : RealPin55) (ψ : Spinor) (hψ : ψ ≠ 0) :
    realPin55ProjectiveSpinorMap g (Projectivization.mk ℝ ψ hψ) =
      Projectivization.mk ℝ (realPin55ExteriorSpinorLinearEquiv g ψ)
        ((realPin55ExteriorSpinorLinearEquiv g).map_ne_zero_iff.mpr hψ) := by
  exact ProjectiveRepresentation.projectivizationMap_mk
    realPin55ProjectiveRepresentation g ψ hψ

/-- Projective transport composes according to the full Pin group law. -/
theorem realPin55ProjectiveSpinorMap_mul
    (g h : RealPin55) :
    realPin55ProjectiveSpinorMap (g * h) =
      realPin55ProjectiveSpinorMap g ∘ realPin55ProjectiveSpinorMap h := by
  exact ProjectiveRepresentation.projectivizationMap_mul
    realPin55ProjectiveRepresentation g h

@[simp] theorem realPin55ProjectiveSpinorMap_one :
    realPin55ProjectiveSpinorMap (1 : RealPin55) = id := by
  exact ProjectiveRepresentation.projectivizationMap_one
    realPin55ProjectiveRepresentation

/-- The projective pure-spinor locus is stable under the full real split Pin
action. -/
theorem realPin55_projectivePureSpinor
    (g : RealPin55) {p : ℙ ℝ Spinor}
    (hp : p ∈ ProjectivePureSpinor) :
    realPin55ProjectiveSpinorMap g p ∈ ProjectivePureSpinor := by
  induction p using Projectivization.ind with
  | h ψ hψ =>
      rw [realPin55ProjectiveSpinorMap_mk]
      rw [projectivePureSpinor_mk_iff]
      apply realPin55_isPureSpinor g
      exact (projectivePureSpinor_mk_iff ψ hψ).mp hp

/-- A projective pure-spinor point transported by full Pin. -/
noncomputable def realPin55ProjectivePureSpinorMap
    (g : RealPin55)
    (p : {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor}) :
    {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor} :=
  ⟨realPin55ProjectiveSpinorMap g p.1,
    realPin55_projectivePureSpinor g p.2⟩

/-- The projective pure-spinor transport is a genuine `RealPin55` action. -/
noncomputable def realPin55ProjectivePureSpinorAction :
    RealPin55 →* Function.End
      {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor} where
  toFun := realPin55ProjectivePureSpinorMap
  map_one' := by
    ext p
    apply Subtype.ext
    change realPin55ProjectiveSpinorMap (1 : RealPin55) p.1 = p.1
    rw [realPin55ProjectiveSpinorMap_one]
    rfl
  map_mul' g h := by
    ext p
    apply Subtype.ext
    change realPin55ProjectiveSpinorMap (g * h) p.1 =
      realPin55ProjectiveSpinorMap g (realPin55ProjectiveSpinorMap h p.1)
    rw [realPin55ProjectiveSpinorMap_mul]
    rfl

/-- Projective annihilator readout is exactly equivariant under the native full
Pin action. -/
theorem projectivePureSpinorAnnihilator_equivariant
    (g : RealPin55)
    (p : {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor}) :
    projectivePureSpinorAnnihilator
        (realPin55ProjectivePureSpinorMap g p).1 =
      Submodule.map (realPin55NeutralTransport g).toLinearMap
        (projectivePureSpinorAnnihilator p.1) := by
  rcases p with ⟨p, hp⟩
  change projectivePureSpinorAnnihilator
      (realPin55ProjectiveSpinorMap g p) =
    Submodule.map (realPin55NeutralTransport g).toLinearMap
      (projectivePureSpinorAnnihilator p)
  induction p using Projectivization.ind with
  | h ψ hψ =>
      rw [realPin55ProjectiveSpinorMap_mk]
      rw [projectivePureSpinorAnnihilator_mk]
      rw [projectivePureSpinorAnnihilator_mk]
      exact realPin55_annihilator_equivariant g ψ

/-- The canonical maximal-neutral Grassmannian readout commutes with full Pin
transport at the level of its underlying submodule. -/
theorem projectivePureSpinorGrassmannianPoint_equivariant
    (g : RealPin55)
    (p : {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor}) :
    (projectivePureSpinorGrassmannianPoint
        (realPin55ProjectivePureSpinorMap g p)).1 =
      Submodule.map (realPin55NeutralTransport g).toLinearMap
        (projectivePureSpinorGrassmannianPoint p).1 := by
  change projectivePureSpinorAnnihilator
      (realPin55ProjectivePureSpinorMap g p).1 =
    Submodule.map (realPin55NeutralTransport g).toLinearMap
      (projectivePureSpinorAnnihilator p.1)
  exact projectivePureSpinorAnnihilator_equivariant g p

end InfoGeometry.Twistor.Pin55ProjectivePureSpinorGrassmannianEquivariance
