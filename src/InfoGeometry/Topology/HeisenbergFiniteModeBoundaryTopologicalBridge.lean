/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit

/-!
# Topological Readout for the Finite-Mode Heisenberg Boundary Bridge

This module packages the finite-mode Heisenberg boundary exhaustion into the
subtype bundle `HeisenbergFiniteModeBoundaryBundle`, constructs the canonical
section `topologicalHeisenbergFiniteModeBoundaryBundle`, and proves continuity,
local constancy, and `TopCat` retraction identities.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge`:
    `heisenbergFiniteMode_boundaryReadout`.
  * `InfoGeometry.Canonical.HeisenbergFiniteModeColimit`:
    `heisenbergFiniteModeDiagram`, `heisenbergFiniteModeColimitMap`.
- BUCKET 2 (Deconfabulation):
  * Replaced the 4-field `structure HeisenbergFiniteModeBoundaryPacket` wrapper with
    the explicit subtype carrier `def HeisenbergFiniteModeBoundaryBundle` and explicit
    projection functions.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `HeisenbergFiniteModeBoundaryBundle`, `HeisenbergFiniteModeBoundaryBundle.current`,
    `HeisenbergFiniteModeBoundaryBundle.stage`, `HeisenbergFiniteModeBoundaryBundle.stageElem`,
    `HeisenbergFiniteModeBoundaryBundle.boundaryEq`.
  * `topologicalHeisenbergFiniteModeBoundaryBundle`,
    `topologicalHeisenbergFiniteModeBoundaryBundle_current`.
  * `continuous_topologicalHeisenbergFiniteModeBoundaryBundle`,
    `isLocallyConstant_topologicalHeisenbergFiniteModeBoundaryBundle`.
  * `section_projection`, `section_projection_apply`: categorical retraction in `TopCat`.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeBoundaryTopologicalBridge

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical
open InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergAlgebraTopologicalSpace :
    TopologicalSpace (HeisenbergAlgebra 𝕜) := ⊥

instance heisenbergAlgebraDiscreteTopology :
    DiscreteTopology (HeisenbergAlgebra 𝕜) := DiscreteTopology.mk (Eq.refl _)

/-- Subtype carrier of finite-mode Heisenberg boundary triples `(current, stage, stageElem)`
whose stage colimit image equals `current`. -/
def HeisenbergFiniteModeBoundaryBundle : Type _ :=
  { p : HeisenbergAlgebra 𝕜 ×
      (Σ s : Finset (Option ℤ), InfoGeometry.Canonical.heisenbergFiniteModeStage (𝕜 := 𝕜) s) //
    (InfoGeometry.Canonical.heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
      ((colimit.ι (InfoGeometry.Canonical.heisenbergFiniteModeDiagram (𝕜 := 𝕜)) p.2.1).hom p.2.2) =
      p.1 }

/-- Target Heisenberg algebra element of a boundary bundle point. -/
def HeisenbergFiniteModeBoundaryBundle.current
    (p : HeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜)) : HeisenbergAlgebra 𝕜 :=
  p.1.1

/-- Finite mode support stage of a boundary bundle point. -/
def HeisenbergFiniteModeBoundaryBundle.stage
    (p : HeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜)) : Finset (Option ℤ) :=
  p.1.2.1

/-- Stage vector of a boundary bundle point. -/
def HeisenbergFiniteModeBoundaryBundle.stageElem
    (p : HeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜)) :
    InfoGeometry.Canonical.heisenbergFiniteModeStage (𝕜 := 𝕜) p.stage :=
  p.1.2.2

/-- Colimit readout equality of a boundary bundle point. -/
theorem HeisenbergFiniteModeBoundaryBundle.boundaryEq
    (p : HeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜)) :
    (InfoGeometry.Canonical.heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
        ((colimit.ι (InfoGeometry.Canonical.heisenbergFiniteModeDiagram (𝕜 := 𝕜)) p.stage).hom
          p.stageElem) =
      p.current := by
  unfold HeisenbergFiniteModeBoundaryBundle.stage HeisenbergFiniteModeBoundaryBundle.stageElem
    HeisenbergFiniteModeBoundaryBundle.current
  exact p.2

instance heisenbergFiniteModeBoundaryBundleTopologicalSpace :
    TopologicalSpace (HeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜)) := ⊥

instance heisenbergFiniteModeBoundaryBundleDiscreteTopology :
    DiscreteTopology (HeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜)) := DiscreteTopology.mk (Eq.refl _)

/-- The canonical boundary bundle point selected from the finite-mode exhaustion. -/
noncomputable def topologicalHeisenbergFiniteModeBoundaryBundle
    (X : HeisenbergAlgebra 𝕜) :
    HeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜) := by
  classical
  let s : Finset (Option ℤ) :=
    Classical.choose
      (InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge.heisenbergFiniteMode_boundaryReadout
        (𝕜 := 𝕜) X)
  have hxStage :
      ∃ x : heisenbergFiniteModeStage (𝕜 := 𝕜) s,
        (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
          ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X :=
    Classical.choose_spec
      (InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge.heisenbergFiniteMode_boundaryReadout
        (𝕜 := 𝕜) X)
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s :=
    Classical.choose hxStage
  have hx :
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
        ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X :=
    Classical.choose_spec hxStage
  exact ⟨(X, ⟨s, x⟩), hx⟩

/-- Base current projection of `topologicalHeisenbergFiniteModeBoundaryBundle X`. -/
@[simp] theorem topologicalHeisenbergFiniteModeBoundaryBundle_current
    (X : HeisenbergAlgebra 𝕜) :
    (topologicalHeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜) X).current = X := by
  unfold topologicalHeisenbergFiniteModeBoundaryBundle HeisenbergFiniteModeBoundaryBundle.current
  exact Eq.refl _

/-- The canonical boundary bundle section is continuous on the discrete Heisenberg carrier. -/
theorem continuous_topologicalHeisenbergFiniteModeBoundaryBundle :
    Continuous (topologicalHeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜)) := by
  unfold topologicalHeisenbergFiniteModeBoundaryBundle
  exact continuous_of_discreteTopology

/-- The canonical boundary bundle section is locally constant on the discrete Heisenberg carrier. -/
theorem isLocallyConstant_topologicalHeisenbergFiniteModeBoundaryBundle :
    IsLocallyConstant (topologicalHeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜)) := by
  unfold topologicalHeisenbergFiniteModeBoundaryBundle
  exact IsLocallyConstant.of_discrete

/-- The boundary bundle viewed as a `TopCat` object. -/
abbrev topCat : TopCat :=
  TopCat.of (HeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜))

/-- The Heisenberg carrier viewed as a `TopCat` object. -/
abbrev parameterTopCat : TopCat :=
  TopCat.of (HeisenbergAlgebra 𝕜)

/-- The canonical projection from the boundary bundle to its Heisenberg current. -/
noncomputable def projection : topCat (𝕜 := 𝕜) ⟶ parameterTopCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  refine ⟨fun p => p.current, ?_⟩
  exact continuous_of_discreteTopology

/-- The canonical section of the projection built from the finite-mode boundary readout. -/
noncomputable def boundarySection : parameterTopCat (𝕜 := 𝕜) ⟶ topCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  refine ⟨fun X => topologicalHeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜) X, ?_⟩
  exact continuous_topologicalHeisenbergFiniteModeBoundaryBundle (𝕜 := 𝕜)

/-- Categorical retraction law `boundarySection ≫ projection = 𝟙 _` in `TopCat`. -/
@[simp] theorem section_projection :
    boundarySection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext X
  unfold boundarySection projection
  exact topologicalHeisenbergFiniteModeBoundaryBundle_current (𝕜 := 𝕜) X

/-- Pointwise evaluation of `boundarySection ≫ projection` on `X : HeisenbergAlgebra 𝕜`. -/
@[simp] theorem section_projection_apply (X : HeisenbergAlgebra 𝕜) :
    (boundarySection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜)) X = X := by
  rw [section_projection (𝕜 := 𝕜)]
  exact Eq.refl _

end
end InfoGeometry.Topology.HeisenbergFiniteModeBoundaryTopologicalBridge
