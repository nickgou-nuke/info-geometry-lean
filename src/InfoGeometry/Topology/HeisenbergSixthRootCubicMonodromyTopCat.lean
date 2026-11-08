/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyBridge

/-!
# TopCat Packaging for the Heisenberg Sixth-Root / Cubic Monodromy Bundle

This module defines the dependent product bundle `Bundle` storing the Heisenberg charge
parameter, sixth-root parameter, Heisenberg boundary atlas, effective cubic root, and
Klein-bottle colour monodromy operator, realizes `Bundle` and `𝕜 × SixthRootParameter`
in `TopCat`, and proves the categorical retraction law `readout ≫ projection = 𝟙 _`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyBridge`:
    `heisenbergSixthRootCubicMonodromyReadout`.
- BUCKET 2 (Deconfabulation):
  * Replaced the 5-field `structure Packet` wrapper with the dependent product carrier
    `def Bundle` and explicit projection functions `Bundle.α`, `Bundle.q`,
    `Bundle.heisenberg`, `Bundle.cubicRoot`, `Bundle.monodromy`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `Bundle`, `Bundle.α`, `Bundle.q`, `Bundle.heisenberg`, `Bundle.cubicRoot`,
    `Bundle.monodromy`.
  * `topCat`, `parameterTopCat`, `projection`, `readout`.
  * `projection_readout`, `projection_readout_apply`: categorical retraction in `TopCat`.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyTopCat

open CategoryTheory
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyBridge
open InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Dependent product carrier storing the Heisenberg charge parameter, sixth-root
parameter, Heisenberg boundary atlas, effective cubic root, and colour monodromy operator. -/
def Bundle : Type _ :=
  Σ α : 𝕜,
    SixthRootParameter ×
      (InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
        (CubicRootParameter × ColourOperator))

/-- Charge parameter coordinate of a monodromy bundle point. -/
def Bundle.α (p : Bundle (𝕜 := 𝕜)) : 𝕜 :=
  p.1

/-- Sixth-root parameter coordinate of a monodromy bundle point. -/
def Bundle.q (p : Bundle (𝕜 := 𝕜)) : SixthRootParameter :=
  p.2.1

/-- Heisenberg boundary atlas component of a monodromy bundle point. -/
def Bundle.heisenberg (p : Bundle (𝕜 := 𝕜)) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) p.α :=
  p.2.2.1

/-- Effective cubic-root component of a monodromy bundle point. -/
def Bundle.cubicRoot (p : Bundle (𝕜 := 𝕜)) : CubicRootParameter :=
  p.2.2.2.1

/-- Klein-bottle colour monodromy operator component of a monodromy bundle point. -/
def Bundle.monodromy (p : Bundle (𝕜 := 𝕜)) : ColourOperator :=
  p.2.2.2.2

instance bundleTopologicalSpace : TopologicalSpace (Bundle (𝕜 := 𝕜)) := ⊥

instance bundleDiscreteTopology : DiscreteTopology (Bundle (𝕜 := 𝕜)) := DiscreteTopology.mk (Eq.refl _)

instance parameterTopologicalSpace :
    TopologicalSpace (𝕜 × SixthRootParameter) := ⊥

instance parameterDiscreteTopology :
    DiscreteTopology (𝕜 × SixthRootParameter) := DiscreteTopology.mk (Eq.refl _)

/-- The monodromy bundle as a `TopCat` object. -/
def topCat : TopCat :=
  TopCat.of (Bundle (𝕜 := 𝕜))

/-- The parameter space `𝕜 × SixthRootParameter` as a `TopCat` object. -/
def parameterTopCat : TopCat :=
  TopCat.of (𝕜 × SixthRootParameter)

/-- Projection morphism from the bundle back to its input parameter pair. -/
noncomputable def projection :
    topCat (𝕜 := 𝕜) ⟶ parameterTopCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  exact ⟨fun p : Bundle (𝕜 := 𝕜) => (p.α, p.q),
    continuous_of_discreteTopology⟩

/-- Canonical section morphism from parameters into the monodromy bundle. -/
noncomputable def readout :
    parameterTopCat (𝕜 := 𝕜) ⟶ topCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  exact ⟨fun p : 𝕜 × SixthRootParameter =>
      ⟨p.1,
        (p.2,
          (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) p.1 p.2 |>.1,
            (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) p.1 p.2 |>.2.1,
              heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) p.1 p.2 |>.2.2)))⟩,
      continuous_of_discreteTopology⟩

/-- Categorical retraction law `readout ≫ projection = 𝟙 _` in `TopCat`. -/
@[simp] theorem projection_readout :
    readout (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext p
  · unfold readout projection Bundle.α
    exact Eq.refl _
  · unfold readout projection Bundle.q
    exact Eq.refl _

/-- Pointwise evaluation of `readout ≫ projection` at `p : 𝕜 × SixthRootParameter`. -/
@[simp] theorem projection_readout_apply (p : 𝕜 × SixthRootParameter) :
    (readout (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜)) p = p := by
  rw [projection_readout (𝕜 := 𝕜)]
  exact Eq.refl _

end InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyTopCat
