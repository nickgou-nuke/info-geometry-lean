/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological
import InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

/-!
# Heisenberg Sixth-Root / Cubic Monodromy Bridge

This module pairs the Heisenberg boundary atlas readout with the effective cubic-root
parameter `effectiveCubicRootParameter q` and the Klein-bottle cubic colour monodromy
operator `cubicRootChargeReadout`, and proves coordinate projections, root independence,
cubic order-three laws, chiral exchange conjugation, continuity, and local constancy.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological`:
    `SixthRootParameter`, `heisenbergBoundaryAtlasReadout`.
  * `InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological`:
    `CubicRootParameter`, `ColourOperator`, `cubicRootChargeReadout`,
    `cubicRootChargeReadout_cube`, `chiralExchange_conj_cubicRootChargeReadout`.
  * `InfoGeometry.Topology.ZornSixthRootCubicChargeTopological`:
    `effectiveCubeRoot`, `effectiveCubeRoot_cube`.
- BUCKET 2 (Deconfabulation):
  * All coordinate projections, order-three laws, and chiral conjugation identities
    are proved via explicit unfolding and rewriting.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `effectiveCubicRootParameter`, `heisenbergSixthRootCubicMonodromyReadout`.
  * `heisenbergSixthRootCubicMonodromyReadout_fst`,
    `heisenbergSixthRootCubicMonodromyReadout_snd_fst`,
    `heisenbergSixthRootCubicMonodromyReadout_snd_snd`.
  * `heisenbergBoundaryAtlasReadout_root_independent`.
  * `heisenbergSixthRootCubicMonodromyReadout_root_cube`,
    `heisenbergSixthRootCubicMonodromyReadout_charge_cube`,
    `heisenbergSixthRootCubicMonodromyReadout_exchange_conj`.
  * `continuous_heisenbergSixthRootCubicMonodromyReadout`,
    `isLocallyConstant_heisenbergSixthRootCubicMonodromyReadout`.
-/

namespace InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyBridge

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological
open InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The cubic-root parameter induced by squaring a sixth-root parameter. -/
def effectiveCubicRootParameter (q : SixthRootParameter) : CubicRootParameter :=
  ⟨effectiveCubeRoot q, effectiveCubeRoot_cube q⟩

/-- The combined Heisenberg boundary / cubic-root monodromy readout. -/
noncomputable def heisenbergSixthRootCubicMonodromyReadout
    (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
      (CubicRootParameter × ColourOperator) :=
  (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q,
    (effectiveCubicRootParameter q,
      cubicRootChargeReadout (effectiveCubicRootParameter q)))

/-- First projection of `heisenbergSixthRootCubicMonodromyReadout α q` is the Heisenberg boundary atlas. -/
@[simp] theorem heisenbergSixthRootCubicMonodromyReadout_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).1 =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q := by
  unfold heisenbergSixthRootCubicMonodromyReadout
  exact Eq.refl _

/-- Cubic-root parameter component of `heisenbergSixthRootCubicMonodromyReadout α q`. -/
@[simp] theorem heisenbergSixthRootCubicMonodromyReadout_snd_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.1 =
      effectiveCubicRootParameter q := by
  unfold heisenbergSixthRootCubicMonodromyReadout
  exact Eq.refl _

/-- Klein-bottle colour monodromy component of `heisenbergSixthRootCubicMonodromyReadout α q`. -/
@[simp] theorem heisenbergSixthRootCubicMonodromyReadout_snd_snd
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2 =
      cubicRootChargeReadout (effectiveCubicRootParameter q) := by
  unfold heisenbergSixthRootCubicMonodromyReadout
  exact Eq.refl _

/-- The Heisenberg boundary component is independent of the sixth-root parameter `q`. -/
theorem heisenbergBoundaryAtlasReadout_root_independent
    (α : 𝕜) (q q' : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q' := by
  unfold heisenbergBoundaryAtlasReadout
  rw [InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas_heisenberg,
    InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas_heisenberg]

/-- The effective cubic-root parameter satisfies `ω^3 = 1`. -/
theorem heisenbergSixthRootCubicMonodromyReadout_root_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.1.1 ^ 3 = 1 := by
  rw [heisenbergSixthRootCubicMonodromyReadout_snd_fst]
  exact effectiveCubeRoot_cube q

/-- The cubic monodromy operator has order three on the colour fiber. -/
theorem heisenbergSixthRootCubicMonodromyReadout_charge_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2.comp
        ((heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2.comp
          (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2) =
      LinearMap.id := by
  rw [heisenbergSixthRootCubicMonodromyReadout_snd_snd]
  exact cubicRootChargeReadout_cube (effectiveCubicRootParameter q)

/-- Chiral exchange conjugates the cubic colour monodromy operator to its square. -/
theorem heisenbergSixthRootCubicMonodromyReadout_exchange_conj
    (α : 𝕜) (q : SixthRootParameter) :
    (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
      (K := ℂ)).comp
        ((heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2.comp
          (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
            (K := ℂ))) =
      (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2.comp
        (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α q).2.2 := by
  rw [heisenbergSixthRootCubicMonodromyReadout_snd_snd]
  exact chiralExchange_conj_cubicRootChargeReadout (q := effectiveCubicRootParameter q)

/-- The combined readout is continuous on the discrete sixth-root parameter space. -/
theorem continuous_heisenbergSixthRootCubicMonodromyReadout (α : 𝕜) :
    Continuous (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α) := by
  unfold heisenbergSixthRootCubicMonodromyReadout
  exact continuous_of_discreteTopology

/-- The combined readout is locally constant on the discrete sixth-root parameter space. -/
theorem isLocallyConstant_heisenbergSixthRootCubicMonodromyReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergSixthRootCubicMonodromyReadout (𝕜 := 𝕜) α) := by
  unfold heisenbergSixthRootCubicMonodromyReadout
  exact IsLocallyConstant.of_discrete

end

end InfoGeometry.Topology.HeisenbergSixthRootCubicMonodromyBridge
