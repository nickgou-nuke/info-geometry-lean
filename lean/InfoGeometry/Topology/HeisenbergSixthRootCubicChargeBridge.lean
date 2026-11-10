/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

/-!
# Heisenberg Sixth-Root / Cubic-Charge Bridge

This module combines the Heisenberg boundary atlas readout, the effective cube root
`effectiveCubeRoot q`, and the induced order-three Zorn operator `sixthRootCubicCharge q`
into `heisenbergSixthRootCubicChargeReadout`, and proves its coordinate projections,
root independence of the Heisenberg boundary component, cubic root and operator order-three
identities, continuity, and local constancy.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological`:
    `SixthRootParameter`, `heisenbergBoundaryAtlasReadout`.
  * `InfoGeometry.Topology.ZornSixthRootCubicChargeTopological`:
    `effectiveCubeRoot`, `effectiveCubeRoot_cube`, `sixthRootCubicCharge`,
    `sixthRootCubicChargeHomeomorph_cube`.
- BUCKET 2 (Deconfabulation):
  * All coordinate projections and order-three identities are proved via explicit
    definitional unfolding and reduction to the Zorn cyclotomic charge theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergSixthRootCubicChargeReadout`.
  * `heisenbergSixthRootCubicChargeReadout_fst`,
    `heisenbergSixthRootCubicChargeReadout_snd_fst`,
    `heisenbergSixthRootCubicChargeReadout_snd_snd`.
  * `heisenbergBoundaryAtlasReadout_root_independent`.
  * `heisenbergSixthRootCubicChargeReadout_root_cube`,
    `heisenbergSixthRootCubicChargeReadout_charge_cube`.
  * `continuous_heisenbergSixthRootCubicChargeReadout`,
    `isLocallyConstant_heisenbergSixthRootCubicChargeReadout`.
-/

namespace InfoGeometry.Topology.HeisenbergSixthRootCubicChargeBridge

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]

/-- Complex Zorn octonionic matrix carrier. -/
abbrev Zorn := InfoGeometry.Canonical.ZornMatrix ℂ

instance zornCubicChargeTopologicalSpace :
    TopologicalSpace (Zorn →ₗ[ℂ] Zorn) := ⊥

instance zornCubicChargeDiscreteTopology :
    DiscreteTopology (Zorn →ₗ[ℂ] Zorn) := DiscreteTopology.mk (Eq.refl _)

/-- The combined Heisenberg boundary / sixth-root / cubic-charge readout. -/
noncomputable def heisenbergSixthRootCubicChargeReadout
    (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
      (ℂ × (Zorn →ₗ[ℂ] Zorn)) :=
  (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q,
    (effectiveCubeRoot q, sixthRootCubicCharge q))

/-- First projection of `heisenbergSixthRootCubicChargeReadout α q` is the Heisenberg boundary atlas. -/
@[simp] theorem heisenbergSixthRootCubicChargeReadout_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).1 =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q := by
  unfold heisenbergSixthRootCubicChargeReadout
  exact Eq.refl _

/-- Effective cube-root component of `heisenbergSixthRootCubicChargeReadout α q`. -/
@[simp] theorem heisenbergSixthRootCubicChargeReadout_snd_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.1 =
      effectiveCubeRoot q := by
  unfold heisenbergSixthRootCubicChargeReadout
  exact Eq.refl _

/-- Cubic Zorn charge operator component of `heisenbergSixthRootCubicChargeReadout α q`. -/
@[simp] theorem heisenbergSixthRootCubicChargeReadout_snd_snd
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.2 =
      sixthRootCubicCharge q := by
  unfold heisenbergSixthRootCubicChargeReadout
  exact Eq.refl _

/-- The Heisenberg boundary component is independent of the sixth-root parameter `q`. -/
theorem heisenbergBoundaryAtlasReadout_root_independent
    (α : 𝕜) (q q' : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q' := by
  unfold heisenbergBoundaryAtlasReadout
  rw [InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas_heisenberg,
    InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas_heisenberg]

/-- The effective cube root in `heisenbergSixthRootCubicChargeReadout α q` satisfies `ω^3 = 1`. -/
theorem heisenbergSixthRootCubicChargeReadout_root_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.1 ^ 3 = 1 := by
  rw [heisenbergSixthRootCubicChargeReadout_snd_fst]
  exact effectiveCubeRoot_cube q

/-- The cubic Zorn operator in `heisenbergSixthRootCubicChargeReadout α q` has order three. -/
theorem heisenbergSixthRootCubicChargeReadout_charge_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.2.comp
        ((heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.2.comp
          (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α q).2.2) =
      LinearMap.id := by
  rw [heisenbergSixthRootCubicChargeReadout_snd_snd]
  exact sixthRootCubicChargeHomeomorph_cube q

/-- The combined readout is continuous on the discrete sixth-root parameter space. -/
theorem continuous_heisenbergSixthRootCubicChargeReadout (α : 𝕜) :
    Continuous (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α) := by
  unfold heisenbergSixthRootCubicChargeReadout
  exact continuous_of_discreteTopology

/-- The combined readout is locally constant on the discrete sixth-root parameter space. -/
theorem isLocallyConstant_heisenbergSixthRootCubicChargeReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergSixthRootCubicChargeReadout (𝕜 := 𝕜) α) := by
  unfold heisenbergSixthRootCubicChargeReadout
  exact IsLocallyConstant.of_discrete

end
end InfoGeometry.Topology.HeisenbergSixthRootCubicChargeBridge
