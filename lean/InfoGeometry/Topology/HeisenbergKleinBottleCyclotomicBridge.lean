/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.KleinBottleCyclotomicChiralLift

/-!
# Heisenberg / Klein-Bottle Cyclotomic Bridge

This module pairs the Heisenberg boundary atlas readout with the Klein-bottle
chiral cubic charge `cubicCharge ((q.1 : ℂ) ^ 2)` and chiral exchange
`chiralExchange` in `heisenbergKleinCyclotomicReadout`, and proves coordinate
projections, root independence, cubic order-three, exchange involution, chiral
conjugation, continuity, and local constancy.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological`:
    `SixthRootParameter`, `heisenbergBoundaryAtlasReadout`.
  * `InfoGeometry.Topology.KleinBottleCyclotomicChiralLift`:
    `cubicCharge`, `chiralExchange`, `cubicCharge_cube`, `chiralExchange_square`,
    `chiralExchange_conj_cubicCharge`.
- BUCKET 2 (Deconfabulation):
  * All operator order-three, involution, and conjugation identities are proved
    constructively from the sixth-root exponent identity `((q.1 : ℂ)^2)^3 = 1`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergKleinCyclotomicReadout`.
  * `heisenbergKleinCyclotomicReadout_fst`,
    `heisenbergKleinCyclotomicReadout_snd_fst`,
    `heisenbergKleinCyclotomicReadout_snd_snd`.
  * `heisenbergBoundaryAtlasReadout_root_independent`.
  * `heisenbergKleinCyclotomicReadout_charge_cube`,
    `heisenbergKleinCyclotomicReadout_exchange_square`,
    `heisenbergKleinCyclotomicReadout_exchange_conj`.
  * `continuous_heisenbergKleinCyclotomicReadout`,
    `isLocallyConstant_heisenbergKleinCyclotomicReadout`.
-/

namespace InfoGeometry.Topology.HeisenbergKleinBottleCyclotomicBridge

open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.KleinBottleCyclotomicChiralLift
open InfoGeometry.Canonical

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance a2ColourEndomorphismTopologicalSpace :
    TopologicalSpace
      (InfoGeometry.Canonical.A2ColourFiber ℂ →ₗ[ℂ]
        InfoGeometry.Canonical.A2ColourFiber ℂ) := ⊥

instance a2ColourEndomorphismDiscreteTopology :
    DiscreteTopology
      (InfoGeometry.Canonical.A2ColourFiber ℂ →ₗ[ℂ]
        InfoGeometry.Canonical.A2ColourFiber ℂ) := DiscreteTopology.mk (Eq.refl _)

/-- The combined Heisenberg boundary / Klein-bottle cyclotomic readout. -/
noncomputable def heisenbergKleinCyclotomicReadout (α : 𝕜) (q : SixthRootParameter) :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α ×
      (InfoGeometry.Canonical.A2ColourFiber ℂ →ₗ[ℂ]
        InfoGeometry.Canonical.A2ColourFiber ℂ) ×
      (InfoGeometry.Canonical.A2ColourFiber ℂ →ₗ[ℂ]
        InfoGeometry.Canonical.A2ColourFiber ℂ) :=
  (heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q,
    (InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge
      ((q.1 : ℂ) ^ 2),
      InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
        (K := ℂ)))

/-- First projection of `heisenbergKleinCyclotomicReadout α q` is the Heisenberg boundary atlas. -/
@[simp] theorem heisenbergKleinCyclotomicReadout_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).1 =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q := by
  unfold heisenbergKleinCyclotomicReadout
  exact Eq.refl _

/-- Cubic charge component of `heisenbergKleinCyclotomicReadout α q`. -/
@[simp] theorem heisenbergKleinCyclotomicReadout_snd_fst
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1 =
      InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge
        ((q.1 : ℂ) ^ 2) := by
  unfold heisenbergKleinCyclotomicReadout
  exact Eq.refl _

/-- Chiral exchange component of `heisenbergKleinCyclotomicReadout α q`. -/
@[simp] theorem heisenbergKleinCyclotomicReadout_snd_snd
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2 =
      InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange
        (K := ℂ) := by
  unfold heisenbergKleinCyclotomicReadout
  exact Eq.refl _

/-- The Heisenberg boundary component is independent of the sixth-root parameter `q`. -/
theorem heisenbergBoundaryAtlasReadout_root_independent
    (α : 𝕜) (q q' : SixthRootParameter) :
    heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q =
      heisenbergBoundaryAtlasReadout (𝕜 := 𝕜) α q' := by
  unfold heisenbergBoundaryAtlasReadout
  rw [InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas_heisenberg,
    InfoGeometry.Canonical.HeisenbergCyclotomicAtlas.canonicalAtlas_heisenberg]

/-- The Klein-bottle cubic charge induced by a sixth-root parameter has order three. -/
theorem heisenbergKleinCyclotomicReadout_charge_cube
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1.comp
        ((heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1.comp
          (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1) =
      LinearMap.id := by
  have hq : ((q.1 : ℂ) ^ 2) ^ 3 = 1 := by
    calc
      ((q.1 : ℂ) ^ 2) ^ 3 = (q.1 : ℂ) ^ 6 := by ring
      _ = 1 := q.2
  rw [heisenbergKleinCyclotomicReadout_snd_fst]
  exact InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.cubicCharge_cube
    (K := ℂ) ((q.1 : ℂ) ^ 2) hq

/-- The Klein-bottle chiral exchange is involutive on the combined readout. -/
theorem heisenbergKleinCyclotomicReadout_exchange_square
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2.comp
        (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2 =
      LinearMap.id := by
  rw [heisenbergKleinCyclotomicReadout_snd_snd]
  exact InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange_square
    (K := ℂ)

/-- Chiral exchange conjugates the cubic charge to its square. -/
theorem heisenbergKleinCyclotomicReadout_exchange_conj
    (α : 𝕜) (q : SixthRootParameter) :
    (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2.comp
        ((heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1.comp
          (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.2) =
      (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1.comp
        (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α q).2.1 := by
  have hq : ((q.1 : ℂ) ^ 2) ^ 3 = 1 := by
    calc
      ((q.1 : ℂ) ^ 2) ^ 3 = (q.1 : ℂ) ^ 6 := by ring
      _ = 1 := q.2
  rw [heisenbergKleinCyclotomicReadout_snd_fst, heisenbergKleinCyclotomicReadout_snd_snd]
  exact InfoGeometry.Topology.KleinBottleCyclotomicChiralLift.chiralExchange_conj_cubicCharge
    (K := ℂ) ((q.1 : ℂ) ^ 2) hq

/-- The combined readout is continuous on the discrete sixth-root parameter space. -/
theorem continuous_heisenbergKleinCyclotomicReadout (α : 𝕜) :
    Continuous (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α) := by
  unfold heisenbergKleinCyclotomicReadout
  exact continuous_of_discreteTopology

/-- The combined readout is locally constant on the discrete sixth-root parameter space. -/
theorem isLocallyConstant_heisenbergKleinCyclotomicReadout (α : 𝕜) :
    IsLocallyConstant (heisenbergKleinCyclotomicReadout (𝕜 := 𝕜) α) := by
  unfold heisenbergKleinCyclotomicReadout
  exact IsLocallyConstant.of_discrete

end InfoGeometry.Topology.HeisenbergKleinBottleCyclotomicBridge
