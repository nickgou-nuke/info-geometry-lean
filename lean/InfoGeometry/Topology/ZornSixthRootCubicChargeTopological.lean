/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornSixthRootCubicChargeBridge
import InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
import InfoGeometry.Topology.ThreeColorCyclotomicChargeTopological

/-!
# Topological Sixth-Root to Cubic-Charge Bridge

This module defines the effective cube root `effectiveCubeRoot q = (q.1 : ℂ) ^ 2`
for `q : SixthRootParameter`, the induced order-three Zorn operator
`sixthRootCubicCharge q`, and its topological homeomorphism
`sixthRootCubicChargeHomeomorph q`, and proves `effectiveCubeRoot_cube`,
continuity, local constancy, and `sixthRootCubicChargeHomeomorph_cube`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.ZornSixthRootCubicChargeBridge`:
    `zornSixthRoot_effectiveCubeRoot`.
  * `InfoGeometry.Topology.ThreeColorCyclotomicChargeTopological`:
    `cubicChargeHomeomorph`.
- BUCKET 2 (Deconfabulation):
  * All algebraic order-three and topological properties are proved constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `Zorn`, `effectiveCubeRoot`, `sixthRootCubicCharge`,
    `sixthRootCubicChargeHomeomorph`.
  * `effectiveCubeRoot_cube`, `continuous_effectiveCubeRoot`,
    `isLocallyConstant_effectiveCubeRoot`,
    `sixthRootCubicChargeHomeomorph_apply`,
    `sixthRootCubicChargeHomeomorph_cube`.
-/

namespace InfoGeometry.Topology.ZornSixthRootCubicChargeTopological

open InfoGeometry.Canonical
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.ThreeColorCyclotomicChargeTopological

noncomputable section

/-- Complex Zorn octonionic matrix carrier. -/
abbrev Zorn := ZornMatrix ℂ

/-- Effective cube root `(q.1 : ℂ) ^ 2` associated with a sixth-root parameter `q`. -/
def effectiveCubeRoot (q : SixthRootParameter) : ℂ :=
  (q.1 : ℂ) ^ 2

/-- The effective cube root satisfies `effectiveCubeRoot q ^ 3 = 1`. -/
theorem effectiveCubeRoot_cube (q : SixthRootParameter) :
    effectiveCubeRoot q ^ 3 = 1 := by
  unfold effectiveCubeRoot
  exact zornSixthRoot_effectiveCubeRoot q.1 q.2

/-- The effective root readout is continuous on the discrete parameter set. -/
theorem continuous_effectiveCubeRoot :
    Continuous effectiveCubeRoot := by
  unfold effectiveCubeRoot
  exact continuous_of_discreteTopology

/-- The effective root readout is locally constant on the discrete parameter set. -/
theorem isLocallyConstant_effectiveCubeRoot :
    IsLocallyConstant effectiveCubeRoot := by
  intro s
  exact isOpen_discrete _

/-- Order-three cyclotomic Zorn action associated with a sixth-root parameter `q`. -/
def sixthRootCubicCharge (q : SixthRootParameter) : Zorn →ₗ[ℂ] Zorn :=
  cubicCharge (effectiveCubeRoot q)

/-- The order-three Zorn action equipped with its topological inverse. -/
noncomputable def sixthRootCubicChargeHomeomorph
    (q : SixthRootParameter) : Zorn ≃ₜ Zorn :=
  cubicChargeHomeomorph (effectiveCubeRoot q) (effectiveCubeRoot_cube q)

/-- Pointwise evaluation of `sixthRootCubicChargeHomeomorph q` agrees with `sixthRootCubicCharge q`. -/
@[simp] theorem sixthRootCubicChargeHomeomorph_apply
    (q : SixthRootParameter) (Z : Zorn) :
    sixthRootCubicChargeHomeomorph q Z =
      sixthRootCubicCharge q Z := by
  unfold sixthRootCubicChargeHomeomorph sixthRootCubicCharge
  exact Eq.refl _

/-- The threefold linear composition of `sixthRootCubicCharge q` equals `LinearMap.id`. -/
theorem sixthRootCubicChargeHomeomorph_cube
    (q : SixthRootParameter) :
    (sixthRootCubicCharge q).comp
          ((sixthRootCubicCharge q).comp (sixthRootCubicCharge q)) =
      LinearMap.id := by
  unfold sixthRootCubicCharge
  exact cubicCharge_pow_three (effectiveCubeRoot q) (effectiveCubeRoot_cube q)

end
end InfoGeometry.Topology.ZornSixthRootCubicChargeTopological
