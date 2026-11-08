/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ZornScalingFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorCyclotomicChargeProjectors

/-!
# Sixth-Root Zorn Scaling and Cubic Charge Bridge

This module connects sixth-root-of-unity Zorn scaling ($p^6 = 1 \implies (p^2)^3 = 1$)
with the order-three cyclotomic charge `cubicCharge ((p : ℂ) ^ 2)` and the three
Peirce-sector projectors on `ZornMatrix ℂ`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.ThreeColorCyclotomicChargeProjectors`: `cubicCharge`,
    `cubicProjectorZero`, `cubicProjectorPlus`, `cubicProjectorMinus`,
    `cubicCharge_pow_three`, `cubicProjectors_sum_eq_id`, `cubicCharge_spectral_decomposition`.
- BUCKET 2 (Deconfabulation):
  * Replaced pass-through proofs (`zornSixthRoot_effectiveCubeRoot`,
    `cubicProjectors_sum_of_sixthRoot`) and `simpa` in `cubicCharge_of_sixthRoot`
    with explicit power-law and spectral decomposition derivations.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `zornSixthRoot_effectiveCubeRoot`: $(p : \mathbb{C})^6 = 1 \implies ((p : \mathbb{C})^2)^3 = 1$.
  * `cubicCharge_of_sixthRoot`: `(cubicCharge ((p : ℂ) ^ 2))^[3] = id`.
  * `cubicProjectors_sum_of_sixthRoot`: $P_0(Z) + P_+(Z) + P_-(Z) = Z$.
  * `sixthRoot_cubicCharge_peirce_decomposition`: Peirce resolution of
    `cubicCharge ((p : ℂ) ^ 2) Z` into the three Peirce projectors.
-/

namespace InfoGeometry.Canonical

open ZornMatrix

/-- The effective weight $(p : \mathbb{C})^2$ induced by a sixth root of unity $p^6 = 1$
satisfies $((p : \mathbb{C})^2)^3 = 1$. -/
theorem zornSixthRoot_effectiveCubeRoot
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    ((p : ℂ) ^ 2) ^ 3 = 1 := by
  calc
    ((p : ℂ) ^ 2) ^ 3 = (p : ℂ) ^ (2 * 3) := (pow_mul (p : ℂ) 2 3).symm
    _ = (p : ℂ) ^ 6 := by norm_num
    _ = 1 := hp

/-- The cubic charge operator at the effective Zorn weight $(p : \mathbb{C})^2$ has order three. -/
theorem cubicCharge_of_sixthRoot
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (cubicCharge ((p : ℂ) ^ 2)).comp
        ((cubicCharge ((p : ℂ) ^ 2)).comp (cubicCharge ((p : ℂ) ^ 2))) =
      LinearMap.id := by
  have hcube := zornSixthRoot_effectiveCubeRoot p hp
  exact cubicCharge_pow_three ((p : ℂ) ^ 2) hcube

/-- The three native cyclotomic Peirce projectors partition the identity on `ZornMatrix ℂ`. -/
theorem cubicProjectors_sum_of_sixthRoot
    (Z : ZornMatrix ℂ) :
    cubicProjectorZero Z + cubicProjectorPlus Z + cubicProjectorMinus Z = Z := by
  cases Z
  ext <;> simp [cubicProjectorZero, cubicProjectorPlus, cubicProjectorMinus, add_def]

/-- Peirce resolution of the sixth-root cubic charge operator on `ZornMatrix ℂ`. -/
theorem sixthRoot_cubicCharge_peirce_decomposition
    (p : ℂˣ) (Z : ZornMatrix ℂ) :
    cubicCharge ((p : ℂ) ^ 2) Z =
      cubicProjectorZero Z +
        ((p : ℂ) ^ 2) • cubicProjectorPlus Z +
        (((p : ℂ) ^ 2) ^ 2) • cubicProjectorMinus Z := by
  conv_lhs => rw [← cubicProjectors_sum_of_sixthRoot Z]
  rw [map_add, map_add, cubicCharge_zero_eigen, cubicCharge_plus_eigen, cubicCharge_minus_eigen]

end InfoGeometry.Canonical
