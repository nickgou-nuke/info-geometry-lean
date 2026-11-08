/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.FiniteCARFermiBridge
import InfoGeometry.Clifford.ThermodynamicZetaGeometry

/-!
# Finite CAR and Fermi-family compatibility

The finite one-mode CAR Gibbs normalization and the repository's unified
Fermi family use the same normalized two-state weight.  This file records the
comparison at the actual carriers and leaves the thermal and operator claims
separate.
-/

noncomputable section

namespace InfoGeometry.Algebra.FiniteSingleModeCAR

open InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
open InfoGeometry.Clifford.ThermodynamicZetaGeometry

/-- The occupied Gibbs weight of the finite one-mode CAR system is the FD
member of the native statistical family at the thermal coordinate
`-(β * ε)`. -/
theorem one_mode_gibbs_occupied_weight_eq_occupation_FD
    (β ε : ℝ) :
    Real.exp (-β * ε) /
        (∑ occ : OneModeState,
          Real.exp (-β * (if occ then ε else 0))) =
      occupation .FD (-(β * ε)) := by
  rw [one_mode_gibbs_trace]
  rw [occupation_FD]
  unfold fermiSimplexCoordinate
  rw [Real.exp_neg]
  have hexp : Real.exp (β * ε) ≠ 0 := Real.exp_ne_zero _
  have hden : Real.exp (β * ε) + 1 ≠ 0 := by positivity
  field_simp [hexp, hden]
  have hprod : Real.exp (-(β * ε)) * Real.exp (β * ε) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    Real.exp (-(β * ε)) * (1 + Real.exp (β * ε)) =
        Real.exp (-(β * ε)) + Real.exp (-(β * ε)) * Real.exp (β * ε) := by ring
    _ = 1 + Real.exp (-(β * ε)) := by rw [hprod]; ring

/-- The two finite CAR Gibbs weights occupy a normalized two-point simplex. -/
theorem one_mode_gibbs_occupied_plus_vacant_eq_one
    (β ε : ℝ) :
    Real.exp (-β * ε) /
        (∑ occ : OneModeState,
          Real.exp (-β * (if occ then ε else 0))) +
      1 /
        (∑ occ : OneModeState,
          Real.exp (-β * (if occ then ε else 0))) = 1 := by
  rw [one_mode_gibbs_trace]
  have hden : 1 + Real.exp (-β * ε) ≠ 0 := by positivity
  field_simp [hden]
  ring

/-! The normalized two-state Gibbs weights also expose their signed
polarization directly in the native Fermi family. -/

/-- The occupied-minus-vacant Gibbs polarization is the affine Fermi
    simplex contrast. -/
theorem one_mode_gibbs_polarization_eq_two_occupation_FD_sub_one
    (β ε : ℝ) :
    Real.exp (-β * ε) /
        (∑ occ : OneModeState,
          Real.exp (-β * (if occ then ε else 0))) -
      1 /
        (∑ occ : OneModeState,
          Real.exp (-β * (if occ then ε else 0))) =
      2 * occupation .FD (-(β * ε)) - 1 := by
  have h_occ := one_mode_gibbs_occupied_weight_eq_occupation_FD β ε
  have h_norm := one_mode_gibbs_occupied_plus_vacant_eq_one β ε
  linarith

end InfoGeometry.Algebra.FiniteSingleModeCAR
