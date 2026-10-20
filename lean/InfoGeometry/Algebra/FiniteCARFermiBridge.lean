/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/


import InfoGeometry.Algebra.FiniteSingleModeCAR
import InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry


/-!
# Finite CAR to Fermi occupation

The finite one-mode Gibbs sum is connected to the repository's native Fermi
occupation definition by an explicit normalization theorem.
-/

namespace InfoGeometry.Algebra.FiniteSingleModeCAR

open InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry

/-- The normalized occupied Gibbs weight of the finite one-mode CAR system is
exactly the native Fermi occupation readout. -/
theorem one_mode_gibbs_occupied_weight_eq_fermiOccupation
    (β ε : ℝ) :
    Real.exp (-β * ε) /
        (∑ occ : OneModeState,
          Real.exp (-β * (if occ then ε else 0))) =
      fermiOccupation β ε := by
  rw [one_mode_gibbs_trace]
  unfold fermiOccupation
  have h : Real.exp (β * ε) + 1 ≠ 0 :=
    ne_of_gt (exp_add_one_pos β ε)
  have hexp : Real.exp (β * ε) ≠ 0 := Real.exp_ne_zero _
  have hneg : -β * ε = -(β * ε) := by ring
  rw [hneg, Real.exp_neg]
  field_simp [h, hexp]

end InfoGeometry.Algebra.FiniteSingleModeCAR
