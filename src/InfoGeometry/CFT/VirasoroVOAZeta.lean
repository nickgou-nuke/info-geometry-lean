/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.External.Virasoro.VirasoroAlgebra
import Mathlib.Tactic

/-!
# Virasoro mode anomalies and the free-boson weight polynomial

This owner records two independent, precisely scoped facts.  First, the
Virasoro central extension has its standard resonant bracket, and the first
resonant mode beyond the `sl₂` wedge has a nonzero central defect.  Second,
the quadratic free-boson weight `α²/2` is positive away from zero and vanishes
at the vacuum parameter.  No relation between this weight and the Riemann zeta
function is asserted here.
-/

namespace InfoGeometry.CFT.VirasoroVOAZeta

/-- The quadratic conformal weight used by the rank-one free-boson model. -/
noncomputable def primaryConformalWeight (alpha : ℝ) : ℝ := alpha ^ 2 / 2

/-- Every nonzero parameter has positive quadratic conformal weight. -/
theorem primary_weight_pos_of_ne_zero (alpha : ℝ) (hα : alpha ≠ 0) :
    0 < primaryConformalWeight alpha := by
  unfold primaryConformalWeight
  have hsq : 0 < alpha ^ 2 := sq_pos_of_ne_zero hα
  positivity

/-- The quadratic conformal weight vanishes exactly at the vacuum parameter. -/
theorem primary_weight_eq_zero_iff (alpha : ℝ) :
    primaryConformalWeight alpha = 0 ↔ alpha = 0 := by
  constructor
  · intro hweight
    by_contra hα
    have hpositive := primary_weight_pos_of_ne_zero alpha hα
    linarith
  · rintro rfl
    simp [primaryConformalWeight]

/-- The resonant Virasoro bracket records both its Witt term and central term. -/
theorem resonant_mode_bracket (n : ℤ) :
    ⁅VirasoroProject.VirasoroAlgebra.lgen ℝ n,
      VirasoroProject.VirasoroAlgebra.lgen ℝ (-n)⁆ =
        (2 * (n : ℝ)) • VirasoroProject.VirasoroAlgebra.lgen ℝ 0 +
          (((n ^ 3 - n : ℝ) / 12) • VirasoroProject.VirasoroAlgebra.cgen ℝ) := by
  rw [VirasoroProject.VirasoroAlgebra.lgen_bracket]
  rw [show n + -n = 0 by omega]
  congr 1
  push_cast
  ring_nf

end InfoGeometry.CFT.VirasoroVOAZeta
