/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite shifts of scalar Boltzmann weights

The theorem here is a scalar exponential identity for an arbitrary action
value. It does not assert a conformal Ward identity or connect an operator
variation to the chiral anomaly.
-/

namespace InfoGeometry.Canonical.ConformalWard

/-- Scalar Boltzmann weight of a real action value at temperature `T`. -/
noncomputable def actionBoltzmannWeight (action T : ℝ) : ℝ :=
  Real.exp (-action / T)

/-- An additive shift in the action multiplies its Boltzmann weight by the
exponential of the negative shift. -/
theorem actionBoltzmannWeight_add_shift (action shift T : ℝ) :
    actionBoltzmannWeight (action + shift) T =
      actionBoltzmannWeight action T * Real.exp (-shift / T) := by
  unfold actionBoltzmannWeight
  rw [show -(action + shift) / T = -action / T + -shift / T by ring,
    Real.exp_add]

/-- Every scalar Boltzmann weight is strictly positive. -/
theorem actionBoltzmannWeight_pos (action T : ℝ) :
    0 < actionBoltzmannWeight action T := by
  exact Real.exp_pos _

end InfoGeometry.Canonical.ConformalWard
