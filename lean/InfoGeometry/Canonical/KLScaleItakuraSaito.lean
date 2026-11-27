/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.GaugeReduction

/-!
# The reversed Itakura--Saito mass ratio in the existing KL split

The existing generalized-KL mass/shape theorem has a scalar radial term.
Here its actual expression is proved to be `x * (y/x - 1 - log(y/x))`.
The expression in parentheses is the scalar Itakura--Saito generator,
already named `scalarItakuraSaito` in the heavier trace-formula owner. We state
the expression directly, without creating a second generator definition or
importing an unrelated operator-colimit graph. The ratio is reversed: `y/x`.
The normalized KL shape term is not asserted to be an IS divergence.
-/

namespace InfoGeometry.PositiveMeasure

/-- The radial KL term is the first mass times the scalar IS generator
evaluated at the reversed mass ratio. -/
theorem gklTerm_reverse_ratio (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    gklTerm x y = x * (y / x - 1 - Real.log (y / x)) := by
  rw [gklTerm_eq x y (ne_of_gt hx) (ne_of_gt hy)]
  field_simp [ne_of_gt hx]

/-- The existing exact generalized-KL decomposition, with its radial term
expressed as a reversed mass-ratio Itakura--Saito generator. -/
theorem generalizedKL_mass_ratio_decomposition
    {ι : Type*} [Fintype ι] [Nonempty ι] (μ ν : PositiveMeasure ι ℝ) :
    generalizedKL μ ν = Z μ *
      (generalizedKL (normalize μ) (normalize ν) +
        (Z ν / Z μ - 1 - Real.log (Z ν / Z μ))) := by
  rw [generalizedKL_projective_radial_decomposition,
    gklTerm_reverse_ratio (Z μ) (Z ν) (Z_pos μ) (Z_pos ν)]
  ring

end InfoGeometry.PositiveMeasure
