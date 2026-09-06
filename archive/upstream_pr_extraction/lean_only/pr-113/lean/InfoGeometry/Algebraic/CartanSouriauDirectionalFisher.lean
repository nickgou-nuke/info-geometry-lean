import InfoGeometry.Algebraic.CartanSouriauMassieu

/-!
# Positivity of the finite directional Souriau--Fisher readout

The covariance quadratic form is exposed as a sum of weighted squares.  This
is the finite algebraic positivity statement; it does not assert that it is
the Hessian of a globally defined Massieu function.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CartanSouriauMassieu

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem directional_chargeCovariance_nonneg
    (F : Family ι) (β v : Fin 2 → ℝ) :
    0 ≤ ∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovariance F β a b * v b := by
  rw [chargeCovariance_quadratic_eq_expect_sq]
  refine Finset.sum_nonneg ?_
  intro m _hm
  exact mul_nonneg (le_of_lt (probability_pos F β m)) (sq_nonneg _)

end InfoGeometry.Algebraic.CartanSouriauMassieu
