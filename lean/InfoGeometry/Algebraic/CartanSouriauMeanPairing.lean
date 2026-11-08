import InfoGeometry.Algebraic.CartanSouriauMassieu
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Mean-charge dual pairing

The finite Souriau family has a charge mean with two components.  This owner
records the exact finite pairing identity needed to read it as a dual vector.
It does not assert a full differentiable gradient theorem.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CartanSouriauMassieu

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem expected_directionalCharge_eq_mean_pairing
    (F : Family ι) (β v : Fin 2 → ℝ) :
    (∑ m : ι, probability F β m * directionalCharge F v m) =
      ∑ a : Fin 2, v a * chargeMean F β a := by
  unfold directionalCharge chargeMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro m _hm
  ring

end InfoGeometry.Algebraic.CartanSouriauMassieu
