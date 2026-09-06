import InfoGeometry.Algebraic.CartanSouriauMassieuDirectionalCalculus
import InfoGeometry.Algebraic.CartanSouriauMeanPairing

/-!
# Directional Massieu derivative as a mean-charge pairing

This owner is the finite algebraic bridge between the directional Massieu
calculus and the dual mean-moment coordinates.  It deliberately makes no
claim about a full Fréchet gradient or about an infinite-dimensional orbit.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CartanSouriauMassieu

open scoped BigOperators
open InfoGeometry.Algebraic.CartanSouriauMassieuDirectionalCalculus

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem massieu_directional_deriv_eq_neg_mean_pairing
    (F : Family ι) (β v : Fin 2 → ℝ) :
    deriv (directionalMassieu F β v) 0 =
      -(∑ a : Fin 2, v a * chargeMean F β a) := by
  rw [massieu_directional_deriv]
  rw [expected_directionalCharge_eq_mean_pairing]

end InfoGeometry.Algebraic.CartanSouriauMassieu
