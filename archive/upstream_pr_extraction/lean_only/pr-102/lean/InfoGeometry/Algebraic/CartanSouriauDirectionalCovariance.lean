import InfoGeometry.Algebraic.CartanSouriauMassieu
import InfoGeometry.Algebraic.CartanSouriauDirectionalFisher

/-!
# Bilinear directional covariance

The component covariance readout induces a symmetric bilinear form on the
finite temperature directions.  This is an algebraic readout theorem, not a
claim that a global analytic Hessian has already been constructed.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CartanSouriauMassieu

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def directionalCovariance
    (F : Family ι) (β v w : Fin 2 → ℝ) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    v a * chargeCovariance F β a b * w b

theorem directionalCovariance_swap
    (F : Family ι) (β v w : Fin 2 → ℝ) :
    directionalCovariance F β v w =
      directionalCovariance F β w v := by
  unfold directionalCovariance
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  apply Finset.sum_congr rfl
  intro a _ha
  rw [chargeCovariance_symm F β a b]
  ring

theorem directionalCovariance_self_nonneg
    (F : Family ι) (β v : Fin 2 → ℝ) :
    0 ≤ directionalCovariance F β v v := by
  unfold directionalCovariance
  exact directional_chargeCovariance_nonneg F β v

end InfoGeometry.Algebraic.CartanSouriauMassieu
