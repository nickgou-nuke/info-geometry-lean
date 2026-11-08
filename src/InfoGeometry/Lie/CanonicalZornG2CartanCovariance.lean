import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Lie

open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

variable {State : Type*} [Fintype State] [Nonempty State]
  (D : CartanSouriauDatum State)

def fisherSouriauCovariance (beta : Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  ∑ x : State, realGibbsWeight D beta x *
    (D.momentMap x i - souriauChargeMean D beta i) *
    (D.momentMap x j - souriauChargeMean D beta j)

theorem fisherSouriauCovariance_comm (beta : Fin 2 → ℝ) (i j : Fin 2) :
    fisherSouriauCovariance D beta i j = fisherSouriauCovariance D beta j i := by
  unfold fisherSouriauCovariance
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem fisherSouriauCovariance_diagonal_nonneg
    (beta : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ fisherSouriauCovariance D beta i i := by
  unfold fisherSouriauCovariance
  have hw : ∀ x : State, 0 ≤ realGibbsWeight D beta x := by
    intro x
    exact div_nonneg (le_of_lt (Real.exp_pos _))
      (le_of_lt (realGibbsPartition_pos D beta))
  apply Finset.sum_nonneg
  intro x _
  rw [mul_assoc]
  rw [show (D.momentMap x i - souriauChargeMean D beta i) *
      (D.momentMap x i - souriauChargeMean D beta i) =
      (D.momentMap x i - souriauChargeMean D beta i) ^ (2 : ℕ) by ring]
  exact mul_nonneg (hw x) (sq_nonneg _)

end InfoGeometry.Lie
