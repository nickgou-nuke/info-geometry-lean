import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Analytic.LogSumExp
import InfoGeometry.Analytic.LogSumExpVariancePositivity
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

namespace InfoGeometry.Lie

open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Analytic
open scoped BigOperators

variable {State : Type*} [Fintype State] [Nonempty State]
  (D : CartanSouriauDatum State)

def souriauMassieu (beta : Fin 2 → ℝ) : ℝ :=
  Real.log (realGibbsPartition D beta)

def souriauChargeMean (beta : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ∑ x : State, realGibbsWeight D beta x * D.momentMap x i

def souriauChargeVariance (beta : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ∑ x : State, realGibbsWeight D beta x *
    (D.momentMap x i - souriauChargeMean D beta i) ^ (2 : ℕ)

def betaSlice (beta : Fin 2 → ℝ) (i : Fin 2) (t : ℝ) : Fin 2 → ℝ :=
  fun j => if j = i then t else beta j

theorem souriauMassieu_slice_eq_logSumExp (beta : Fin 2 → ℝ) (i : Fin 2) (t : ℝ) :
    souriauMassieu D (betaSlice beta i t) =
      logSumExp (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) t := by
  unfold souriauMassieu betaSlice logSumExp logSumExpPartition
    realGibbsPartition realGibbsKernel realPairingEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [← Real.exp_add]
  congr 1
  simp only [Fin.sum_univ_two]
  fin_cases i <;> simp <;> ring

theorem souriauChargeMean_eq_logSumExpMean (beta : Fin 2 → ℝ) (i : Fin 2) :
    souriauChargeMean D beta i =
      -(logSumExpMean (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) (beta i)) := by
  let w : State → ℝ := fun x => Real.exp
    (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j))
  let a : State → ℝ := fun x => -D.momentMap x i
  have hw : ∀ x, 0 < w x := fun x => Real.exp_pos _
  rw [logSumExpMean_eq_weighted_sum w a hw (beta i)]
  have hpart : logSumExpPartition w a (beta i) = realGibbsPartition D beta := by
    unfold logSumExpPartition realGibbsPartition w a realGibbsKernel
      realPairingEnergy
    apply Finset.sum_congr rfl
    intro x _
    rw [← Real.exp_add]
    congr 1
    simp only [Fin.sum_univ_two]
    fin_cases i <;> simp [a, realPairingEnergy] <;> ring
  have hweight : ∀ x, logSumExpWeight w a (beta i) x =
      realGibbsWeight D beta x := by
    intro x
    unfold logSumExpWeight realGibbsWeight realGibbsKernel realPairingEnergy
    rw [hpart]
    rw [← Real.exp_add]
    congr 1
    simp only [Fin.sum_univ_two]
    fin_cases i <;> simp [a, realPairingEnergy] <;> ring
  simp_rw [hweight]
  unfold souriauChargeMean a
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

theorem souriauMassieu_gradient_eq_neg_meanCharge (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => souriauMassieu D (betaSlice beta i t)) (beta i) =
      -souriauChargeMean D beta i := by
  have hw : ∀ x, 0 < Real.exp
      (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)) :=
    fun x => Real.exp_pos _
  rw [show (fun t => souriauMassieu D (betaSlice beta i t)) =
      (fun t => logSumExp (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) t) by
    ext t
    exact souriauMassieu_slice_eq_logSumExp D beta i t]
  rw [logSumExp_deriv_eq_mean _ _ hw]
  rw [souriauChargeMean_eq_logSumExpMean D beta i]
  ring

theorem souriauMassieu_secondDeriv_eq_logSumExpVariance
    (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => deriv
      (fun t' => souriauMassieu D (betaSlice beta i t')) t) (beta i) =
      logSumExpVariance (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) (beta i) := by
  have hw : ∀ x, 0 < Real.exp
      (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)) :=
    fun x => Real.exp_pos _
  rw [show (fun t => souriauMassieu D (betaSlice beta i t)) =
      (fun t => logSumExp (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) t) by
    ext t
    exact souriauMassieu_slice_eq_logSumExp D beta i t]
  exact logSumExp_secondDeriv_eq_variance _ _ hw _

theorem souriauMassieu_secondDeriv_eq_chargeVariance
    (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => deriv
      (fun t' => souriauMassieu D (betaSlice beta i t')) t) (beta i) =
      souriauChargeVariance D beta i := by
  rw [souriauMassieu_secondDeriv_eq_logSumExpVariance]
  let w : State → ℝ := fun x => Real.exp
    (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j))
  let a : State → ℝ := fun x => -D.momentMap x i
  have hw : ∀ x, 0 < w x := fun x => Real.exp_pos _
  change logSumExpVariance w a (beta i) = souriauChargeVariance D beta i
  rw [logSumExpVariance_eq_centered w a hw (beta i)]
  have hpart : logSumExpPartition w a (beta i) = realGibbsPartition D beta := by
    unfold logSumExpPartition realGibbsPartition w a realGibbsKernel
      realPairingEnergy
    apply Finset.sum_congr rfl
    intro x _
    rw [← Real.exp_add]
    congr 1
    simp only [Fin.sum_univ_two]
    fin_cases i <;> simp [a, realPairingEnergy] <;> ring
  have hweight : ∀ x, logSumExpWeight w a (beta i) x =
      realGibbsWeight D beta x := by
    intro x
    unfold logSumExpWeight realGibbsWeight realGibbsKernel realPairingEnergy
    rw [hpart]
    rw [← Real.exp_add]
    congr 1
    simp only [Fin.sum_univ_two]
    fin_cases i <;> simp [a, realPairingEnergy] <;> ring
  have hmean : (∑ x : State, logSumExpWeight w a (beta i) x * a x) =
      -souriauChargeMean D beta i := by
    simp_rw [hweight]
    unfold a souriauChargeMean
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
  rw [hmean]
  simp_rw [hweight]
  unfold souriauChargeVariance
  apply Finset.sum_congr rfl
  intro x _
  dsimp [a]
  ring

theorem souriauMassieu_secondDeriv_nonneg (beta : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ deriv (fun t => deriv
      (fun t' => souriauMassieu D (betaSlice beta i t')) t) (beta i) := by
  rw [souriauMassieu_secondDeriv_eq_logSumExpVariance]
  exact logSumExpVariance_nonneg _ _ (fun x => Real.exp_pos _) _

end InfoGeometry.Lie
