import InfoGeometry.Algebraic.CartanSouriauMassieu
import InfoGeometry.Analytic.LogSumExp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Finset

namespace InfoGeometry.Canonical

open InfoGeometry.Algebraic.CartanSouriauMassieu
open InfoGeometry.Analytic

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (F : Family ι) (β v : Fin 2 → ℝ)

theorem energy_add_direction (t : ℝ) (m : ι) :
    energy F (fun a => β a + t * v a) m =
      energy F β m + t * directionalCharge F v m := by
  unfold energy directionalCharge
  simp_rw [add_mul, mul_assoc]
  rw [sum_add_distrib]
  congr 1
  rw [← mul_sum]

theorem unnormalizedWeight_add_direction (t : ℝ) (m : ι) :
    unnormalizedWeight F (fun a => β a + t * v a) m =
      unnormalizedWeight F β m * Real.exp (-(t * directionalCharge F v m)) := by
  unfold unnormalizedWeight
  rw [energy_add_direction F β v t m]
  rw [neg_add, Real.exp_add]
  ring

theorem partition_along_direction (t : ℝ) :
    partition F (fun a => β a + t * v a) =
      ∑ m : ι, unnormalizedWeight F β m * Real.exp (-(t * directionalCharge F v m)) := by
  unfold partition
  apply sum_congr rfl
  intro m _
  exact unnormalizedWeight_add_direction F β v t m

/-- 
The directional derivative of the Massieu potential at t = 0 
evaluates to the negative expected directional charge.
-/
theorem massieu_directional_deriv :
    deriv (fun t => massieu F (fun a => β a + t * v a)) 0 =
      -(∑ a : Fin 2, v a * chargeMean F β a) := by
  have hw : ∀ m, 0 < unnormalizedWeight F β m :=
    fun m => unnormalizedWeight_pos F β m
  have hslice :
      (fun t => massieu F (fun a => β a + t * v a)) =
        (fun t => logSumExp (fun m => unnormalizedWeight F β m)
          (fun m => -directionalCharge F v m) t) := by
    funext t
    unfold massieu logSumExp logSumExpPartition
    rw [partition_along_direction F β v t]
    apply congrArg Real.log
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    ring
  rw [hslice, logSumExp_deriv_eq_mean _ _ hw]
  let w : ι → ℝ := fun m => unnormalizedWeight F β m
  let a : ι → ℝ := fun m => -directionalCharge F v m
  change logSumExpMean w a 0 =
    -(∑ c : Fin 2, v c * chargeMean F β c)
  rw [logSumExpMean_eq_weighted_sum w a hw 0]
  have hpart : logSumExpPartition w a 0 = partition F β := by
    simp [logSumExpPartition, partition, w, a]
  have hweight : ∀ m, logSumExpWeight w a 0 m = probability F β m := by
    intro m
    unfold logSumExpWeight probability
    rw [hpart]
    simp [w, a, partition]
  have hdir_expect :
      (∑ m : ι, probability F β m * directionalCharge F v m) =
        ∑ c : Fin 2, v c * chargeMean F β c := by
    unfold directionalCharge chargeMean
    calc
      (∑ m : ι, probability F β m * ∑ c : Fin 2, v c * F.charge m c) =
          ∑ m : ι, ∑ c : Fin 2,
            probability F β m * (v c * F.charge m c) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
      _ = ∑ c : Fin 2, ∑ m : ι,
            probability F β m * (v c * F.charge m c) := by
        rw [Finset.sum_comm]
      _ = ∑ c : Fin 2, v c *
            ∑ m : ι, probability F β m * F.charge m c := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
  simp_rw [hweight]
  unfold a
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  exact congrArg Neg.neg hdir_expect

/-- 
The second directional derivative of the Massieu potential at t = 0 
evaluates to the directional variance of the charge.
-/
theorem massieu_directional_second_deriv :
    deriv (fun t => deriv (fun t' => massieu F (fun a => β a + t' * v a)) t) 0 =
      ∑ m : ι, probability F β m * (directionalCenteredCharge F β v m)^2 := by
  have hw : ∀ m, 0 < unnormalizedWeight F β m :=
    fun m => unnormalizedWeight_pos F β m
  have hslice :
      (fun t => massieu F (fun a => β a + t * v a)) =
        (fun t => logSumExp (fun m => unnormalizedWeight F β m)
          (fun m => -directionalCharge F v m) t) := by
    funext t
    unfold massieu logSumExp logSumExpPartition
    rw [partition_along_direction F β v t]
    apply congrArg Real.log
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    ring
  rw [hslice]
  rw [logSumExp_secondDeriv_eq_variance _ _ hw]
  let w : ι → ℝ := fun m => unnormalizedWeight F β m
  let a : ι → ℝ := fun m => -directionalCharge F v m
  change logSumExpVariance w a 0 =
    ∑ m : ι, probability F β m * (directionalCenteredCharge F β v m)^2
  rw [logSumExpVariance_eq_centered w a hw 0]
  have hpart : logSumExpPartition w a 0 = partition F β := by
    simp [logSumExpPartition, partition, w, a]
  have hweight : ∀ m, logSumExpWeight w a 0 m = probability F β m := by
    intro m
    unfold logSumExpWeight probability
    rw [hpart]
    simp [w, a, partition]
  have hdir_expect :
      (∑ m : ι, probability F β m * directionalCharge F v m) =
        ∑ c : Fin 2, v c * chargeMean F β c := by
    unfold directionalCharge chargeMean
    calc
      (∑ m : ι, probability F β m * ∑ c : Fin 2, v c * F.charge m c) =
          ∑ m : ι, ∑ c : Fin 2,
            probability F β m * (v c * F.charge m c) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
      _ = ∑ c : Fin 2, ∑ m : ι,
            probability F β m * (v c * F.charge m c) := by
        rw [Finset.sum_comm]
      _ = ∑ c : Fin 2, v c *
            ∑ m : ι, probability F β m * F.charge m c := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
  have hmean :
      (∑ m : ι, logSumExpWeight w a 0 m * a m) =
        -(∑ c : Fin 2, v c * chargeMean F β c) := by
    simp_rw [hweight]
    unfold a
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
    exact congrArg Neg.neg hdir_expect
  rw [hmean]
  simp_rw [hweight]
  unfold a directionalCenteredCharge centeredCharge directionalCharge
  apply Finset.sum_congr rfl
  intro m hm
  have hsum :
      (∑ a : Fin 2, v a * (F.charge m a - chargeMean F β a)) =
        (∑ a : Fin 2, v a * F.charge m a) -
          ∑ a : Fin 2, v a * chargeMean F β a := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  ring

/-- 
The second directional derivative coincides with the covariance quadratic form. 
This algebraically closes the Hessian packaging.
-/
theorem massieu_directional_second_deriv_eq_covariance :
    deriv (fun t => deriv (fun t' => massieu F (fun a => β a + t' * v a)) t) 0 =
      ∑ a : Fin 2, ∑ b : Fin 2, v a * chargeCovariance F β a b * v b := by
  rw [massieu_directional_second_deriv F β v]
  rw [chargeCovariance_quadratic_eq_expect_sq]
  unfold directionalCenteredCharge
  rfl

end InfoGeometry.Canonical
