import InfoGeometry.Algebraic.CartanSouriauMassieu
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Finset

namespace InfoGeometry.Canonical

open InfoGeometry.Algebraic.CartanSouriauMassieu

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
      -(∑ a : Fin 2, v a * chargeMean F β a) := sorry

/-- 
The second directional derivative of the Massieu potential at t = 0 
evaluates to the directional variance of the charge.
-/
theorem massieu_directional_second_deriv :
    deriv (fun t => deriv (fun t' => massieu F (fun a => β a + t' * v a)) t) 0 =
      ∑ m : ι, probability F β m * (directionalCenteredCharge F β v m)^2 := sorry

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
