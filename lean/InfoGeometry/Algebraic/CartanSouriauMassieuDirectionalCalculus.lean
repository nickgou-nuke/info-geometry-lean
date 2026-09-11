import InfoGeometry.Algebraic.CartanSouriauMassieu
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Directional calculus for the finite Souriau/Massieu family

This is the one-dimensional calculus layer.  The parameter is restricted to a
line `β + t v`; full Fréchet differentiability is deliberately left to a
separate owner.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CartanSouriauMassieuDirectionalCalculus

open scoped BigOperators
open Finset
open InfoGeometry.Algebraic.CartanSouriauMassieu

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def directionalParameter (β v : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  fun a => β a + t * v a

def directionalMassieu (F : Family ι) (β v : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  massieu F (directionalParameter β v t)

theorem energy_add_direction
    (F : Family ι) (β v : Fin 2 → ℝ) (t : ℝ) (m : ι) :
    energy F (directionalParameter β v t) m =
      energy F β m + t * directionalCharge F v m := by
  unfold energy directionalParameter directionalCharge
  simp_rw [add_mul, mul_assoc]
  rw [sum_add_distrib]
  congr 1
  rw [← mul_sum]

theorem unnormalizedWeight_add_direction
    (F : Family ι) (β v : Fin 2 → ℝ) (t : ℝ) (m : ι) :
    unnormalizedWeight F (directionalParameter β v t) m =
      unnormalizedWeight F β m *
        Real.exp (-(t * directionalCharge F v m)) := by
  unfold unnormalizedWeight
  rw [energy_add_direction]
  rw [neg_add, Real.exp_add]
  ring

theorem hasDerivAt_unnormalizedWeight_add_direction_zero
    (F : Family ι) (β v : Fin 2 → ℝ) (m : ι) :
    HasDerivAt
      (fun t => unnormalizedWeight F (directionalParameter β v t) m)
      (-(unnormalizedWeight F β m * directionalCharge F v m)) 0 := by
  have hfun :
      (fun t => unnormalizedWeight F (directionalParameter β v t) m) =
        (fun t => unnormalizedWeight F β m *
          Real.exp (-(t * directionalCharge F v m))) := by
    funext t
    exact unnormalizedWeight_add_direction F β v t m
  rw [hfun]
  have hlin : HasDerivAt
      (fun t : ℝ => -(t * directionalCharge F v m))
      (-(directionalCharge F v m)) 0 := by
    convert (hasDerivAt_id (x := (0 : ℝ))).mul_const
      (-(directionalCharge F v m)) using 1 <;> simp <;> ring
  have hexp :=
    (Real.hasDerivAt_exp (-(0 * directionalCharge F v m))).comp 0 hlin
  have hmul := hexp.const_mul (unnormalizedWeight F β m)
  convert hmul using 1 <;> simp <;> ring

theorem hasDerivAt_partition_add_direction_zero
    (F : Family ι) (β v : Fin 2 → ℝ) :
    HasDerivAt
      (fun t => partition F (directionalParameter β v t))
      (∑ m : ι,
        -(unnormalizedWeight F β m * directionalCharge F v m)) 0 := by
  unfold partition
  simpa using (HasDerivAt.fun_sum
    (u := (Finset.univ : Finset ι))
    (fun m _hm => hasDerivAt_unnormalizedWeight_add_direction_zero F β v m))

theorem massieu_directional_deriv
    (F : Family ι) (β v : Fin 2 → ℝ) :
    deriv (directionalMassieu F β v) 0 =
      -(∑ m : ι, probability F β m * directionalCharge F v m) := by
  have hpart := hasDerivAt_partition_add_direction_zero F β v
  have hdir0 : directionalParameter β v 0 = β := by
    funext a
    simp [directionalParameter]
  have hne0 : partition F (directionalParameter β v 0) ≠ 0 := by
    rw [hdir0]
    exact (partition_pos F β).ne'
  have hlog :=
    (Real.hasDerivAt_log hne0).comp 0 hpart
  have hderiv := hlog.deriv
  rw [hdir0] at hderiv
  simp only [Function.comp_def] at hderiv
  change deriv (fun t => Real.log
      (partition F (directionalParameter β v t))) 0 = _
  have hfactor :
      -(∑ m : ι, probability F β m * directionalCharge F v m) =
        (partition F β)⁻¹ *
          ∑ m : ι, -(unnormalizedWeight F β m * directionalCharge F v m) := by
    unfold probability
    calc
      -(∑ m : ι,
          (unnormalizedWeight F β m / partition F β) *
            directionalCharge F v m) =
          -(∑ m : ι,
            (partition F β)⁻¹ *
              (unnormalizedWeight F β m * directionalCharge F v m)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro m _hm
            field_simp
      _ = -((partition F β)⁻¹ *
            ∑ m : ι, unnormalizedWeight F β m * directionalCharge F v m) := by
            rw [Finset.mul_sum]
      _ = (partition F β)⁻¹ *
            ∑ m : ι, -(unnormalizedWeight F β m * directionalCharge F v m) := by
            rw [Finset.sum_neg_distrib]
            ring
  rw [hfactor] at ⊢
  exact hderiv

end InfoGeometry.Algebraic.CartanSouriauMassieuDirectionalCalculus
