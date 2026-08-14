import InfoGeometry.Algebraic.CartanSouriauMassieu
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
  rw [Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

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
      (-(directionalCharge F v m)) using 1 <;> ring
  have hexp := (Real.hasDerivAt_exp 0).comp hlin
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
  have hlog := (Real.hasDerivAt_log (partition_pos F β).ne').comp hpart
  have hderiv := hlog.deriv
  unfold directionalMassieu at hderiv
  rw [directionalParameter] at hderiv
  simpa [probability, partition, unnormalizedWeight, mul_div_assoc,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hderiv

end InfoGeometry.Algebraic.CartanSouriauMassieuDirectionalCalculus
