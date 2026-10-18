import InfoGeometry.Algebraic.CartanSouriauMassieu
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Monoid

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

theorem massieu_directional_hasDerivAt_zero
    (F : Family ι) (β v : Fin 2 → ℝ) :
    HasDerivAt (directionalMassieu F β v)
      (-(∑ m : ι, probability F β m * directionalCharge F v m)) 0 := by
  have hpart := hasDerivAt_partition_add_direction_zero F β v
  have hdir0 : directionalParameter β v 0 = β := by
    funext a
    simp [directionalParameter]
  have hne0 : partition F (directionalParameter β v 0) ≠ 0 := by
    rw [hdir0]
    exact (partition_pos F β).ne'
  have hlog := (Real.hasDerivAt_log hne0).comp 0 hpart
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
  rw [hdir0] at hlog
  have hderiv :
      (partition F β)⁻¹ *
          ∑ m : ι, -(unnormalizedWeight F β m * directionalCharge F v m) =
        -(∑ m : ι, probability F β m * directionalCharge F v m) := hfactor.symm
  change HasDerivAt
    (fun t => Real.log (partition F (directionalParameter β v t)))
    (-(∑ m : ι, probability F β m * directionalCharge F v m)) 0
  exact hlog.congr_deriv hderiv

theorem massieu_directional_deriv
    (F : Family ι) (β v : Fin 2 → ℝ) :
    deriv (directionalMassieu F β v) 0 =
      -(∑ m : ι, probability F β m * directionalCharge F v m) :=
  (massieu_directional_hasDerivAt_zero F β v).deriv

theorem massieu_directional_hasDerivAt
    (F : Family ι) (β v : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (directionalMassieu F β v)
      (-(∑ m : ι, probability F (directionalParameter β v t) m *
        directionalCharge F v m)) t := by
  let βt := directionalParameter β v t
  have hzero := massieu_directional_hasDerivAt_zero F βt v
  have hpath :
      (fun s : ℝ => directionalMassieu F β v (s + t)) =
        directionalMassieu F βt v := by
    funext s
    change massieu F (directionalParameter β v (s + t)) =
      massieu F (directionalParameter βt v s)
    apply congrArg (massieu F)
    funext a
    dsimp [βt, directionalParameter]
    ring
  have hshift :
      HasDerivAt (fun s : ℝ => directionalMassieu F β v (s + t))
        (-(∑ m : ι, probability F βt m * directionalCharge F v m)) 0 := by
    rw [hpath]
    exact hzero
  have hshift' :
      HasDerivAt (fun s : ℝ => directionalMassieu F β v (s + t))
        (-(∑ m : ι, probability F βt m * directionalCharge F v m)) (t - t) := by
    simpa using hshift
  have htranslated := HasDerivAt.comp_sub_const t t hshift'
  have hfinal : HasDerivAt (directionalMassieu F β v)
      (-(∑ m : ι, probability F βt m * directionalCharge F v m)) t := by
    simpa using htranslated
  simpa [βt] using hfinal

theorem massieu_directional_line_integral_eq_endpoint_difference
    (F : Family ι) (β v : Fin 2 → ℝ) :
    (∫ t in (0 : ℝ)..1,
      -(∑ m : ι, probability F (directionalParameter β v t) m *
        directionalCharge F v m)) =
      directionalMassieu F β v 1 - directionalMassieu F β v 0 := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (directionalMassieu F β v)
        (-(∑ m : ι, probability F (directionalParameter β v t) m *
          directionalCharge F v m)) t := by
    intro t ht
    exact massieu_directional_hasDerivAt F β v t
  have hweight_cont (m : ι) :
      Continuous (fun t : ℝ =>
        unnormalizedWeight F (directionalParameter β v t) m) := by
    unfold unnormalizedWeight
    fun_prop [energy, directionalParameter]
  have hpart_cont :
      Continuous (fun t : ℝ => partition F (directionalParameter β v t)) := by
    unfold partition
    apply continuous_finsetSum Finset.univ
    intro m hm
    exact hweight_cont m
  have hprob_cont (m : ι) :
      Continuous (fun t : ℝ => probability F (directionalParameter β v t) m) := by
    unfold probability
    exact (hweight_cont m).div hpart_cont
      (fun t => (partition_pos F (directionalParameter β v t)).ne')
  have hmean_cont :
      Continuous (fun t : ℝ =>
        ∑ m : ι, probability F (directionalParameter β v t) m *
          directionalCharge F v m) := by
    apply continuous_finsetSum Finset.univ
    intro m hm
    exact (hprob_cont m).mul continuous_const
  have hint : IntervalIntegrable
      (fun t : ℝ =>
        -(∑ m : ι, probability F (directionalParameter β v t) m *
          directionalCharge F v m)) MeasureTheory.volume 0 1 :=
    (hmean_cont.neg).intervalIntegrable 0 1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

end InfoGeometry.Algebraic.CartanSouriauMassieuDirectionalCalculus
