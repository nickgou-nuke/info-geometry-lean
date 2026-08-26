/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import InfoGeometry.GrandCanonical.Core

/-!
# Finite Gibbs temperature response

The mean energy decreases with inverse temperature at a rate equal to the
negative Gibbs energy variance. This is the finite linear-response identity
used to interpret a susceptibility peak as a sharp but finite crossover.
-/

namespace InfoGeometry.GrandCanonical

open scoped BigOperators

variable {Data : Type*} [Fintype Data] [Nonempty Data]

theorem deriv_mean_eq_neg_variance
    (params : InfoGeometry.GrandCanonical.GrandCanonicalParams Data) (β : ℝ) :
    deriv (fun t : ℝ => mean params t) β = -variance params β := by
  have hfun :
      (fun t : ℝ => deriv (potential params) t) =
        (fun t : ℝ => -mean params t) := by
    funext t
    exact potential_deriv_eq_neg_mean params t
  have hh := potential_second_derivative_eq_variance params β
  unfold hessian at hh
  rw [hfun] at hh
  have hneg :
      (fun t : ℝ => -mean params t) = -(fun t : ℝ => mean params t) := by
    funext t
    rfl
  rw [hneg, deriv.neg] at hh
  linarith

private lemma hasDerivAt_firstMomentUnnormalized
    (params : InfoGeometry.GrandCanonical.GrandCanonicalParams Data) (β : ℝ) :
    HasDerivAt (firstMomentUnnormalized params)
      (-(secondMomentUnnormalized params β)) β := by
  classical
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ x, params.energy x * Real.exp (-t * params.energy x))
        (∑ x, -(params.energy x) ^ (2 : ℕ) *
          Real.exp (-β * params.energy x)) β := by
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset Data))
        (fun x _hx =>
          (hasDerivAt_exp_neg_mul_energy params β x).const_mul
            (params.energy x)))
  unfold firstMomentUnnormalized secondMomentUnnormalized
  simpa [Finset.sum_neg_distrib] using hsum

theorem deriv_mean_at_inverse_temperature
    (params : InfoGeometry.GrandCanonical.GrandCanonicalParams Data) {ε : ℝ} (hε : 0 < ε) :
    deriv (fun t : ℝ => mean params t⁻¹) ε =
      variance params ε⁻¹ / ε ^ (2 : ℕ) := by
  have hnum : DifferentiableAt ℝ (firstMomentUnnormalized params) ε⁻¹ :=
    (hasDerivAt_firstMomentUnnormalized params ε⁻¹).differentiableAt
  have hden : DifferentiableAt ℝ (partition params) ε⁻¹ :=
    (hasDerivAt_partition params ε⁻¹).differentiableAt
  have hmean_fun :
      mean params = fun t : ℝ =>
        firstMomentUnnormalized params t / partition params t := by
    funext t
    exact mean_eq_firstMoment_div_partition params t
  have hmean : DifferentiableAt ℝ (mean params) ε⁻¹ := by
    rw [hmean_fun]
    simpa [div_eq_mul_inv] using
      hnum.mul (hden.inv (ne_of_gt (partition_pos params ε⁻¹)))
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-(ε ^ (2 : ℕ))⁻¹) ε :=
    hasDerivAt_inv (ne_of_gt hε)
  have hcomp := hmean.hasDerivAt.comp ε hinv
  have hderiv := hcomp.deriv
  simpa [Function.comp_def, deriv_mean_eq_neg_variance, div_eq_mul_inv,
    neg_mul, neg_neg] using hderiv

end InfoGeometry.GrandCanonical
