/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.Calculus.Deriv.Add
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
    (params : GrandCanonicalParams Data) (β : ℝ) :
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

end InfoGeometry.GrandCanonical
