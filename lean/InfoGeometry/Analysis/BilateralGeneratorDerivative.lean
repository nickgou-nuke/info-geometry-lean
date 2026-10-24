/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NoncommRing

/-!
# Differential contract for bilateral generator actions

The two factor ODEs are explicit hypotheses. No transform integral, convergence,
exponential identification, or interchange of differentiation and integration
is asserted. The signal may also vary with time.
-/

namespace InfoGeometry.Analysis.BilateralGeneratorDerivative

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Product rule with independent left and right generator equations. -/
theorem hasDerivAt_bilateral {left signal right : ℝ → A} {a b v : A} {t : ℝ}
    (hl : HasDerivAt left (a * left t) t)
    (hx : HasDerivAt signal v t)
    (hr : HasDerivAt right (right t * b) t) :
    HasDerivAt (fun u => left u * signal u * right u)
      (a * (left t * signal t * right t) + left t * v * right t +
        (left t * signal t * right t) * b) t := by
  convert (hl.mul hx).mul hr using 1 <;> noncomm_ring

/-- Opposite generator signs give a commutator for a fixed signal. -/
theorem hasDerivAt_commutator {left right : ℝ → A} {a x : A} {t : ℝ}
    (hl : HasDerivAt left (a * left t) t)
    (hr : HasDerivAt right (right t * (-a)) t) :
    HasDerivAt (fun u => left u * x * right u)
      (a * (left t * x * right t) - (left t * x * right t) * a) t := by
  convert hasDerivAt_bilateral hl (hasDerivAt_const t x) hr using 1 <;> noncomm_ring

/-- Equal generator signs give an anticommutator for a fixed signal. -/
theorem hasDerivAt_anticommutator {left right : ℝ → A} {a x : A} {t : ℝ}
    (hl : HasDerivAt left (a * left t) t)
    (hr : HasDerivAt right (right t * a) t) :
    HasDerivAt (fun u => left u * x * right u)
      (a * (left t * x * right t) + (left t * x * right t) * a) t := by
  convert hasDerivAt_bilateral hl (hasDerivAt_const t x) hr using 1 <;> noncomm_ring

end InfoGeometry.Analysis.BilateralGeneratorDerivative
