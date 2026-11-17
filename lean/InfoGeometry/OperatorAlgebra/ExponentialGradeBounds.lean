/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TransportLieDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith

/-!
# Exact real exponential weights on commutator eigenspaces

The carrier is the original, possibly noncommutative, complete real normed
algebra. A real commutator eigenvector has an exactly weighted orbit under
the existing analytic exponential conjugation. The integrating-factor
argument uses the existing derivative of that conjugation.

The norm conclusions distinguish a bounded orbit for all real times from
a contraction at one time. They do not identify this conjugation with the
modular flow of a specified state or construct an irreversible dynamics.
-/

namespace InfoGeometry.OperatorAlgebra.ExponentialGradeBounds

open InfoGeometry.Canonical

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A real eigenvector of the generator commutator has its exact exponential
weight under the actual algebra exponential conjugation. -/
theorem expTransport_eq_exp_smul_of_lie_eq
    (H X : A) (rate t : ℝ) (h : H * X - X * H = rate • X) :
    expTransport H X t = Real.exp (rate * t) • X := by
  have hf (s : ℝ) :
      HasDerivAt (fun r : ℝ => expTransport H X r)
        (rate • expTransport H X s) s := by
    simpa only [Ring.lie_def, h, expTransport_smul_seed] using
      hasDerivAt_expTransport H X s
  let g : ℝ → A := fun s => Real.exp ((-rate) * s) • expTransport H X s
  have hg (s : ℝ) : HasDerivAt g 0 s := by
    have he : HasDerivAt (fun r : ℝ => Real.exp ((-rate) * r))
        (Real.exp ((-rate) * s) * (-rate)) s := by
      exact (hasDerivAt_const_mul (x := s) (-rate)).exp
    convert! he.fun_smul (hf s) using 1;
      simp only [smul_smul, mul_neg, neg_smul, add_neg_cancel]
  have hconst : g t = g 0 :=
    is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt)
      (fun s => (hg s).deriv) t 0
  have hzero : g 0 = X := by simp [g, expTransport]
  rw [hzero] at hconst
  change Real.exp ((-rate) * t) • expTransport H X t = X at hconst
  have hscaled := congrArg (fun Y : A => Real.exp (rate * t) • Y) hconst
  simpa only [smul_smul, ← Real.exp_add, neg_mul, add_neg_cancel,
    Real.exp_zero, one_smul] using hscaled

/-- The exact operator norm weight of a real commutator eigenvector. -/
theorem norm_expTransport_eq_of_lie_eq
    (H X : A) (rate t : ℝ) (h : H * X - X * H = rate • X) :
    ‖expTransport H X t‖ = Real.exp (rate * t) * ‖X‖ := by
  rw [expTransport_eq_exp_smul_of_lie_eq H X rate t h, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- For a nonzero commutator eigenvector, contraction occurs exactly when
the signed exponential weight is nonpositive. -/
theorem norm_expTransport_le_norm_iff_of_lie_eq
    (H X : A) (rate t : ℝ) (h : H * X - X * H = rate • X)
    (hX : X ≠ 0) :
    ‖expTransport H X t‖ ≤ ‖X‖ ↔ rate * t ≤ 0 := by
  rw [norm_expTransport_eq_of_lie_eq H X rate t h]
  have hnorm : 0 < ‖X‖ := norm_pos_iff.mpr hX
  calc
    Real.exp (rate * t) * ‖X‖ ≤ ‖X‖ ↔ Real.exp (rate * t) ≤ 1 := by
      simpa only [one_mul] using
        (mul_le_mul_iff_left₀ hnorm :
          Real.exp (rate * t) * ‖X‖ ≤ 1 * ‖X‖ ↔ Real.exp (rate * t) ≤ 1)
    _ ↔ rate * t ≤ 0 := Real.exp_le_one_iff

/-- A real commutator eigenvector has a uniformly bounded orbit for all real
times exactly when its eigenvalue vanishes or the eigenvector is zero. -/
theorem bounded_expTransport_iff_of_lie_eq
    (H X : A) (rate : ℝ) (h : H * X - X * H = rate • X) :
    (∃ C : ℝ, ∀ t : ℝ, ‖expTransport H X t‖ ≤ C) ↔ rate = 0 ∨ X = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_cases hrate : rate = 0
    · exact Or.inl hrate
    · right
      by_contra hX
      have hnorm : 0 < ‖X‖ := norm_pos_iff.mpr hX
      have hb := hC (C / ‖X‖ / rate)
      rw [norm_expTransport_eq_of_lie_eq H X rate (C / ‖X‖ / rate) h,
        mul_div_cancel₀ (C / ‖X‖) hrate] at hb
      have hlower := mul_le_mul_of_nonneg_right
        (Real.add_one_le_exp (C / ‖X‖)) (norm_nonneg X)
      have hcancel : C / ‖X‖ * ‖X‖ = C :=
        div_mul_cancel₀ C (ne_of_gt hnorm)
      rw [add_mul, one_mul, hcancel] at hlower
      linarith
  · rintro (hrate | hX)
    · refine ⟨‖X‖, fun t => ?_⟩
      simpa only [hrate, zero_mul, Real.exp_zero, one_mul] using
        (norm_expTransport_eq_of_lie_eq H X rate t h).le
    · refine ⟨0, fun t => ?_⟩
      simp [hX, expTransport]

end InfoGeometry.OperatorAlgebra.ExponentialGradeBounds
