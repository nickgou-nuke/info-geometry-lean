/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.CastroFirstOrderFactorization
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Tactic

/-!
# Theta reflection and parameter identities for the Castro CT audit

The theta kernel below is Mathlib's actual Gaussian series, not a finite sum or
an assumed modular datum. Its modular equation gives the real logarithmic
potential and the reflection law of the exponential ansatz.

The final section audits the *argument* of the paper-defined signed kernel.
It makes no identification with a convergent integral or a sesquilinear form.
In particular it establishes neither positivity of a pairing nor operator selfadjointness,
and it has no Riemann Hypothesis consequence.

Source: C. Castro Perelman, February 2007, revised March 2007,
https://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/castro2007RH.pdf,
equations (2.2), (2.7), (2.29), (2.33), and (2.36).
-/

noncomputable section

namespace InfoGeometry.Arithmetic.CastroPerelmanCTAudit

open InfoGeometry.Physics.CastroFirstOrderFactorization

/-! ## The actual Gaussian theta potential -/

/-- Positivity follows from Mathlib's convergent Gaussian series for positive input. -/
theorem evenKernel_zero_pos {x : ℝ} (hx : 0 < x) :
    0 < HurwitzZeta.evenKernel 0 x := by
  have hs : HasSum (fun n : ℤ => Real.exp (-Real.pi * (n : ℝ) ^ 2 * x))
      (HurwitzZeta.evenKernel 0 x) := by
    simpa using HurwitzZeta.hasSum_int_evenKernel 0 hx
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- Native Gauss--Jacobi inversion, oriented as in the paper. -/
theorem evenKernel_zero_inv {x : ℝ} (hx : 0 < x) :
    HurwitzZeta.evenKernel 0 (1 / x) =
      x ^ (1 / 2 : ℝ) * HurwitzZeta.evenKernel 0 x := by
  have hp : x ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have h := congrArg (fun y : ℝ => x ^ (1 / 2 : ℝ) * y)
    (HurwitzZeta.evenKernel_functional_equation 0 x)
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero, ← mul_assoc,
    mul_one_div_cancel hp, one_mul] at h
  exact h.symm

/-- The real potential `W(u) = log(G(exp(ell*u))) / 2` in logarithmic coordinate. -/
def thetaLogPotential (ell u : ℝ) : ℝ :=
  Real.log (HurwitzZeta.evenKernel 0 (Real.exp (ell * u))) / 2

/-- Modular inversion yields the exact additive shift of the logarithmic potential. -/
theorem thetaLogPotential_neg (ell u : ℝ) :
    thetaLogPotential ell (-u) = thetaLogPotential ell u + ell * u / 4 := by
  have hx : 0 < Real.exp (ell * u) := Real.exp_pos _
  have hinv : Real.exp (ell * -u) = 1 / Real.exp (ell * u) := by
    rw [mul_neg, Real.exp_neg, one_div]
  unfold thetaLogPotential
  rw [hinv, evenKernel_zero_inv hx,
    Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (evenKernel_zero_pos hx).ne',
    Real.log_rpow hx, Real.log_exp]
  ring

/-- Exponent compatibility is an algebraic condition, independent of the spectral label. -/
theorem reflection_exponent_iff (s k ell : ℂ) :
    s - k + ell / 4 = s - 1 + k ↔ ell = 4 * (2 * k - 1) := by
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    linear_combination h / 4

/-- Under the scaling constraint, the actual theta ansatz obeys the reflection law.
This is a sufficient global law; pointwise equality at `u = 0` imposes no constraint. -/
theorem theta_psi_reflection (s : ℂ) (k ell u : ℝ)
    (hscale : ell = 4 * (2 * k - 1)) :
    psi s (k : ℂ) (fun v => (thetaLogPotential ell v : ℂ)) (-u) =
      psi (1 - s) (k : ℂ) (fun v => (thetaLogPotential ell v : ℂ)) u := by
  unfold psi
  congr 1
  dsimp only
  rw [thetaLogPotential_neg]
  have hscaleC : (ell : ℂ) = 4 * (2 * (k : ℂ) - 1) := by
    exact_mod_cast hscale
  push_cast
  rw [hscaleC]
  ring

/-! ## Scalar parameter compatibility, separate from an analytic pairing -/

/-- The affine symmetry condition of equation (2.33), with its denominator hypothesis. -/
theorem affine_compatibility_iff (k ell : ℝ) (hell : ell ≠ 0) :
    -2 / ell + 2 * ((4 * k - 1) / ell) = 1 ↔ ell = 4 * (2 * k - 1) := by
  constructor
  · intro h
    field_simp [hell] at h
    linarith
  · intro h
    field_simp [hell]
    linarith

/-- The completed-zeta argument in the paper's label kernel, without an integral claim. -/
def pairingArgument (k ell : ℝ) (s₁ s₂ : ℂ) : ℂ :=
  (2 / (ell : ℂ)) * (2 * (k : ℂ) - (star s₁ + s₂))

/-- On conjugate-reflected labels, the argument is `1/2` for every spectral label. -/
theorem pairingArgument_ct (k ell : ℝ) (hell : ell ≠ 0)
    (hscale : ell = 4 * (2 * k - 1)) (s : ℂ) :
    pairingArgument k ell s (1 - star s) = 1 / 2 := by
  have hellC : (ell : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hell
  have hscaleC : (ell : ℂ) = 4 * (2 * (k : ℂ) - 1) := by
    exact_mod_cast hscale
  unfold pairingArgument
  rw [show star s + (1 - star s) = (1 : ℂ) by ring]
  field_simp [hellC]
  linear_combination -hscaleC

/-- Substitution in any scalar function of the argument. The signed factor is the
paper's convention; no equality with an ordinary positive-orientation Mellin integral
and no nonzero value of `Z (1/2)` is asserted. -/
theorem signed_label_kernel_ct (Z : ℂ → ℂ) (k ell : ℝ) (hell : ell ≠ 0)
    (hscale : ell = 4 * (2 * k - 1)) (s : ℂ) :
    (2 / (ell : ℂ)) * Z (pairingArgument k ell s (1 - star s)) =
      (2 / (ell : ℂ)) * Z (1 / 2) := by
  rw [pairingArgument_ct k ell hell hscale s]

end InfoGeometry.Arithmetic.CastroPerelmanCTAudit

end
