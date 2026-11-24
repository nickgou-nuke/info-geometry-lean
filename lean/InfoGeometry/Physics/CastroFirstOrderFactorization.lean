/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Physics.HarishChandraCasimirBridge

/-!
# Castro's first-order expressions in a real logarithmic coordinate

The carrier is the native function space `ℝ → ℂ`.  The potential `W` is already
expressed in the logarithmic coordinate: for a positive-axis potential `V`, its
intended specialization is `W u = V (Real.exp u)`.

For `psi s k W u = exp ((-s + k) * u + W u)`, the derivative is proved using
`HasDerivAt`.  The two displayed first-order expressions are

* `D1 = -∂ + W' + k`;
* `D2 = +∂ + W' + k`.

Global differentiability of `W` gives an equality of functions `D1 psi = s psi`.
Rewriting by that equality before differentiating proves the actual composite
`D2 (D1 psi)`.  No second derivative of `W` is required.  Its equality with the
existing quadratic parameter `casimirEigenvalue s = s * (1 - s)` holds at `u`
exactly when `s = 0` or `deriv W u = 1 / 2 - k`.

The separate algebraic expression `inversionDual = +∂ - W' + 1 - k` is exactly
`1 - D1`. Identifying it with conjugation by coordinate inversion additionally
requires compatibility of the potential with inversion; that operator identity
is not asserted here. Its composite with `D1` has the quadratic value on every displayed mode. These
are pointwise differential identities; no Hilbert-space domain, adjointness,
theta specialization, spectral reality, or zeta-zero correspondence is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.CastroFirstOrderFactorization

open InfoGeometry.Physics.HarishChandraCasimir

/-- The potential-weighted mode in the real logarithmic coordinate. -/
def psi (s k : ℂ) (W : ℝ → ℂ) (u : ℝ) : ℂ :=
  Complex.exp ((-s + k) * (u : ℂ) + W u)

/-- The first displayed expression, `-∂ + W' + k`. -/
def D1 (k : ℂ) (W f : ℝ → ℂ) (u : ℝ) : ℂ :=
  -deriv f u + (deriv W u + k) * f u

/-- The second displayed expression, `+∂ + W' + k`. -/
def D2 (k : ℂ) (W f : ℝ → ℂ) (u : ℝ) : ℂ :=
  deriv f u + (deriv W u + k) * f u

/-- The algebraic partner `+∂ - W' + 1 - k = 1 - D1`; the name anticipates
inversion compatibility, which is not a premise or conclusion of this definition. -/
def inversionDual (k : ℂ) (W f : ℝ → ℂ) (u : ℝ) : ℂ :=
  deriv f u + (1 - k - deriv W u) * f u

/-- Every displayed exponential mode is nonzero at every real coordinate. -/
@[simp]
theorem psi_ne_zero (s k : ℂ) (W : ℝ → ℂ) (u : ℝ) :
    psi s k W u ≠ 0 :=
  Complex.exp_ne_zero _

/-- The wavefunction derivative follows from the real-to-complex chain rule. -/
theorem hasDerivAt_psi (s k : ℂ) {W : ℝ → ℂ} {u : ℝ} {w : ℂ}
    (hW : HasDerivAt W w u) :
    HasDerivAt (psi s k W) ((-s + k + w) * psi s k W u) u := by
  have hid : HasDerivAt (fun v : ℝ => (v : ℂ)) (1 : ℂ) u := by
    simpa using (hasDerivAt_id u).ofReal_comp
  have hlinear : HasDerivAt (fun v : ℝ => (-s + k) * (v : ℂ)) (-s + k) u := by
    simpa only [mul_one] using hid.const_mul (-s + k)
  have h := (hlinear.add hW).cexp
  rw [mul_comm] at h
  exact h

/-- Pointwise derivative readback under a local differentiability hypothesis. -/
theorem deriv_psi (s k : ℂ) {W : ℝ → ℂ} {u : ℝ}
    (hW : DifferentiableAt ℝ W u) :
    deriv (psi s k W) u =
      (-s + k + deriv W u) * psi s k W u :=
  (hasDerivAt_psi s k hW.hasDerivAt).deriv

/-- The first-order eigenfunction equation is an actual derivative identity. -/
theorem D1_psi (s k : ℂ) {W : ℝ → ℂ} {u : ℝ}
    (hW : DifferentiableAt ℝ W u) :
    D1 k W (psi s k W) u = s * psi s k W u := by
  rw [D1, deriv_psi s k hW]
  ring

/-- Global differentiability makes the first-order eigenfunction identity an
equality of functions, so it may safely be rewritten beneath a derivative. -/
theorem D1_psi_fun (s k : ℂ) {W : ℝ → ℂ} (hW : Differentiable ℝ W) :
    D1 k W (psi s k W) = fun u => s * psi s k W u := by
  funext u
  exact D1_psi s k (hW u)

/-- Differentiating the first-order eigenfunction identity requires only the
first derivative of `W`, after the equality of functions has been established. -/
theorem hasDerivAt_D1_psi (s k : ℂ) {W : ℝ → ℂ}
    (hW : Differentiable ℝ W) (u : ℝ) :
    HasDerivAt (D1 k W (psi s k W))
      (s * ((-s + k + deriv W u) * psi s k W u)) u := by
  rw [D1_psi_fun s k hW]
  exact (hasDerivAt_psi s k (hW u).hasDerivAt).const_mul s

/-- The actual composite of the two displayed first-order expressions. -/
theorem D2_D1_psi (s k : ℂ) {W : ℝ → ℂ}
    (hW : Differentiable ℝ W) (u : ℝ) :
    D2 k W (D1 k W (psi s k W)) u =
      s * (-s + 2 * k + 2 * deriv W u) * psi s k W u := by
  rw [D2, (hasDerivAt_D1_psi s k hW u).deriv, D1_psi s k (hW u)]
  ring

/-- The algebraic partner is the identity operator minus `D1`, pointwise. -/
theorem inversionDual_eq_sub_D1 (k : ℂ) (W f : ℝ → ℂ) (u : ℝ) :
    inversionDual k W f u = f u - D1 k W f u := by
  unfold inversionDual D1
  ring

/-- The difference between the printed partner and the inversion partner is
multiplication by the exact potential-dependent coefficient. -/
theorem D2_sub_inversionDual (k : ℂ) (W f : ℝ → ℂ) (u : ℝ) :
    D2 k W f u - inversionDual k W f u =
      2 * (deriv W u - (1 / 2 - k)) * f u := by
  unfold D2 inversionDual
  ring

/-- The corrected partner gives the quadratic parameter on the actual mode,
without imposing any constant-potential-derivative condition. -/
theorem inversionDual_D1_psi (s k : ℂ) {W : ℝ → ℂ}
    (hW : Differentiable ℝ W) (u : ℝ) :
    inversionDual k W (D1 k W (psi s k W)) u =
      casimirEigenvalue s * psi s k W u := by
  rw [inversionDual, (hasDerivAt_D1_psi s k hW u).deriv,
    D1_psi s k (hW u)]
  unfold casimirEigenvalue
  ring

/-- The exact defect in assigning the quadratic parameter to `D2 ∘ D1`. -/
theorem D2_D1_psi_defect (s k : ℂ) {W : ℝ → ℂ}
    (hW : Differentiable ℝ W) (u : ℝ) :
    D2 k W (D1 k W (psi s k W)) u -
        casimirEigenvalue s * psi s k W u =
      s * (2 * (deriv W u - (1 / 2 - k))) * psi s k W u := by
  rw [D2_D1_psi s k hW u]
  unfold casimirEigenvalue
  ring

/-- At a real coordinate, the claimed quadratic eigenvalue holds exactly for
the zero mode or for the displayed constant derivative of the potential. -/
theorem D2_D1_psi_eq_casimir_iff (s k : ℂ) {W : ℝ → ℂ}
    (hW : Differentiable ℝ W) (u : ℝ) :
    D2 k W (D1 k W (psi s k W)) u =
        casimirEigenvalue s * psi s k W u ↔
      s = 0 ∨ deriv W u = 1 / 2 - k := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  rw [← sub_eq_zero, D2_D1_psi_defect s k hW u]
  simp only [mul_eq_zero, psi_ne_zero, htwo, false_or, or_false, sub_eq_zero]

/-- The zero mode satisfies the printed composite equation for every
differentiable potential.  Cancelling the factor `s` would lose this case. -/
theorem D2_D1_psi_zero (k : ℂ) {W : ℝ → ℂ}
    (hW : Differentiable ℝ W) (u : ℝ) :
    D2 k W (D1 k W (psi 0 k W)) u = 0 := by
  simpa using D2_D1_psi 0 k hW u

/-- The global eigenfunction equation retains the zero mode; for any nonzero
parameter it requires the same constant potential derivative everywhere. -/
theorem D2_D1_psi_eigenfunction_iff (s k : ℂ) {W : ℝ → ℂ}
    (hW : Differentiable ℝ W) :
    (∀ u : ℝ, D2 k W (D1 k W (psi s k W)) u =
      casimirEigenvalue s * psi s k W u) ↔
      s = 0 ∨ ∀ u : ℝ, deriv W u = 1 / 2 - k := by
  constructor
  · intro h
    by_cases hs : s = 0
    · exact Or.inl hs
    · right
      intro u
      exact ((D2_D1_psi_eq_casimir_iff s k hW u).mp (h u)).resolve_left hs
  · intro h u
    apply (D2_D1_psi_eq_casimir_iff s k hW u).mpr
    rcases h with hs | hderiv
    · exact Or.inl hs
    · exact Or.inr (hderiv u)

end InfoGeometry.Physics.CastroFirstOrderFactorization

end
