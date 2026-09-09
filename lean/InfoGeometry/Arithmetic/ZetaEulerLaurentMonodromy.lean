import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic
import InfoGeometry.Projective.KleinQuadricMonodromy

/-!
# Zeta Euler--Laurent--Monodromy core

The theorem-safe bridge between:

* the logarithmic coordinate `y = log x`;
* the Euler operator `x d/dx = d/dy`;
* the regularized Riemann zeta function;
* the logarithmic derivative `ζ'/ζ`;
* local meromorphic order and the corresponding Laurent principal term;
* the `2πi` monodromy/de Rham period of a divisor point.

This file formalizes the local analytic and Laurent-principal structure of the
arithmetic connection `-ζ'/ζ` and its topological period readouts.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Complex Filter Set
open scoped Topology Polynomial

namespace InfoGeometry.Arithmetic.ZetaEulerLaurentMonodromy

open DirichletCharacter
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/-! ## 1. Logarithmic coordinate and Euler derivative -/

/-- Pull a function on `ℂˣ` back to its logarithmic universal-cover coordinate. -/
def expPullback (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  f (Complex.exp y)

/-- Euler/logarithmic derivative in the argument: `x f'(x)`. -/
def eulerDerivative (f : ℂ → ℂ) (x : ℂ) : ℂ :=
  x * deriv f x

/-- Chain rule: after `x = exp y`, ordinary `y`-differentiation is the
Euler derivative `x d/dx`. -/
theorem hasDerivAt_expPullback
    {f : ℂ → ℂ} {y a : ℂ}
    (hf : HasDerivAt f a (Complex.exp y)) :
    HasDerivAt (expPullback f) (Complex.exp y * a) y := by
  simpa [expPullback, mul_comm] using
    hf.comp y (Complex.hasDerivAt_exp y)

/-- Derivative readback of `d/d(log x) = x d/dx`. -/
theorem deriv_expPullback_eq_eulerDerivative
    (f : ℂ → ℂ) (y : ℂ)
    (hf : DifferentiableAt ℂ f (Complex.exp y)) :
    deriv (expPullback f) y =
      eulerDerivative f (Complex.exp y) := by
  have h :=
    hf.hasDerivAt.comp y (Complex.hasDerivAt_exp y)
  simpa [expPullback, eulerDerivative, mul_comm] using h.deriv

/-! ## 2. Exact algebraic Euler operator on polynomials -/

/-- Formal Euler operator `X d/dX` on complex polynomials. -/
def polynomialEuler (p : ℂ[X]) : ℂ[X] :=
  Polynomial.X * Polynomial.derivative p

@[simp]
theorem polynomialEuler_C (c : ℂ) :
    polynomialEuler (Polynomial.C c) = 0 := by
  simp [polynomialEuler]

/-- Monomials are exact eigenvectors of the formal Euler operator. -/
@[simp]
theorem polynomialEuler_X_pow_succ (n : ℕ) :
    polynomialEuler (Polynomial.X ^ (n + 1) : ℂ[X]) =
      Polynomial.C (n + 1 : ℂ) * Polynomial.X ^ (n + 1) := by
  rw [polynomialEuler, Polynomial.derivative_X_pow_succ]
  ring

/-! ## 3. Native pole clearing at `s = 1` -/

/-- Entire regularized zeta owner supplied by Mathlib's trivial
Dirichlet-character continuation. -/
abbrev zetaPoleRemoved : ℂ → ℂ :=
  LFunctionTrivChar₁ 1

/-- Away from `1`, the regularized owner is `(s-1) ζ(s)`. -/
theorem zetaPoleRemoved_apply_of_ne_one
    {s : ℂ} (hs : s ≠ 1) :
    zetaPoleRemoved s = (s - 1) * riemannZeta s := by
  simp [zetaPoleRemoved, LFunctionTrivChar₁, Function.update_of_ne hs]

/-- The regularized zeta function is entire. -/
theorem differentiable_zetaPoleRemoved :
    Differentiable ℂ zetaPoleRemoved := by
  exact differentiable_LFunctionTrivChar₁ 1

/-- Its value at the regularized pole is nonzero. -/
theorem zetaPoleRemoved_one_ne_zero :
    zetaPoleRemoved 1 ≠ 0 := by
  exact LFunctionTrivChar₁_apply_one_ne_zero 1

/-- Native residue-one statement for the raw Riemann zeta function. -/
theorem riemannZeta_simplePole_residue_one :
    Tendsto
      (fun s : ℂ => (s - 1) * riemannZeta s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (1 : ℂ)) := by
  exact riemannZeta_residue_one

/-- Derivative of the regularized owner away from the pole. -/
theorem deriv_zetaPoleRemoved_apply_of_ne_one
    {s : ℂ} (hs : s ≠ 1) :
    deriv zetaPoleRemoved s =
      (s - 1) * deriv riemannZeta s + riemannZeta s := by
  simpa [zetaPoleRemoved] using
    (deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs)

/-- Exact pole/regular decomposition of the arithmetic connection
`-ζ'/ζ` away from the pole and zeros:

`-d log ζ = ds/(s-1) - d log ((s-1)ζ)`.
-/
theorem neg_logDeriv_riemannZeta_eq_pole_sub_regular
    {s : ℂ}
    (hs : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    -logDeriv riemannZeta s =
      1 / (s - 1) - logDeriv zetaPoleRemoved s := by
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hG : zetaPoleRemoved s ≠ 0 := by
    rw [zetaPoleRemoved_apply_of_ne_one hs]
    exact mul_ne_zero hs0 hz
  rw [logDeriv_apply, logDeriv_apply]
  rw [deriv_zetaPoleRemoved_apply_of_ne_one hs]
  rw [zetaPoleRemoved_apply_of_ne_one hs]
  field_simp [hs0, hz, hG]
  ring

/-- The regular remainder in the pole decomposition is continuous at `s = 1`
and away from zeta zeros. -/
theorem continuousOn_neg_logDeriv_zetaPoleRemoved :
    ContinuousOn
      (fun s : ℂ => -logDeriv zetaPoleRemoved s)
      {s : ℂ | s = 1 ∨ riemannZeta s ≠ 0} := by
  have h := continuousOn_neg_logDeriv_LFunctionTrivChar₁ (n := 1)
  simp only [LFunctionTrivChar, LFunction_modOne_eq] at h
  have heq : (fun s : ℂ => -logDeriv zetaPoleRemoved s) =
             (fun s : ℂ => -deriv (LFunctionTrivChar₁ 1) s / LFunctionTrivChar₁ 1 s) := by
    ext s
    simp [zetaPoleRemoved, logDeriv_apply, neg_div]
  rw [heq]
  exact h

/-! ## 4. Simple zeta zeros and logarithmic residues -/

/-- General residue formula for logarithmic derivative at a simple zero. -/
lemma tendsto_mul_logDeriv_of_hasDerivAt_of_continuousAt
    {f : ℂ → ℂ} {ρ : ℂ} {f' : ℂ}
    (hf : HasDerivAt f f' ρ)
    (hf0 : f ρ = 0)
    (hf'0 : f' ≠ 0)
    (hcont : ContinuousAt (deriv f) ρ) :
    Tendsto (fun s => (s - ρ) * logDeriv f s) (𝓝[≠] ρ) (𝓝 1) := by
  have h_slope : Tendsto (slope f ρ) (𝓝[≠] ρ) (𝓝 f') :=
    hasDerivAt_iff_tendsto_slope.mp hf
  have h_slope_eq : (fun s => (f s - f ρ) / (s - ρ)) = slope f ρ := by
    ext s
    simp [slope, div_eq_inv_mul, smul_eq_mul]
  have h_slope2 : Tendsto (fun s => (f s - f ρ) / (s - ρ)) (𝓝[≠] ρ) (𝓝 f') := by
    rw [h_slope_eq]
    exact h_slope
  have h_slope3 : Tendsto (fun s => f s / (s - ρ)) (𝓝[≠] ρ) (𝓝 f') := by
    simpa [hf0] using h_slope2
  have h_inv : Tendsto (fun s => (s - ρ) / f s) (𝓝[≠] ρ) (𝓝 f'⁻¹) := by
    have h1 := h_slope3.inv₀ hf'0
    simpa [inv_div] using h1
  have h_deriv : Tendsto (deriv f) (𝓝[≠] ρ) (𝓝 (deriv f ρ)) :=
    hcont.mono_left nhdsWithin_le_nhds
  have h_deriv_eq : deriv f ρ = f' := hf.deriv
  rw [h_deriv_eq] at h_deriv
  have h_mul := h_inv.mul h_deriv
  have h_one : f'⁻¹ * f' = 1 := inv_mul_cancel₀ hf'0
  rw [h_one] at h_mul
  refine h_mul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  dsimp [logDeriv]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- At a certified simple zeta zero `ρ ≠ 1`, `ζ'/ζ` has residue `+1`. -/
theorem logDeriv_riemannZeta_residue_simpleZero
    {ρ : ℂ}
    (hρ : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0)
    (hsimple : deriv riemannZeta ρ ≠ 0) :
    Tendsto
      (fun s : ℂ => (s - ρ) * logDeriv riemannZeta s)
      (𝓝[≠] ρ)
      (𝓝 (1 : ℂ)) := by
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hana : AnalyticOn ℂ riemannZeta {s : ℂ | s ≠ 1} := hdiff.analyticOn hopen
  have hana_ρ : AnalyticAt ℂ riemannZeta ρ := hana.analyticAt (hopen.mem_nhds hρ)
  have hcont : ContinuousAt (deriv riemannZeta) ρ := (hana_ρ.deriv).continuousAt
  have hf_deriv : HasDerivAt riemannZeta (deriv riemannZeta ρ) ρ := (differentiableAt_riemannZeta hρ).hasDerivAt
  exact tendsto_mul_logDeriv_of_hasDerivAt_of_continuousAt hf_deriv hzero hsimple hcont

/-- At a certified simple zeta zero, the arithmetic connection `-ζ'/ζ`
has residue `-1`. -/
theorem neg_logDeriv_riemannZeta_residue_simpleZero
    {ρ : ℂ}
    (hρ : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0)
    (hsimple : deriv riemannZeta ρ ≠ 0) :
    Tendsto
      (fun s : ℂ => (s - ρ) * (-logDeriv riemannZeta s))
      (𝓝[≠] ρ)
      (𝓝 (-1 : ℂ)) := by
  have h :=
    (logDeriv_riemannZeta_residue_simpleZero
      hρ hzero hsimple).neg
  simpa [mul_neg] using h

/-! ## 5. Native meromorphic order and local Laurent normal form -/

/-- A certified finite-order divisor point of a meromorphic function. -/
structure DivisorPoint (f : ℂ → ℂ) (a : ℂ) where
  order : ℤ
  meromorphicAt : MeromorphicAt f a
  order_eq :
    meromorphicOrderAt f a = (order : WithTop ℤ)

namespace DivisorPoint

variable {f : ℂ → ℂ} {a : ℂ}

/-- Native local normal form
`f(z) = (z-a)^m g(z)` with `g(a) ≠ 0`. -/
theorem exists_local_factor
    (D : DivisorPoint f a) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g a ∧
      g a ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] a,
        f z = (z - a) ^ D.order * g z := by
  rcases
      (meromorphicOrderAt_eq_int_iff D.meromorphicAt).mp D.order_eq
    with ⟨g, hg, hgne, heq⟩
  refine ⟨g, hg, hgne, ?_⟩
  filter_upwards [heq] with z hz
  simpa [smul_eq_mul] using hz

end DivisorPoint

/-! ## 6. Formal Laurent principal terms -/

/-- A single formal Laurent term `c X⁻¹`. -/
def simpleLaurentPrincipalTerm (c : ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-1 : ℤ) c

/-- Principal term of `d log f` at a divisor point of order `m`. -/
def logDerivPrincipalTerm (m : ℤ) : LaurentSeries ℂ :=
  simpleLaurentPrincipalTerm (m : ℂ)

/-- Principal term of `-d log f`. -/
def negLogDerivPrincipalTerm (m : ℤ) : LaurentSeries ℂ :=
  simpleLaurentPrincipalTerm (-(m : ℂ))

@[simp]
theorem logDerivPrincipalTerm_coeff_neg_one (m : ℤ) :
    (logDerivPrincipalTerm m).coeff (-1) = (m : ℂ) := by
  simp [logDerivPrincipalTerm, simpleLaurentPrincipalTerm]

@[simp]
theorem negLogDerivPrincipalTerm_coeff_neg_one (m : ℤ) :
    (negLogDerivPrincipalTerm m).coeff (-1) = -(m : ℂ) := by
  simp [negLogDerivPrincipalTerm, simpleLaurentPrincipalTerm]

/-- Raw zeta has principal Laurent pole term `X⁻¹` at `s = 1`. -/
def riemannZetaPolePrincipalTerm : LaurentSeries ℂ :=
  simpleLaurentPrincipalTerm 1

/-- The arithmetic connection `-ζ'/ζ` has pole principal term `X⁻¹`
at `s = 1`. -/
def negLogDerivZetaPolePrincipalTerm : LaurentSeries ℂ :=
  simpleLaurentPrincipalTerm 1

/-! ## 7. Monodromy and de Rham period readout -/

/-- Additive logarithmic monodromy attached to divisor order `m`. -/
def divisorMonodromy (m : ℤ) : ℂ :=
  logarithmicPhase m

/-- Principal de Rham period around a divisor point in local coordinate
`w = z-a`. -/
def principalDeRhamPeriod (m : ℤ) (R : ℝ) : ℂ :=
  (m : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z)

/-- The local period is exactly `2πi` times the divisor order. -/
theorem principalDeRhamPeriod_eq_monodromy
    (m : ℤ) (R : ℝ) (hR : 0 < R) :
    principalDeRhamPeriod m R = divisorMonodromy m := by
  exact deRhamClass_of_winding R hR m

/-- Exponentiated holonomy closes because divisor orders are integral. -/
theorem exp_divisorMonodromy_eq_one (m : ℤ) :
    Complex.exp (divisorMonodromy m) = 1 := by
  exact holonomyPhase_is_root_of_unity m

end InfoGeometry.Arithmetic.ZetaEulerLaurentMonodromy
