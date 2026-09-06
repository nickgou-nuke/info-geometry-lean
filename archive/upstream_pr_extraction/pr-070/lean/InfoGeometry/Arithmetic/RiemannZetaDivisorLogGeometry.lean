import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Riemann zeta divisor and logarithmic geometry

Native local owner for the multiplicative Euler derivative, logarithmic-cover
coordinates, meromorphic zero/pole order, and the logarithmic derivative.

Contour periods, the argument principle, global Hadamard products, and any
Witten-index identification belong to downstream owners.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannZetaDivisorLogGeometry

open Filter
open scoped Topology

/-! ## Multiplicative Euler derivative -/

/-- The multiplicative derivative `x f'(x)`. -/
def eulerDerivReal (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * deriv f x

/-- Differentiation after `x = exp t` is the Euler derivative. -/
theorem deriv_exp_pullback
    (f : ℝ → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (Real.exp t)) :
    deriv (fun y : ℝ => f (Real.exp y)) t =
      eulerDerivReal f (Real.exp t) := by
  have hcomp := hf.hasDerivAt.comp t (Real.hasDerivAt_exp t)
  simpa [eulerDerivReal, mul_comm] using hcomp.deriv

/-- Exact form of `x d/dx = d/d(log x)` for positive real `x`. -/
theorem eulerDeriv_eq_deriv_logCoord
    (f : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hf : DifferentiableAt ℝ f x) :
    eulerDerivReal f x =
      deriv (fun y : ℝ => f (Real.exp y)) (Real.log x) := by
  symm
  have hf' : DifferentiableAt ℝ f (Real.exp (Real.log x)) := by
    simpa [Real.exp_log hx] using hf
  rw [deriv_exp_pullback f (Real.log x) hf']
  simp [eulerDerivReal, Real.exp_log hx]

/-! ## Centered logarithmic cover -/

/-- The centered Euler derivative `(s - a) f'(s)`. -/
def centeredEulerDeriv (a : ℂ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (s - a) * deriv f s

/-- Pullback through the local logarithmic cover `s = a + exp w`. -/
def logCoverPullback (a : ℂ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  f (a + Complex.exp w)

/-- On the logarithmic cover, differentiation is the centered Euler derivative. -/
theorem deriv_logCoverPullback
    (a : ℂ) (f : ℂ → ℂ) (w : ℂ)
    (hf : DifferentiableAt ℂ f (a + Complex.exp w)) :
    deriv (logCoverPullback a f) w =
      centeredEulerDeriv a f (a + Complex.exp w) := by
  have hinner : HasDerivAt
      (fun z : ℂ => a + Complex.exp z) (Complex.exp w) w := by
    convert (hasDerivAt_const w a).add (Complex.hasDerivAt_exp w) using 1 <;>
      simp
  have hcomp := hf.hasDerivAt.comp w hinner
  simpa [logCoverPullback, centeredEulerDeriv, mul_comm, mul_left_comm,
    mul_assoc] using hcomp.deriv

/-! ## Native divisor order and logarithmic derivative -/

/-- Native meromorphic zero/pole order, with `⊤` for the zero germ. -/
def divisorOrder (f : ℂ → ℂ) (a : ℂ) : WithTop ℤ :=
  meromorphicOrderAt f a

/-- The scalar coefficient of the logarithmic one-form `d log f`. -/
def dlogCoeff (f : ℂ → ℂ) : ℂ → ℂ :=
  logDeriv f

/-! ## Riemann-zeta specialization -/

/-- The logarithmic coefficient `ζ'/ζ`. -/
def zetaDlogCoeff : ℂ → ℂ :=
  dlogCoeff riemannZeta

/-- Native punctured-neighborhood normalization of the simple zeta pole at `1`. -/
theorem riemannZeta_simplePole_normalization :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
  riemannZeta_residue_one

end InfoGeometry.Arithmetic.RiemannZetaDivisorLogGeometry

end noncomputable section
