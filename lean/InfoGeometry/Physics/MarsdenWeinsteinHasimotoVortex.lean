/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Finite Hasimoto Identities and Cross-Product Algebra

The historical overview below records the motivating formulas, but the formal
content in this file is narrower: it proves finite-dimensional cross-product
identities, complex scalar identities, and facts about finite weighted sums.
It does not formalize a Frenet curve, LIA or NLS dynamics, a
Marsden–Weinstein quotient, or vortex-ring dynamics. Differential statements
are made only for explicitly differentiable paths.

The remaining list is historical motivation only; the listed physical bridges
are not formalized in this module:
1. **Frenet–Serret Triad & Vector Kinematics**:
   - The unit tangent $\\mathbf{t}$, normal $\\mathbf{n}$, and binormal $\\mathbf{b} = \\mathbf{t} \\times \\mathbf{n}$.
   - The Local Induction Approximation (LIA / Da Rios–Betchov): $\\dot{\\mathbf{X}} = \\kappa \\mathbf{b}$.
   - Equivalence with the continuous Heisenberg spin chain on the 2-sphere $S^2$:
     $$\\dot{\\mathbf{t}} = \\mathbf{t} \\times \\mathbf{t}'' = \\kappa' \\mathbf{b} - \\kappa \\tau \\mathbf{n}$$
2. **Hasimoto Transformation**:
   - The complex wave function $\\psi(s) = \\kappa \\exp(i \\theta(s))$ mapping vortex filament geometry
     to the 1D cubic non-linear Schr\"odinger (NLS) equation.
   - Soliton density: $|\\psi|^2 = \\kappa^2$.
   - Quantum current / helicity density: $\\operatorname{Im}(\\psi^* \\psi') = \\kappa^2 \\tau$.
3. **Discrete Integrable Invariant Hierarchy**:
   - Soliton charge / Vortex length $N = \\sum w_i \\kappa_i^2 \\ge 0$.
   - Total Helicity / Momentum $P = \\sum w_i \\kappa_i^2 \\tau_i$, vanishing on planar curves ($\tau_i = 0$).
   - NLS Filament Energy $H = \\sum w_i ((\\kappa'_i)^2 + \\kappa_i^2 \\tau_i^2 - \\frac{1}{2} \\kappa_i^4)$.
4. **Marsden–Weinstein Symplectic Reduction on $S^2 \\cong \\mathrm{SU}(2) / \\mathrm{U}(1)$**:
   - Kirillov–Kostant–Souriau symplectic 2-form $\\omega_{S^2}(\\mathbf{u}, \\mathbf{v}) = \\mathbf{t} \\cdot (\\mathbf{u} \\times \\mathbf{v})$.
   - Skew-symmetry, alternating property, and radial gauge annihilation.
5. **Stationary Vortex Smoke Rings**:
   - Constant curvature $\\kappa = 1/R$, zero torsion $\\tau = 0$.
   - Translational drift velocity $v_{\\mathrm{drift}} = 1/R > 0$ and dispersion $\\omega_0 = 1/(2R^2) > 0$.
-/

namespace InfoGeometry.Physics.HasimotoVortex

open Matrix Complex
open scoped ComplexConjugate

noncomputable section

/-! ### Part I: Frenet–Serret Triad and Vector Cross Kinematics -/

/-- Bilinearity of the cross product, under the explicit identity `t × n = b`. -/
theorem crossFrame_scaled_normal (t n b : Fin 3 → ℝ)
    (hcross : t ⨯₃ n = b) (kappa : ℝ) :
    t ⨯₃ (kappa • n) = kappa • b := by
  rw [LinearMap.map_smul, hcross]

/-- An algebraic vector assembled from the three vectors and scalar
coefficients; this is not defined as a second derivative. -/
def crossExpansionVector (t n b : Fin 3 → ℝ) (kappa kappa_prime tau : ℝ) : Fin 3 → ℝ :=
  (- (kappa ^ 2)) • t + kappa_prime • n + (kappa * tau) • b

/-- An algebraic vector traditionally used as the right-hand side of a tangent
evolution equation; this definition contains no trajectory or derivative. -/
def crossExpansionResult (n b : Fin 3 → ℝ) (kappa_prime kappa tau : ℝ) : Fin 3 → ℝ :=
  kappa_prime • b - (kappa * tau) • n

/-- Cross-product expansion using the three explicit frame identities.  This
is a finite algebraic identity, not a dynamical equivalence. -/
theorem cross_expansion_identity (t n b : Fin 3 → ℝ)
    (htn : t ⨯₃ n = b) (htb : t ⨯₃ b = -n) (htt : t ⨯₃ t = 0)
    (kappa kappa_prime tau : ℝ) :
    t ⨯₃ crossExpansionVector t n b kappa kappa_prime tau =
      crossExpansionResult n b kappa_prime kappa tau := by
  unfold crossExpansionVector crossExpansionResult
  have h1 : t ⨯₃ ((- (kappa ^ 2)) • t) = 0 := by
    rw [LinearMap.map_smul, htt, smul_zero]
  have h2 : t ⨯₃ (kappa_prime • n) = kappa_prime • b := by
    rw [LinearMap.map_smul, htn]
  have h3 : t ⨯₃ ((kappa * tau) • b) = - ((kappa * tau) • n) := by
    rw [LinearMap.map_smul, htb, smul_neg]
  rw [LinearMap.map_add, LinearMap.map_add]
  rw [h1, h2, h3, zero_add, sub_eq_add_neg]

/-! ### Part II: Hasimoto Complex Transformation -/

/-- Hasimoto complex wave function envelope:
    $$\\psi(s) = \\kappa \\exp(i \\theta(s))$$ -/
def hasimotoWave (kappa theta : ℝ) : ℂ :=
  (kappa : ℂ) * exp (theta * I)

/-- Amplitude-phase path used for the differentiability theorem below. -/
def hasimotoPath (kappa theta : ℝ → ℝ) (s : ℝ) : ℂ :=
  (kappa s : ℂ) * exp ((theta s : ℂ) * I)

/-- The usual pointwise expression for the Hasimoto derivative.  Its
interpretation as a derivative is supplied by `hasDerivAt_hasimotoPath_eq_jet`.
-/
def hasimotoDeriv (kappa kappa_prime tau theta : ℝ) : ℂ :=
  ((kappa_prime : ℂ) + I * ((kappa * tau : ℝ) : ℂ)) * exp (theta * I)

/-- The derivative of an amplitude-phase path, from derivatives of its real
amplitude and phase at the point. -/
theorem hasDerivAt_hasimotoPath
    (kappa theta : ℝ → ℝ) (s kappa' theta' : ℝ)
    (hκ : HasDerivAt kappa kappa' s) (hθ : HasDerivAt theta theta' s) :
    HasDerivAt (hasimotoPath kappa theta)
      ((kappa' : ℂ) * exp ((theta s : ℂ) * I) +
        (kappa s : ℂ) * (exp ((theta s : ℂ) * I) * ((theta' : ℂ) * I))) s := by
  have hκc : HasDerivAt (fun x : ℝ => (kappa x : ℂ)) (kappa' : ℂ) s :=
    hκ.ofReal_comp
  have hθc : HasDerivAt (fun x : ℝ => (theta x : ℂ)) (theta' : ℂ) s :=
    hθ.ofReal_comp
  have harg : HasDerivAt (fun x : ℝ => (theta x : ℂ) * I) ((theta' : ℂ) * I) s :=
    hθc.mul_const I
  have hexp : HasDerivAt (fun x : ℝ => exp ((theta x : ℂ) * I))
      (exp ((theta s : ℂ) * I) * ((theta' : ℂ) * I)) s := by
    exact (Complex.hasDerivAt_exp _).comp s harg
  have hprod := hκc.mul hexp
  simpa [hasimotoPath] using hprod

/-- The product-rule derivative is the Hasimoto jet when the phase derivative
is denoted by `tau`. -/
theorem hasDerivAt_hasimotoPath_eq_jet
    (kappa theta : ℝ → ℝ) (s kappa' tau : ℝ)
    (hκ : HasDerivAt kappa kappa' s) (hθ : HasDerivAt theta tau s) :
    HasDerivAt (hasimotoPath kappa theta)
      (hasimotoDeriv (kappa s) kappa' tau (theta s)) s := by
  have h := hasDerivAt_hasimotoPath kappa theta s kappa' tau hκ hθ
  apply h.congr_deriv
  unfold hasimotoDeriv
  rw [Complex.ofReal_mul]
  ring

/-- **Theorem 3 (Unit Modulus of Complex Phase Factor)**:
    $\\operatorname{normSq}(\\exp(i x)) = 1$. -/
theorem normSq_exp_ofReal_mul_I (x : ℝ) : normSq (exp (x * I)) = 1 := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, normSq_add_mul_I]
  exact Real.cos_sq_add_sin_sq x

/-- **Theorem 4 (Hasimoto Soliton Probability Density)**:
    The squared modulus of the Hasimoto wave function is identically the squared curvature:
    $$|\\psi|^2 = \\kappa^2$$ -/
theorem hasimoto_normSq (kappa theta : ℝ) :
    normSq (hasimotoWave kappa theta) = kappa ^ 2 := by
  unfold hasimotoWave
  rw [map_mul, normSq_ofReal, normSq_exp_ofReal_mul_I, mul_one, sq]

/-- Complex conjugate of the phase factor: $\\operatorname{conj}(\\exp(i x)) = \\exp(-i x)$. -/
theorem conj_exp_ofReal_mul_I (x : ℝ) : conj (exp (x * I)) = exp (- (x * I)) := by
  rw [exp_mul_I, map_add, map_mul, conj_I, ← ofReal_cos, ← ofReal_sin, conj_ofReal, conj_ofReal]
  rw [show - (x * I) = (- (x : ℂ)) * I by ring, exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg, ofReal_cos, ofReal_sin]
  ring

/-- **Theorem 5 (Hasimoto Wave-Deriv Product Factorization)**:
    $$\\psi^* \\psi' = \\kappa \\kappa' + i \\kappa^2 \\tau$$ -/
theorem hasimoto_conj_mul_deriv (kappa kappa_prime tau theta : ℝ) :
    conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta =
      ((kappa * kappa_prime : ℝ) : ℂ) + I * ((kappa ^ 2 * tau : ℝ) : ℂ) := by
  unfold hasimotoWave hasimotoDeriv
  rw [map_mul, conj_ofReal, conj_exp_ofReal_mul_I]
  have h_exp : exp (- (theta * I)) * (((kappa_prime : ℂ) + I * ((kappa * tau : ℝ) : ℂ)) * exp (theta * I)) =
      ((kappa_prime : ℂ) + I * ((kappa * tau : ℝ) : ℂ)) * (exp (- (theta * I)) * exp (theta * I)) := by
    ring
  rw [mul_assoc (kappa : ℂ), h_exp]
  have h_cancel : exp (- (theta * I)) * exp (theta * I) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  rw [h_cancel, mul_one]
  apply Complex.ext
  · simp only [mul_re, add_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, sub_zero, zero_mul]
    ring
  · simp only [mul_im, add_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, mul_zero]
    ring

/-- The conjugate-amplitude product for an actual differentiable
amplitude-phase path. -/
theorem hasimotoPath_conj_mul_deriv
    (kappa theta : ℝ → ℝ) (s kappa' tau : ℝ)
    (hκ : HasDerivAt kappa kappa' s) (hθ : HasDerivAt theta tau s) :
    conj (hasimotoPath kappa theta s) * deriv (hasimotoPath kappa theta) s =
      ((kappa s * kappa' : ℝ) : ℂ) + I * ((kappa s ^ 2 * tau : ℝ) : ℂ) := by
  have hderiv := (hasDerivAt_hasimotoPath_eq_jet kappa theta s kappa' tau hκ hθ).deriv
  rw [hderiv]
  simpa [hasimotoPath, hasimotoWave] using
    hasimoto_conj_mul_deriv (kappa s) kappa' tau (theta s)

/-- Imaginary part of the pointwise Hasimoto jet product.  Its path-derivative
interpretation is proved separately under differentiability hypotheses. -/
theorem hasimoto_helicity_density (kappa kappa_prime tau theta : ℝ) :
    (conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).im =
      kappa ^ 2 * tau := by
  rw [hasimoto_conj_mul_deriv]
  simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero]
  ring

/-- Real part of the pointwise Hasimoto jet product. -/
theorem hasimoto_jet_real_part (kappa kappa_prime tau theta : ℝ) :
    (conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).re =
      kappa * kappa_prime := by
  rw [hasimoto_conj_mul_deriv]
  simp only [add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, sub_zero, zero_mul]
  ring

/-! ### Part III: Finite Weighted Sums -/

/-- A finite weighted sum of squares.  No continuum length or NLS invariant is
asserted by this definition. -/
def filamentLength {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, w i * kappa i ^ 2

/-- **Theorem 8 (Non-Negativity of Filament Length)**:
    $N \\ge 0$ whenever segment weights $w_i \\ge 0$. -/
theorem filamentLength_nonneg {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    0 ≤ filamentLength w kappa := by
  unfold filamentLength
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hw i) (sq_nonneg _)

/-- A finite weighted sum of curvature-square/torsion-shaped scalars. -/
def filamentHelicity {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ) (tau : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, w i * (kappa i ^ 2 * tau i)

/-- **Theorem 9 (Helicity Vanishing on Planar Vortex Filaments)**:
    Planar filaments ($\\tau_i = 0$) carry identically zero total helicity. -/
theorem filamentHelicity_zero_of_planar {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ) (tau : Fin k → ℝ)
    (h_planar : ∀ i, tau i = 0) :
    filamentHelicity w kappa tau = 0 := by
  unfold filamentHelicity
  simp [h_planar]

/-! ### Part IV: Cross Triple Product -/

/-- The scalar triple product `t · (u × v)` on three real coordinate vectors.
No manifold or symplectic reduction is defined here. -/
def crossTripleProduct (t u v : Fin 3 → ℝ) : ℝ :=
  t ⬝ᵥ (u ⨯₃ v)

/-- Swapping the last two inputs of the scalar triple product changes sign. -/
theorem crossTripleProduct_skew (t u v : Fin 3 → ℝ) :
    crossTripleProduct t v u = - crossTripleProduct t u v := by
  unfold crossTripleProduct
  rw [← cross_anticomm, dotProduct_neg]

/-- The scalar triple product vanishes when its last two inputs agree. -/
theorem crossTripleProduct_self (t u : Fin 3 → ℝ) :
    crossTripleProduct t u u = 0 := by
  unfold crossTripleProduct
  rw [cross_self, dotProduct_zero]

/-- The triple product vanishes when the first two inputs agree. -/
theorem crossTripleProduct_first_cross_zero (t w : Fin 3 → ℝ) :
    crossTripleProduct t t w = 0 := by
  unfold crossTripleProduct
  exact dot_self_cross t w

end

end InfoGeometry.Physics.HasimotoVortex
