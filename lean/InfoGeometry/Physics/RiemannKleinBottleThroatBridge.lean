import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Algebraic Riemann-parameter reflection

This module proves algebraic consequences of `s ↦ 1-s`: critical-strip invariance,
reflection symmetry of the polynomial `s(1-s)`, and conjugation identities on the
critical line. On real coordinates the map is `(σ,t) ↦ (1-σ,-t)`; its linear
part is `-I` and has determinant `+1`. Thus it is an orientation-preserving
half-turn, not an orientation-reversing glide and not a Klein-bottle construction.

The polynomial `s(1-s)` is formalized only as a polynomial: no Laplace operator,
Iwasawa root datum, or spectral realization is defined here. The scalar
cancellation identities do not establish a weak-value singularity or a theorem
about zeta zeros.
-/

open Complex

noncomputable section

namespace InfoGeometry.Physics.RiemannParameterReflection

/-! ## 1. Critical Strip & Functional Involution -/

/-- Critical strip condition: $0 \le \operatorname{Re}(s) \le 1$. -/
def inCriticalStrip (s : ℂ) : Prop :=
  0 ≤ s.re ∧ s.re ≤ 1

/-- Functional involution $s \mapsto 1 - s$. -/
def functionalInvolution (s : ℂ) : ℂ :=
  1 - s

/-- 🏆 THEOREM: The functional involution is an involution: $\mathcal{I}^2 = \mathrm{id}$. -/
theorem involution_involutive (s : ℂ) :
    functionalInvolution (functionalInvolution s) = s := by
  dsimp [functionalInvolution]
  ring

/-- 🏆 THEOREM: The functional involution preserves the critical strip. -/
theorem involution_preserves_strip (s : ℂ) (hs : inCriticalStrip s) :
    inCriticalStrip (functionalInvolution s) := by
  dsimp [inCriticalStrip, functionalInvolution] at *
  constructor
  · simp; linarith [hs.2]
  · simp; linarith [hs.1]

/-! ## 2. Plane action of the functional reflection -/

/- The affine coordinate action is a half-turn about `(1/2, 0)`. -/
def functionalReflectionPlane (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - p.1, -p.2)

/-- The coordinate reflection is involutive. -/
theorem functionalReflectionPlane_involutive (p : ℝ × ℝ) :
    functionalReflectionPlane (functionalReflectionPlane p) = p := by
  dsimp [functionalReflectionPlane]
  ext <;> ring

/-- The linear part of the coordinate reflection is `-I₂`. -/
def functionalReflectionLinear : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(-1 : ℝ), 0; 0, -1]

/-- The positive determinant confirms preservation of plane orientation. -/
theorem functionalReflectionLinear_det : Matrix.det functionalReflectionLinear = 1 := by
  simp [functionalReflectionLinear, Matrix.det_fin_two]

/-- 🏆 THEOREM: Fixed locus of spatial reflection $\sigma \mapsto 1 - \sigma$ is the unique midline $\sigma = 1/2$. -/
theorem spatial_reflection_fixed_iff (σ : ℝ) :
    1 - σ = σ ↔ σ = 1 / 2 := by
  constructor
  · intro h; linarith
  · intro h; linarith

/-- 🏆 THEOREM: The critical line $s = 1/2 + it$ is invariant under the functional involution:
    $\mathcal{I}(1/2 + it) = 1/2 - it$. -/
theorem critical_line_functional_involution (t : ℝ) :
    functionalInvolution (1 / 2 + (t : ℂ) * Complex.I) = 1 / 2 - (t : ℂ) * Complex.I := by
  dsimp [functionalInvolution]
  ring

/-- 🏆 THEOREM: Real part of the functional involution on the critical line remains $1/2$. -/
theorem critical_line_re_invariant (t : ℝ) :
    (functionalInvolution (1 / 2 + (t : ℂ) * Complex.I)).re = 1 / 2 := by
  rw [critical_line_functional_involution]
  simp

/-! ## 3. Reflection-invariant polynomial -/

/-- Fixed real coordinate of the map `σ ↦ 1-σ`. -/
def reflectionCenter : ℝ := 1 / 2

/-- The quadratic polynomial `s(1-s)`, with no spectral-operator interpretation. -/
def reflectionPolynomial (s : ℂ) : ℂ :=
  s * (1 - s)

/-- The polynomial is invariant under `s ↦ 1-s`. -/
theorem reflectionPolynomial_invariant (s : ℂ) :
    reflectionPolynomial (functionalInvolution s) = reflectionPolynomial s := by
  dsimp [reflectionPolynomial, functionalInvolution]
  ring

/-- On the critical line the polynomial has real value `1/4+t²`. -/
theorem reflectionPolynomial_on_critical_line (t : ℝ) :
    reflectionPolynomial (1 / 2 + (t : ℂ) * Complex.I) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  dsimp [reflectionPolynomial]
  rw [sq]
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- Imaginary part of the polynomial at `σ+it`:
    $\operatorname{Im}(s(1 - s)) = t(1 - 2\sigma)$ for $s = \sigma + it$. -/
theorem reflectionPolynomial_im_formula (σ t : ℝ) :
    (reflectionPolynomial ((σ : ℂ) + (t : ℂ) * Complex.I)).im = t * (1 - 2 * σ) := by
  dsimp [reflectionPolynomial]
  simp
  ring

/-- For nonzero `t`, the polynomial at `σ+it` is real exactly when `σ=1/2`. -/
theorem reflectionPolynomial_is_real_iff (σ t : ℝ) (ht : t ≠ 0) :
    (reflectionPolynomial ((σ : ℂ) + (t : ℂ) * Complex.I)).im = 0 ↔ σ = 1 / 2 := by
  rw [reflectionPolynomial_im_formula]
  constructor
  · intro h
    have h1 : 1 - 2 * σ = 0 := by
      cases mul_eq_zero.mp h with
      | inl h_t => exact False.elim (ht h_t)
      | inr h_fac => exact h_fac
    linarith
  · intro h
    rw [h]
    linarith

/-- The real polynomial value on the critical line is at least `1/4`. -/
theorem reflectionPolynomial_critical_ge_quarter (t : ℝ) :
    (1 / 4 : ℝ) ≤ 1 / 4 + t ^ 2 := by
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  linarith

/-- The polynomial at the reflection center is the square of that center. -/
theorem reflectionPolynomial_at_center :
    reflectionPolynomial (reflectionCenter : ℂ) = ((reflectionCenter ^ 2 : ℝ) : ℂ) := by
  dsimp [reflectionPolynomial, reflectionCenter]
  norm_num

/-! ## 4. Complex conjugation on the critical line -/

/-- 🏆 THEOREM: Complex conjugate of $1/2 + it$ is $1/2 - it$. -/
theorem star_critical_line (t : ℝ) :
    star (1 / 2 + (t : ℂ) * Complex.I) = 1 / 2 - (t : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- 🏆 THEOREM: On the critical line, functional involution matches complex conjugation:
    $\mathcal{I}(1/2 + it) = (1/2 + it)^*$. -/
theorem functional_involution_eq_star_on_critical_line (t : ℝ) :
    functionalInvolution (1 / 2 + (t : ℂ) * Complex.I) = star (1 / 2 + (t : ℂ) * Complex.I) := by
  rw [critical_line_functional_involution, star_critical_line]

/-- A nonzero complex number divided by its conjugate has unit modulus. -/
theorem quotient_by_conjugate_unit_modulus {z : ℂ} (hz : z ≠ 0) :
    ‖z / star z‖ = 1 := by
  rw [norm_div, norm_star, div_self]
  exact norm_ne_zero_iff.mpr hz

/-- 🏆 THEOREM: Reality of self-dual functions on the critical line:
    If $f$ satisfies the functional equation $f(1 - s) = f(s)$ and Schwarz reflection $f(s^*) = (f(s))^*$,
    then $f(1/2 + it)$ is self-conjugate (strictly real): $f(1/2 + it) = (f(1/2 + it))^*$. -/
theorem self_dual_critical_real (f : ℂ → ℂ)
    (h_func : ∀ s, f (1 - s) = f s)
    (h_star : ∀ s, f (star s) = star (f s)) (t : ℝ) :
    f (1 / 2 + (t : ℂ) * Complex.I) = star (f (1 / 2 + (t : ℂ) * Complex.I)) := by
  have h1 : f (1 / 2 + (t : ℂ) * Complex.I) = f (1 - (1 / 2 + (t : ℂ) * Complex.I)) := (h_func _).symm
  have h2 : 1 - (1 / 2 + (t : ℂ) * Complex.I) = star (1 / 2 + (t : ℂ) * Complex.I) := by
    change functionalInvolution _ = star _
    rw [functional_involution_eq_star_on_critical_line]
  rw [h2, h_star] at h1
  exact h1

/-- 🏆 THEOREM: Modulus equality on the critical line for any self-dual function:
    $\|f(1/2 + it)\| = \|f(1 - (1/2 + it))\|$. -/
theorem self_dual_modulus_eq (f : ℂ → ℂ) (h_func : ∀ s, f (1 - s) = f s) (t : ℝ) :
    ‖f (1 / 2 + (t : ℂ) * Complex.I)‖ = ‖f (functionalInvolution (1 / 2 + (t : ℂ) * Complex.I))‖ := by
  dsimp [functionalInvolution]
  rw [h_func]

/-! ## 5. Scalar cancellation identities -/

/-- If two complex scalars sum to zero, they have equal norm. -/
theorem destructive_interference_equal_modulus (psi phi : ℂ) (h : psi + phi = 0) :
    ‖psi‖ = ‖phi‖ := by
  have hphi : phi = -psi := eq_neg_of_add_eq_zero_right h
  rw [hphi, norm_neg]

/-- Under scalar cancellation, the conjugate product is the negative squared norm. -/
theorem destructive_overlap_annihilation (psi phi : ℂ) (h : psi + phi = 0) :
    star phi * psi = - ((‖psi‖ ^ 2 : ℝ) : ℂ) := by
  have hphi : phi = -psi := eq_neg_of_add_eq_zero_right h
  rw [hphi, star_neg, neg_mul]
  have h_prod : star psi * psi = ((‖psi‖ ^ 2 : ℝ) : ℂ) := by
    have h_normSq : (Complex.normSq psi : ℂ) = star psi * psi := normSq_eq_conj_mul_self
    rw [← h_normSq, Complex.normSq_eq_norm_sq]
  rw [h_prod]

end InfoGeometry.Physics.RiemannParameterReflection
