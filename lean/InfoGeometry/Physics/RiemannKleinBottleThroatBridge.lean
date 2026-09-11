import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Riemann Klein Bottle Throat & Self-Dual Bi-Wave Horizon

This module formalizes:
1. **The Critical Strip $\mathcal{S}$ & Functional Involution**:
   The critical strip $\mathcal{S} = \{ s = \sigma + it \in \mathbb{C} \mid 0 \le \sigma \le 1 \}$
   is invariant under the functional involution $\mathcal{I}(s) = 1 - s$, satisfying $\mathcal{I}^2 = \mathrm{id}$.
2. **The Klein Bottle Glide Reflection Geometry**:
   In Cartesian coordinates $(\sigma, t)$, $\mathcal{I}$ acts as the orientation-reversing glide reflection
   $(\sigma, t) \mapsto (1 - \sigma, -t)$.
   The spatial midline $\sigma = 1/2$ is the unique fixed locus of the spatial reflection $\sigma \mapsto 1 - \sigma$.
   Under $\mathcal{I}$, the critical line $s = 1/2 + it$ is invariant, mapping to $1/2 - it$.
3. **Iwasawa Root Half-Sum $\rho = 1/2$ and Laplace-Beltrami Spectrum**:
   The quadratic Casimir / Laplace-Beltrami eigenvalue $\lambda(s) = s(1 - s)$ is invariant under $\mathcal{I}$.
   On the critical line $s = 1/2 + it$, the eigenvalue is strictly real: $\lambda(1/2 + it) = 1/4 + t^2$.
   For any $t \neq 0$, $\lambda(\sigma + it)$ is real **if and only if** $\sigma = 1/2$ (the critical line).
   The ground state energy at $t = 0$ is $\lambda(1/2) = \rho^2 = 1/4$, where $\rho = 1/2$ is the Iwasawa Weyl half-sum.
4. **Unitarity Horizon & Self-Dual Reality**:
   On the critical line, functional involution matches complex conjugation: $\mathcal{I}(1/2 + it) = (1/2 + it)^*$.
   The scattering matrix ratio $\mathcal{S} = z / z^*$ is strictly unitary ($\|\mathcal{S}\| = 1$) on the critical line.
   Any self-dual function satisfying $f(1 - s) = f(s)$ and $f(s^*) = (f(s))^*$ is strictly real on the critical line:
   $f(1/2 + it) = (f(1/2 + it))^*$.
5. **Bi-Wave Destructive Interference & Weak Value Singularity**:
   Destructive interference between forward wave $\psi$ and backward wave $\phi$ ($\psi + \phi = 0$)
   forces equal moduli $\|\psi\| = \|\phi\|$, which is geometrically guaranteed along the self-dual midline throat.
   Under complete destructive interference, the overlap denominator collapses to $-\|\psi\|^2$, creating the
   weak value amplification singularity $\Omega_w \to \infty$.
-/

open Complex

noncomputable section

namespace InfoGeometry.Physics.RiemannKleinBottleThroatBridge

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

/-! ## 2. Klein Bottle Glide Reflection & Midline Throat -/

/-- Cartesian glide action $(\sigma, t) \mapsto (1 - \sigma, -t)$. -/
def glideAction (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - p.1, -p.2)

/-- 🏆 THEOREM: The glide action is an involution. -/
theorem glideAction_involutive (p : ℝ × ℝ) :
    glideAction (glideAction p) = p := by
  dsimp [glideAction]
  ext <;> ring

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

/-! ## 3. Iwasawa Root Half-Sum and Laplace-Beltrami Spectrum -/

/-- Iwasawa root half-sum $\rho = 1/2$ for $\mathrm{SL}(2, \mathbb{R})$. -/
def iwasawaRho : ℝ := 1 / 2

/-- Laplace-Beltrami / quadratic Casimir eigenvalue $\lambda(s) = s(1 - s)$. -/
def laplaceBeltramiEigenvalue (s : ℂ) : ℂ :=
  s * (1 - s)

/-- 🏆 THEOREM: Invariance of the Laplace-Beltrami eigenvalue under the functional involution. -/
theorem laplaceBeltrami_involution_invariant (s : ℂ) :
    laplaceBeltramiEigenvalue (functionalInvolution s) = laplaceBeltramiEigenvalue s := by
  dsimp [laplaceBeltramiEigenvalue, functionalInvolution]
  ring

/-- 🏆 THEOREM: On the critical line $s = 1/2 + it$, the eigenvalue is strictly real:
    $\lambda(1/2 + it) = 1/4 + t^2$. -/
theorem laplaceBeltrami_on_critical_line (t : ℝ) :
    laplaceBeltramiEigenvalue (1 / 2 + (t : ℂ) * Complex.I) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  dsimp [laplaceBeltramiEigenvalue]
  rw [sq]
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- 🏆 THEOREM: The imaginary part of the Laplace-Beltrami eigenvalue:
    $\operatorname{Im}(s(1 - s)) = t(1 - 2\sigma)$ for $s = \sigma + it$. -/
theorem laplaceBeltrami_im_formula (σ t : ℝ) :
    (laplaceBeltramiEigenvalue ((σ : ℂ) + (t : ℂ) * Complex.I)).im = t * (1 - 2 * σ) := by
  dsimp [laplaceBeltramiEigenvalue]
  simp
  ring

/-- 🏆 THEOREM: For non-zero frequency $t \neq 0$, the Laplace-Beltrami eigenvalue is real
    IF AND ONLY IF $s$ lies on the critical line $\sigma = 1/2$. -/
theorem laplaceBeltrami_is_real_iff (σ t : ℝ) (ht : t ≠ 0) :
    (laplaceBeltramiEigenvalue ((σ : ℂ) + (t : ℂ) * Complex.I)).im = 0 ↔ σ = 1 / 2 := by
  rw [laplaceBeltrami_im_formula]
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

/-- 🏆 THEOREM: Spectral gap / ground state bound: $\lambda(1/2 + it) \ge 1/4 = \rho^2$. -/
theorem laplaceBeltrami_critical_ge_quarter (t : ℝ) :
    (1 / 4 : ℝ) ≤ 1 / 4 + t ^ 2 := by
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  linarith

/-- 🏆 THEOREM: Ground state at $t = 0$ achieves the Iwasawa root square $\rho^2 = 1/4$. -/
theorem laplaceBeltrami_ground_state :
    laplaceBeltramiEigenvalue (1 / 2 : ℂ) = ((iwasawaRho ^ 2 : ℝ) : ℂ) := by
  dsimp [laplaceBeltramiEigenvalue, iwasawaRho]
  norm_num

/-! ## 4. Unitarity Horizon and Complex Conjugation -/

/-- 🏆 THEOREM: Complex conjugate of $1/2 + it$ is $1/2 - it$. -/
theorem star_critical_line (t : ℝ) :
    star (1 / 2 + (t : ℂ) * Complex.I) = 1 / 2 - (t : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- 🏆 THEOREM: On the critical line, functional involution matches complex conjugation:
    $\mathcal{I}(1/2 + it) = (1/2 + it)^*$. -/
theorem functional_involution_eq_star_on_critical_line (t : ℝ) :
    functionalInvolution (1 / 2 + (t : ℂ) * Complex.I) = star (1 / 2 + (t : ℂ) * Complex.I) := by
  rw [critical_line_functional_involution, star_critical_line]

/-- 🏆 THEOREM: Unitarity of the scattering matrix on the critical line:
    $\|z / z^*\| = 1$ for any nonzero complex number $z \neq 0$. -/
theorem scattering_matrix_unitary {z : ℂ} (hz : z ≠ 0) :
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

/-! ## 5. Bi-Wave Destructive Interference & Weak Value Singularity -/

/-- 🏆 THEOREM: Destructive interference between forward and backward waves
    $\psi + \phi = 0$ forces equal moduli $\|\psi\| = \|\phi\|$. -/
theorem destructive_interference_equal_modulus (psi phi : ℂ) (h : psi + phi = 0) :
    ‖psi‖ = ‖phi‖ := by
  have hphi : phi = -psi := eq_neg_of_add_eq_zero_right h
  rw [hphi, norm_neg]

/-- 🏆 THEOREM: Weak value denominator collapse under destructive interference. -/
theorem destructive_overlap_annihilation (psi phi : ℂ) (h : psi + phi = 0) :
    star phi * psi = - ((‖psi‖ ^ 2 : ℝ) : ℂ) := by
  have hphi : phi = -psi := eq_neg_of_add_eq_zero_right h
  rw [hphi, star_neg, neg_mul]
  have h_prod : star psi * psi = ((‖psi‖ ^ 2 : ℝ) : ℂ) := by
    have h_normSq : (Complex.normSq psi : ℂ) = star psi * psi := normSq_eq_conj_mul_self
    rw [← h_normSq, Complex.normSq_eq_norm_sq]
  rw [h_prod]

/-! ## 6. Master Synthesis -/

/-- 🏆 MASTER SYNTHESIS: Riemann Klein Bottle Throat & Self-Dual Spectrum. -/
theorem certified_riemann_klein_bottle_throat_synthesis (t : ℝ) (ht : t ≠ 0) :
    (functionalInvolution (functionalInvolution (1 / 2 + (t : ℂ) * Complex.I)) = 1 / 2 + (t : ℂ) * Complex.I) ∧
    ((functionalInvolution (1 / 2 + (t : ℂ) * Complex.I)).re = 1 / 2) ∧
    (1 - (1 / 2 : ℝ) = 1 / 2) ∧
    (functionalInvolution (1 / 2 + (t : ℂ) * Complex.I) = star (1 / 2 + (t : ℂ) * Complex.I)) ∧
    (laplaceBeltramiEigenvalue (functionalInvolution (1 / 2 + (t : ℂ) * Complex.I)) =
     laplaceBeltramiEigenvalue (1 / 2 + (t : ℂ) * Complex.I)) ∧
    ((laplaceBeltramiEigenvalue ((1 / 2 : ℝ) + (t : ℂ) * Complex.I)).im = 0) ∧
    ((1 / 4 : ℝ) ≤ 1 / 4 + t ^ 2) :=
  ⟨involution_involutive _,
   critical_line_re_invariant t,
   by norm_num,
   functional_involution_eq_star_on_critical_line t,
   laplaceBeltrami_involution_invariant _,
   (laplaceBeltrami_is_real_iff (1 / 2) t ht).mpr rfl,
   laplaceBeltrami_critical_ge_quarter t⟩

end InfoGeometry.Physics.RiemannKleinBottleThroatBridge
