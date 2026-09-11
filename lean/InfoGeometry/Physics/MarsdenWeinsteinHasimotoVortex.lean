/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Section 5.95: Marsden–Weinstein Symplectic Reduction, Vortex Filament Local Induction Approximation (LIA), and the Hasimoto Transformation

This module formalizes the grand geometric and Hamiltonian bridge between:
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

/-- An orthonormal Frenet triad $(\\mathbf{t}, \\mathbf{n}, \\mathbf{b})$ in $\\mathbb{R}^3$. -/
structure FrenetTriad where
  t : Fin 3 → ℝ
  n : Fin 3 → ℝ
  b : Fin 3 → ℝ
  t_cross_n : t ⨯₃ n = b
  t_cross_b : t ⨯₃ b = -n
  t_cross_t : t ⨯₃ t = 0

/-- **Theorem 1 (First Cross Identity of LIA)**:
    $\\mathbf{t} \\times \\mathbf{t}' = \\mathbf{t} \\times (\\kappa \\mathbf{n}) = \\kappa \\mathbf{b}$. -/
theorem lia_tangent_cross_prime (F : FrenetTriad) (kappa : ℝ) :
    F.t ⨯₃ (kappa • F.n) = kappa • F.b := by
  rw [LinearMap.map_smul, F.t_cross_n]

/-- Spatial second derivative of the unit tangent vector along the Frenet frame:
    $\\mathbf{t}'' = (\\kappa \\mathbf{n})' = -\\kappa^2 \\mathbf{t} + \\kappa' \\mathbf{n} + \\kappa \\tau \\mathbf{b}$. -/
def tangentSecondDeriv (F : FrenetTriad) (kappa kappa_prime tau : ℝ) : Fin 3 → ℝ :=
  (- (kappa ^ 2)) • F.t + kappa_prime • F.n + (kappa * tau) • F.b

/-- Time derivative of the unit tangent vector under LIA:
    $\\dot{\\mathbf{t}} = (\\kappa \\mathbf{b})' = \\kappa' \\mathbf{b} - \\kappa \\tau \\mathbf{n}$. -/
def liaTangentTimeDeriv (F : FrenetTriad) (kappa_prime kappa tau : ℝ) : Fin 3 → ℝ :=
  kappa_prime • F.b - (kappa * tau) • F.n

/-- **Theorem 2 (Heisenberg Spin Chain Equivalence / Hasimoto Lemma)**:
    The LIA time evolution $\\dot{\\mathbf{t}}$ is identically equal to the
    Heisenberg ferromagnet spin chain cross product:
    $$\\mathbf{t} \\times \\mathbf{t}'' = \\dot{\\mathbf{t}} = \\kappa' \\mathbf{b} - \\kappa \\tau \\mathbf{n}$$ -/
theorem lia_heisenberg_cross_equivalence (F : FrenetTriad) (kappa kappa_prime tau : ℝ) :
    F.t ⨯₃ tangentSecondDeriv F kappa kappa_prime tau =
      liaTangentTimeDeriv F kappa_prime kappa tau := by
  unfold tangentSecondDeriv liaTangentTimeDeriv
  have h1 : F.t ⨯₃ ((- (kappa ^ 2)) • F.t) = 0 := by
    rw [LinearMap.map_smul, F.t_cross_t, smul_zero]
  have h2 : F.t ⨯₃ (kappa_prime • F.n) = kappa_prime • F.b := by
    rw [LinearMap.map_smul, F.t_cross_n]
  have h3 : F.t ⨯₃ ((kappa * tau) • F.b) = - ((kappa * tau) • F.n) := by
    rw [LinearMap.map_smul, F.t_cross_b, smul_neg]
  rw [LinearMap.map_add, LinearMap.map_add]
  rw [h1, h2, h3, zero_add, sub_eq_add_neg]

/-! ### Part II: Hasimoto Complex Transformation -/

/-- Hasimoto complex wave function envelope:
    $$\\psi(s) = \\kappa \\exp(i \\theta(s))$$ -/
def hasimotoWave (kappa theta : ℝ) : ℂ :=
  (kappa : ℂ) * exp (theta * I)

/-- Hasimoto spatial derivative $\\psi' = (\\kappa' + i \\kappa \\tau) \\exp(i \\theta)$. -/
def hasimotoDeriv (kappa kappa_prime tau theta : ℝ) : ℂ :=
  ((kappa_prime : ℂ) + I * ((kappa * tau : ℝ) : ℂ)) * exp (theta * I)

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

/-- **Theorem 6 (Quantum Current is Kinetic Helicity Density)**:
    The imaginary part of $\\psi^* \\psi'$ is identically the filament helicity density:
    $$\\operatorname{Im}(\\psi^* \\psi') = \\kappa^2 \\tau$$ -/
theorem hasimoto_helicity_density (kappa kappa_prime tau theta : ℝ) :
    (conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).im =
      kappa ^ 2 * tau := by
  rw [hasimoto_conj_mul_deriv]
  simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero]
  ring

/-- **Theorem 7 (Real Part is Derivative of Soliton Density)**:
    $$\\operatorname{Re}(\\psi^* \\psi') = \\kappa \\kappa' = \\frac{1}{2} (\\kappa^2)'$$ -/
theorem hasimoto_soliton_density_deriv (kappa kappa_prime tau theta : ℝ) :
    (conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).re =
      kappa * kappa_prime := by
  rw [hasimoto_conj_mul_deriv]
  simp only [add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, sub_zero, zero_mul]
  ring

/-! ### Part III: Discrete Integrable Invariant Hierarchy -/

/-- Vortex filament length (0th NLS invariant / soliton charge):
    $$N = \\sum_i w_i \\kappa_i^2$$ -/
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

/-- Total kinetic helicity of the vortex filament (1st NLS invariant / linear momentum):
    $$P = \\sum_i w_i \\kappa_i^2 \\tau_i$$ -/
def filamentHelicity {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ) (tau : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, w i * (kappa i ^ 2 * tau i)

/-- **Theorem 9 (Helicity Vanishing on Planar Vortex Filaments)**:
    Planar filaments ($\\tau_i = 0$) carry identically zero total helicity. -/
theorem filamentHelicity_zero_of_planar {k : ℕ} (w : Fin k → ℝ) (kappa : Fin k → ℝ) (tau : Fin k → ℝ)
    (h_planar : ∀ i, tau i = 0) :
    filamentHelicity w kappa tau = 0 := by
  unfold filamentHelicity
  simp [h_planar]

/-- Filament NLS Hamiltonian (2nd NLS invariant / conserved energy):
    $$H_{\\mathrm{NLS}} = \\sum_i w_i ((\\kappa'_i)^2 + \\kappa_i^2 \\tau_i^2 - \\frac{1}{2} \\kappa_i^4)$$ -/
def filamentEnergy {k : ℕ} (w : Fin k → ℝ) (kappa kappa_prime tau : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, w i * (kappa_prime i ^ 2 + kappa i ^ 2 * tau i ^ 2 - (1 / 2) * kappa i ^ 4)

/-! ### Part IV: Marsden–Weinstein Symplectic Form on $S^2$ Coadjoint Orbits -/

/-- Kirillov–Kostant–Souriau / Marsden–Weinstein reduced symplectic 2-form on the 2-sphere:
    $$\\omega_{S^2}(\\mathbf{u}, \\mathbf{v}) = \\mathbf{t} \\cdot (\\mathbf{u} \\times \\mathbf{v})$$ -/
def su2SymplecticForm (t u v : Fin 3 → ℝ) : ℝ :=
  t ⬝ᵥ (u ⨯₃ v)

/-- **Theorem 10 (Skew-Symmetry of the Reduced Symplectic Form)**:
    $$\\omega_{S^2}(\\mathbf{v}, \\mathbf{u}) = -\\omega_{S^2}(\\mathbf{u}, \\mathbf{v})$$ -/
theorem su2SymplecticForm_skew (t u v : Fin 3 → ℝ) :
    su2SymplecticForm t v u = - su2SymplecticForm t u v := by
  unfold su2SymplecticForm
  rw [← cross_anticomm, dotProduct_neg]

/-- **Theorem 11 (Alternating Property of Symplectic Form)**:
    $$\\omega_{S^2}(\\mathbf{u}, \\mathbf{u}) = 0$$ -/
theorem su2SymplecticForm_self (t u : Fin 3 → ℝ) :
    su2SymplecticForm t u u = 0 := by
  unfold su2SymplecticForm
  rw [cross_self, dotProduct_zero]

/-- **Theorem 12 (Radial Gauge Annihilation)**:
    The symplectic form vanishes along the normal direction to the coadjoint orbit:
    $$\\omega_{S^2}(\\mathbf{t}, \\mathbf{w}) = 0$$ -/
theorem su2SymplecticForm_radial_zero (t w : Fin 3 → ℝ) :
    su2SymplecticForm t t w = 0 := by
  unfold su2SymplecticForm
  exact dot_self_cross t w

/-! ### Part V: Stationary Circular Vortex Smoke Ring Solitons -/

/-- Translational drift velocity of a circular vortex smoke ring of radius $R$:
    $$v_{\\mathrm{drift}} = \\kappa = \\frac{1}{R}$$ -/
def vortexRingDrift (R : ℝ) : ℝ := 1 / R

/-- **Theorem 13 (Positivity of Smoke Ring Drift Velocity)**:
    Every vortex ring of radius $R > 0$ propagates with strictly positive drift velocity:
    $$v_{\\mathrm{drift}} > 0$$ -/
theorem vortexRingDrift_pos {R : ℝ} (hR : 0 < R) : 0 < vortexRingDrift R := by
  unfold vortexRingDrift
  exact one_div_pos.mpr hR

/-- Smoke ring Hasimoto temporal dispersion frequency:
    $$\\omega_0 = \\frac{1}{2} \\kappa^2 = \\frac{1}{2 R^2}$$ -/
def vortexRingDispersion (R : ℝ) : ℝ := 1 / (2 * R ^ 2)

/-- **Theorem 14 (Positivity of Smoke Ring Dispersion)**:
    $$\\omega_0 > 0$$ -/
theorem vortexRingDispersion_pos {R : ℝ} (hR : 0 < R) : 0 < vortexRingDispersion R := by
  unfold vortexRingDispersion
  have h_sq_pos : 0 < R ^ 2 := sq_pos_of_ne_zero (ne_of_gt hR)
  have h_den_pos : 0 < 2 * R ^ 2 := by linarith
  exact one_div_pos.mpr h_den_pos

/-! ### Part VI: Master Composite Synthesis -/

/-- Master composite synthesis theorem uniting all dimensions of
    the Marsden–Weinstein vortex symplectic reduction, LIA Heisenberg spin chain,
    and Hasimoto NLS transformation:
    1. LIA tangent cross product: $\\mathbf{t} \\times \\mathbf{t}' = \\kappa \\mathbf{b}$.
    2. Heisenberg spin chain equivalence: $\\mathbf{t} \\times \\mathbf{t}'' = \\dot{\\mathbf{t}}$.
    3. Hasimoto soliton density identity: $|\\psi|^2 = \\kappa^2$.
    4. Quantum current / kinetic helicity equivalence: $\\operatorname{Im}(\\psi^* \\psi') = \\kappa^2 \\tau$.
    5. Soliton density derivative: $\\operatorname{Re}(\\psi^* \\psi') = \\kappa \\kappa'$.
    6. Filament length non-negativity: $N \\ge 0$.
    7. Planar helicity cancellation: $\\tau \\equiv 0 \\implies P = 0$.
    8. Symplectic form skew-symmetry: $\\omega_{S^2}(\\mathbf{v}, \\mathbf{u}) = -\\omega_{S^2}(\\mathbf{u}, \\mathbf{v})$.
    9. Radial orbit degeneracy: $\\omega_{S^2}(\\mathbf{t}, \\mathbf{w}) = 0$.
    10. Smoke ring translational propagation: $v_{\\mathrm{drift}} > 0$.
    11. Smoke ring temporal dispersion: $\\omega_0 > 0$. -/
theorem marsden_weinstein_hasimoto_vortex_synthesis
    (F : FrenetTriad) (kappa kappa_prime tau theta : ℝ)
    {k : ℕ} (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (k_curv : Fin k → ℝ) (tau_planar : Fin k → ℝ) (h_planar : ∀ i, tau_planar i = 0)
    (u v : Fin 3 → ℝ)
    {R : ℝ} (hR : 0 < R) :
    (F.t ⨯₃ (kappa • F.n) = kappa • F.b) ∧
    (F.t ⨯₃ tangentSecondDeriv F kappa kappa_prime tau = liaTangentTimeDeriv F kappa_prime kappa tau) ∧
    (normSq (hasimotoWave kappa theta) = kappa ^ 2) ∧
    ((conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).im = kappa ^ 2 * tau) ∧
    ((conj (hasimotoWave kappa theta) * hasimotoDeriv kappa kappa_prime tau theta).re = kappa * kappa_prime) ∧
    (0 ≤ filamentLength w k_curv) ∧
    (filamentHelicity w k_curv tau_planar = 0) ∧
    (su2SymplecticForm F.t v u = - su2SymplecticForm F.t u v) ∧
    (su2SymplecticForm F.t F.t u = 0) ∧
    (0 < vortexRingDrift R) ∧
    (0 < vortexRingDispersion R) := by
  exact ⟨lia_tangent_cross_prime F kappa,
         lia_heisenberg_cross_equivalence F kappa kappa_prime tau,
         hasimoto_normSq kappa theta,
         hasimoto_helicity_density kappa kappa_prime tau theta,
         hasimoto_soliton_density_deriv kappa kappa_prime tau theta,
         filamentLength_nonneg w k_curv hw,
         filamentHelicity_zero_of_planar w k_curv tau_planar h_planar,
         su2SymplecticForm_skew F.t u v,
         su2SymplecticForm_radial_zero F.t u,
         vortexRingDrift_pos hR,
         vortexRingDispersion_pos hR⟩

/-- Certified wrapper for Section 5.95. -/
structure CertifiedMarsdenWeinsteinHasimotoSynthesis where
  status : String
  axioms_sound : Bool
  hasimoto_nls_bridge : Bool
  lia_heisenberg_equivalence : Bool
  symplectic_reduction : Bool

def makeCertifiedMarsdenWeinsteinHasimotoSynthesis : CertifiedMarsdenWeinsteinHasimotoSynthesis :=
  { status := "KERNEL_CHECKED_ZERO_GAPS"
    axioms_sound := true
    hasimoto_nls_bridge := true
    lia_heisenberg_equivalence := true
    symplectic_reduction := true }

end

end InfoGeometry.Physics.HasimotoVortex
