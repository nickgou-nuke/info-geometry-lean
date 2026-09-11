import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornCartanRootReflections
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import Mathlib.Tactic

open InfoGeometry.Lie.CanonicalZornCartanRootReflections
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

/-!
# $G_2$ Cartan--Killing Metric Owner and 150° Root Angle Geometry

This module establishes the exact Cartan--Killing metric geometry on the
3-coordinate Cartan plane for the exceptional Lie algebra $\mathfrak{g}_2$.

Key verified properties:
1. **Root Lengths**: Short simple root $\|\alpha\|^2 = 2/3$, long simple root $\|\beta\|^2 = 2$.
2. **Length Ratio**: $\|\beta\| = \sqrt{3} \|\alpha\|$ and $\frac{\|\beta\|^2}{\|\alpha\|^2} = 3$.
3. **Cartan Pairing / Inner Product**: $\langle \alpha, \beta \rangle = -1$.
4. **Exact 150° Angle**: $\theta_{\alpha, \beta} = \frac{5\pi}{6} = 150^\circ$ via $\cos(5\pi/6) = -\frac{\sqrt{3}}{2}$.
5. **Highest Root Orthogonality**: $\langle \alpha, 3\alpha + 2\beta \rangle = 0 \implies 90^\circ$.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2RootMetricGeometry

/-- Euclidean inner product on the Cartan embedding ℝ³. -/
def cartanInner (v w : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, v i * w i

/-- Euclidean squared norm on the Cartan embedding ℝ³. -/
def cartanNormSq (v : Fin 3 → ℝ) : ℝ :=
  cartanInner v v

/-- Short simple root α in the 3-coordinate Cartan plane. -/
def shortSimpleRoot : Fin 3 → ℝ :=
  ![2 / 3, -(1 / 3), -(1 / 3)]

/-- Long simple root β in the 3-coordinate Cartan plane. -/
def longSimpleRoot : Fin 3 → ℝ :=
  ![-1, 1, 0]

/-- The 6 positive roots in the 3-coordinate Cartan plane. -/
def root_alpha : Fin 3 → ℝ := shortSimpleRoot
def root_beta : Fin 3 → ℝ := longSimpleRoot
def root_alpha_plus_beta : Fin 3 → ℝ := ![-1 / 3, 2 / 3, -(1 / 3)]
def root_two_alpha_plus_beta : Fin 3 → ℝ := ![-1 / 3, -(1 / 3), 2 / 3]
def root_three_alpha_plus_beta : Fin 3 → ℝ := ![1, 0, -1]
def root_three_alpha_plus_two_beta : Fin 3 → ℝ := ![0, 1, -1]

/-! ### Norm Theorems -/

@[simp] theorem shortSimpleRoot_normSq :
    cartanNormSq shortSimpleRoot = 2 / 3 := by
  simp [cartanNormSq, cartanInner, shortSimpleRoot, Fin.sum_univ_three]
  ring

@[simp] theorem longSimpleRoot_normSq :
    cartanNormSq longSimpleRoot = 2 := by
  simp [cartanNormSq, cartanInner, longSimpleRoot, Fin.sum_univ_three]
  ring

/-- **Theorem (Exact Root Length Ratio Squared is 3)**:
    $$\frac{\|\beta\|^2}{\|\alpha\|^2} = 3$$
-/
theorem g2_root_length_ratio_sq :
    cartanNormSq longSimpleRoot / cartanNormSq shortSimpleRoot = 3 := by
  rw [longSimpleRoot_normSq, shortSimpleRoot_normSq]
  norm_num

/-- **Theorem (Exact Root Length Ratio is √3)**:
    $$\|\beta\| = \sqrt{3} \|\alpha\|$$
-/
theorem g2_root_length_ratio :
    Real.sqrt (cartanNormSq longSimpleRoot) = Real.sqrt 3 * Real.sqrt (cartanNormSq shortSimpleRoot) := by
  rw [longSimpleRoot_normSq, shortSimpleRoot_normSq]
  have hpos3 : (0 : ℝ) ≤ 3 := by norm_num
  rw [← Real.sqrt_mul hpos3]
  congr 1
  norm_num

/-! ### Inner Product and Angle Theorems -/

@[simp] theorem simple_roots_inner :
    cartanInner shortSimpleRoot longSimpleRoot = -1 := by
  simp [cartanInner, shortSimpleRoot, longSimpleRoot, Fin.sum_univ_three]
  ring

/-- **Theorem (Cosine Squared Between Simple Roots is 3/4)**:
    $$\cos^2(\theta_{\alpha, \beta}) = \frac{\langle \alpha, \beta \rangle^2}{\|\alpha\|^2 \|\beta\|^2} = \frac{3}{4}$$
-/
theorem simple_roots_cos_sq :
    (cartanInner shortSimpleRoot longSimpleRoot)^2 /
      (cartanNormSq shortSimpleRoot * cartanNormSq longSimpleRoot) = 3 / 4 := by
  rw [simple_roots_inner, shortSimpleRoot_normSq, longSimpleRoot_normSq]
  norm_num

/-- **Theorem (Cosine of Angle Between Simple Roots is -√3 / 2)**:
    $$\cos(\theta_{\alpha, \beta}) = \frac{\langle \alpha, \beta \rangle}{\|\alpha\| \|\beta\|} = -\frac{\sqrt{3}}{2}$$
-/
theorem simple_roots_cos :
    cartanInner shortSimpleRoot longSimpleRoot /
      (Real.sqrt (cartanNormSq shortSimpleRoot) * Real.sqrt (cartanNormSq longSimpleRoot)) =
        - Real.sqrt 3 / 2 := by
  rw [simple_roots_inner, shortSimpleRoot_normSq, longSimpleRoot_normSq]
  have h23 : (0 : ℝ) ≤ 2 / 3 := by norm_num
  rw [← Real.sqrt_mul h23]
  have h43 : (2 / 3 : ℝ) * 2 = 4 / 3 := by norm_num
  rw [h43]
  have hsqrt43 : Real.sqrt (4 / 3) = 2 / Real.sqrt 3 := by
    have h4 : (0 : ℝ) ≤ 4 := by norm_num
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    have h4sqrt : Real.sqrt 4 = 2 := by
      have h2sq : (4 : ℝ) = 2^2 := by norm_num
      rw [h2sq, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_div h4, h4sqrt]
  rw [hsqrt43]
  have hnz : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp

/-- **GRAND THEOREM (Exact 150° Angle Between Simple Roots)**:
    $$\theta_{\alpha, \beta} = \frac{5\pi}{6} = 150^\circ$$
    verified through $\cos(5\pi/6) = -\frac{\sqrt{3}}{2}$.
-/
theorem simple_roots_angle_is_150_degrees :
    Real.cos (5 * Real.pi / 6) =
      cartanInner shortSimpleRoot longSimpleRoot /
        (Real.sqrt (cartanNormSq shortSimpleRoot) * Real.sqrt (cartanNormSq longSimpleRoot)) := by
  have h : 5 * Real.pi / 6 = Real.pi - Real.pi / 6 := by ring
  have hneg : -(Real.sqrt 3 / 2) = - Real.sqrt 3 / 2 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_six, hneg, simple_roots_cos]

/-! ### Orthogonality of Highest Root -/

/-- **Theorem (Highest Root Orthogonal to Short Simple Root)**:
    $$\langle \alpha, 3\alpha + 2\beta \rangle = 0 \implies \theta = 90^\circ$$
-/
theorem highest_root_orthogonal_to_short_simple :
    cartanInner shortSimpleRoot root_three_alpha_plus_two_beta = 0 := by
  simp [cartanInner, shortSimpleRoot, root_three_alpha_plus_two_beta, Fin.sum_univ_three]

/-- **Theorem (Cosine of 90° is Zero)**:
    $$\cos(\pi / 2) = 0$$
-/
theorem highest_root_angle_is_90_degrees :
    Real.cos (Real.pi / 2) =
      cartanInner shortSimpleRoot root_three_alpha_plus_two_beta /
        (Real.sqrt (cartanNormSq shortSimpleRoot) * Real.sqrt (cartanNormSq root_three_alpha_plus_two_beta)) := by
  rw [Real.cos_pi_div_two, highest_root_orthogonal_to_short_simple, zero_div]

end InfoGeometry.Lie.CanonicalZornG2RootMetricGeometry
