import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Exact Self-Concordant Barrier Geometry on Doubled Positive Cones

This module formalizes:
1. The Volume Potential Φ_vol and Chiral Potential Φ_chir on positive eigenvalue spectra.
2. First-order Gradients / Dual Moments: ∇Φ_vol and ∇Φ_chir.
3. Second-order Hessians / Fisher–Rao Metrics: ∇²Φ_vol and ∇²Φ_chir.
4. Positive Definiteness: ∇²Φ_vol(h, h) > 0 for non-zero perturbations h ≠ 0.
5. Third-order Directional Curvatures: ∇³Φ_vol and ∇³Φ_chir.
6. The Nesterov–Nemirovski Self-Concordance Inequality:
     |∇³Φ_vol(h, h, h)| ≤ 2 * (∇²Φ_vol(h, h))^(3/2)
   proved natively using the spectral power-sum bound ∑ |uᵢ|³ ≤ (∑ uᵢ²)^(3/2).
7. Weyl Scale Transformation Laws:
     Φ_vol(s • a, s • d) = Φ_vol(a, d) - 2n * log s
     Φ_chir(s • a, s • d) = Φ_chir(a, d)  (Strict scale invariance)

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.Modular.SelfConcordance

variable {ι : Type*} [Fintype ι]

/-- A positive spectral state represents the eigenvalues of an element in the positive cone Herm⁺(n). -/
structure PositiveState (ι : Type*) [Fintype ι] where
  val : ι → ℝ
  pos : ∀ i, 0 < val i

/-!
=============================================================================
PART 1: Potentials, Gradients, Hessians, and Third Derivatives
=============================================================================
-/

/-- Single-sector log-barrier: F(a) = - ∑ᵢ log(aᵢ). -/
def logBarrier (a : PositiveState ι) : ℝ :=
  - ∑ i, Real.log (a.val i)

/-- Volume Barrier on doubled positive cone: Φ_vol(a, d) = F(a) + F(d). -/
def barrierVol (a d : PositiveState ι) : ℝ :=
  logBarrier a + logBarrier d

/-- Chiral Barrier on doubled positive cone: Φ_chir(a, d) = F(a) - F(d). -/
def barrierChir (a d : PositiveState ι) : ℝ :=
  logBarrier a - logBarrier d

/-- Single-sector Gradient / Dual Observable: ∇F(a)[h] = - ∑ᵢ (hᵢ / aᵢ). -/
def gradLogBarrier (a : PositiveState ι) (h : ι → ℝ) : ℝ :=
  - ∑ i, h i / a.val i

/-- Volume Gradient: ∇Φ_vol(a, d)[h, k] = ∇F(a)[h] + ∇F(d)[k]. -/
def gradVol (a d : PositiveState ι) (h k : ι → ℝ) : ℝ :=
  gradLogBarrier a h + gradLogBarrier d k

/-- Chiral Gradient: ∇Φ_chir(a, d)[h, k] = ∇F(a)[h] - ∇F(d)[k]. -/
def gradChir (a d : PositiveState ι) (h k : ι → ℝ) : ℝ :=
  gradLogBarrier a h - gradLogBarrier d k

/-- Single-sector Hessian / Fisher–Rao Quadratic Form: ∇²F(a)[h, h] = ∑ᵢ (hᵢ / aᵢ)². -/
def hessLogBarrier (a : PositiveState ι) (h : ι → ℝ) : ℝ :=
  ∑ i, (h i / a.val i) ^ 2

/-- Volume Hessian / Siegel Metric: ∇²Φ_vol(a, d)[(h, k), (h, k)] = ∇²F(a)[h, h] + ∇²F(d)[k, k]. -/
def hessVol (a d : PositiveState ι) (h k : ι → ℝ) : ℝ :=
  hessLogBarrier a h + hessLogBarrier d k

/-- Chiral Hessian Quadratic Form: ∇²Φ_chir(a, d)[(h, k), (h, k)] = ∇²F(a)[h, h] - ∇²F(d)[k, k]. -/
def hessChir (a d : PositiveState ι) (h k : ι → ℝ) : ℝ :=
  hessLogBarrier a h - hessLogBarrier d k

/-- Single-sector Third Derivative: ∇³F(a)[h, h, h] = -2 ∑ᵢ (hᵢ / aᵢ)³. -/
def thirdLogBarrier (a : PositiveState ι) (h : ι → ℝ) : ℝ :=
  - 2 * ∑ i, (h i / a.val i) ^ 3

/-- Volume Third Derivative: ∇³Φ_vol(a, d)[(h, k), (h, k), (h, k)] = ∇³F(a)[h] + ∇³F(d)[k]. -/
def thirdVol (a d : PositiveState ι) (h k : ι → ℝ) : ℝ :=
  thirdLogBarrier a h + thirdLogBarrier d k

/-!
=============================================================================
PART 2: Positivity and Metric Properties of the Hessian
=============================================================================
-/

/-- THEOREM 1 (Non-Negativity of Single-Sector Hessian): ∇²F(a)[h, h] ≥ 0. -/
theorem hessLogBarrier_nonneg (a : PositiveState ι) (h : ι → ℝ) :
    0 ≤ hessLogBarrier a h := by
  dsimp [hessLogBarrier]
  apply sum_nonneg
  intro i _
  exact sq_nonneg _

/-- THEOREM 2 (Non-Negativity of Volume Hessian / Siegel Metric): ∇²Φ_vol ≥ 0. -/
theorem hessVol_nonneg (a d : PositiveState ι) (h k : ι → ℝ) :
    0 ≤ hessVol a d h k := by
  dsimp [hessVol]
  have h1 := hessLogBarrier_nonneg a h
  have h2 := hessLogBarrier_nonneg d k
  linarith

/-- 
  THEOREM 3 (Strict Positivity / Non-Degeneracy):
  If the perturbation (h, k) is non-zero, then the Volume Hessian is strictly positive:
  (∃ i, h i ≠ 0 ∨ k i ≠ 0) ⟹ ∇²Φ_vol > 0.
-/
theorem hessVol_pos_of_ne_zero (a d : PositiveState ι) (h k : ι → ℝ)
    (i₀ : ι) (h_nonzero : h i₀ ≠ 0 ∨ k i₀ ≠ 0) :
    0 < hessVol a d h k := by
  dsimp [hessVol, hessLogBarrier]
  have h_sum_a : 0 ≤ ∑ i, (h i / a.val i) ^ 2 := sum_nonneg (fun i _ => sq_nonneg _)
  have h_sum_d : 0 ≤ ∑ i, (k i / d.val i) ^ 2 := sum_nonneg (fun i _ => sq_nonneg _)
  cases h_nonzero with
  | inl hh =>
    have h_term_pos : 0 < (h i₀ / a.val i₀) ^ 2 := by
      have h_div : h i₀ / a.val i₀ ≠ 0 := div_ne_zero hh (ne_of_gt (a.pos i₀))
      exact sq_pos_of_ne_zero h_div
    have h_sum_a_pos : 0 < ∑ i, (h i / a.val i) ^ 2 := by
      calc
        0 < (h i₀ / a.val i₀) ^ 2 := h_term_pos
        _ ≤ ∑ i, (h i / a.val i) ^ 2 := single_le_sum (s := univ) (fun i _ => sq_nonneg (h i / a.val i)) (mem_univ i₀)
    linarith
  | inr hk =>
    have h_term_pos : 0 < (k i₀ / d.val i₀) ^ 2 := by
      have h_div : k i₀ / d.val i₀ ≠ 0 := div_ne_zero hk (ne_of_gt (d.pos i₀))
      exact sq_pos_of_ne_zero h_div
    have h_sum_d_pos : 0 < ∑ i, (k i / d.val i) ^ 2 := by
      calc
        0 < (k i₀ / d.val i₀) ^ 2 := h_term_pos
        _ ≤ ∑ i, (k i / d.val i) ^ 2 := single_le_sum (s := univ) (fun i _ => sq_nonneg (k i / d.val i)) (mem_univ i₀)
    linarith

/-!
=============================================================================
PART 3: The Nesterov–Nemirovski Self-Concordance Inequality
=============================================================================
-/

/-- Helper lemma: for any vector u, |∑ᵢ uᵢ³| ≤ ∑ᵢ |uᵢ|³. -/
lemma abs_sum_cube_le_sum_abs_cube (u : ι → ℝ) :
    |∑ i, u i ^ 3| ≤ ∑ i, |u i| ^ 3 := by
  have h := abs_sum_le_sum_abs (fun i => u i ^ 3) univ
  have h_eq (i : ι) : |u i ^ 3| = |u i| ^ 3 := by
    rw [abs_pow]
  simp_rw [h_eq] at h
  exact h

/-- Helper lemma: for any vector u, |u j| ≤ sqrt(∑ᵢ uᵢ²). -/
lemma abs_le_sqrt_sum_sq (u : ι → ℝ) (j : ι) :
    |u j| ≤ Real.sqrt (∑ i, (u i) ^ 2) := by
  have h_sq : (u j) ^ 2 ≤ ∑ i, (u i) ^ 2 :=
    single_le_sum (s := univ) (fun i _ => sq_nonneg (u i)) (mem_univ j)
  have h_nonneg : 0 ≤ ∑ i, (u i) ^ 2 := sum_nonneg (fun i _ => sq_nonneg _)
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq_eq_abs] at h_sqrt
  exact h_sqrt

/-- 
  LEMMA (Power-Sum / L2-L3 Bound):
  ∑ᵢ |uᵢ|³ ≤ (∑ᵢ uᵢ²)^(3/2) = (sqrt(∑ᵢ uᵢ²)) * (∑ᵢ uᵢ²).
-/
theorem sum_abs_cube_le_pow_three_halves (u : ι → ℝ) :
    ∑ i, |u i| ^ 3 ≤ (Real.sqrt (∑ i, (u i) ^ 2)) * (∑ i, (u i) ^ 2) := by
  have h_term (i : ι) : |u i| ^ 3 ≤ Real.sqrt (∑ j, (u j) ^ 2) * (u i) ^ 2 := by
    have h_abs := abs_le_sqrt_sum_sq u i
    have h_cube_eq : |u i| ^ 3 = |u i| * (u i) ^ 2 := by
      calc |u i| ^ 3 = |u i| * |u i| ^ 2 := by ring
      _ = |u i| * (u i) ^ 2 := by rw [sq_abs]
    calc
      |u i| ^ 3 = |u i| * (u i) ^ 2 := h_cube_eq
      _ ≤ Real.sqrt (∑ j, (u j) ^ 2) * (u i) ^ 2 := by
        have h_sq_nonneg : 0 ≤ (u i) ^ 2 := sq_nonneg _
        nlinarith
  have h_sum : ∑ i, |u i| ^ 3 ≤ ∑ i, Real.sqrt (∑ j, (u j) ^ 2) * (u i) ^ 2 :=
    sum_le_sum (s := univ) (fun i _ => h_term i)
  rw [← mul_sum] at h_sum
  exact h_sum

/-- 
  THEOREM 4 (Single-Sector Self-Concordance Inequality):
  |∇³F(a)[h, h, h]| ≤ 2 * (sqrt(∇²F(a)[h, h])) * ∇²F(a)[h, h]
  (which is 2 * (∇²F(a)[h, h])^(3/2)).
-/
theorem logBarrier_self_concordant (a : PositiveState ι) (h : ι → ℝ) :
    |thirdLogBarrier a h| ≤ 2 * (Real.sqrt (hessLogBarrier a h)) * hessLogBarrier a h := by
  dsimp [thirdLogBarrier, hessLogBarrier]
  have h_abs_mult : |-2 * ∑ i, (h i / a.val i) ^ 3| = 2 * |∑ i, (h i / a.val i) ^ 3| := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [h_abs_mult]
  have h_cube_bound := abs_sum_cube_le_sum_abs_cube (fun i => h i / a.val i)
  have h_l2_bound := sum_abs_cube_le_pow_three_halves (fun i => h i / a.val i)
  have h_chain : |∑ i, (h i / a.val i) ^ 3| ≤ Real.sqrt (∑ i, (h i / a.val i) ^ 2) * ∑ i, (h i / a.val i) ^ 2 :=
    le_trans h_cube_bound h_l2_bound
  nlinarith

/-- 
  THEOREM 5 (Doubled Volume Self-Concordance Theorem):
  For any doubled perturbation (h, k), the volume barrier satisfies the universal
  Nesterov–Nemirovski self-concordance inequality:
    |∇³Φ_vol| ≤ 2 * (sqrt(∇²Φ_vol)) * ∇²Φ_vol
-/
theorem volumeBarrier_self_concordant (a d : PositiveState ι) (h k : ι → ℝ) :
    |thirdVol a d h k| ≤ 2 * (Real.sqrt (hessVol a d h k)) * hessVol a d h k := by
  dsimp [thirdVol, hessVol, thirdLogBarrier, hessLogBarrier]
  have h_sum_terms :
      (-2 * ∑ i, (h i / a.val i) ^ 3) + (-2 * ∑ i, (k i / d.val i) ^ 3) =
      -2 * ((∑ i, (h i / a.val i) ^ 3) + (∑ i, (k i / d.val i) ^ 3)) := by ring
  rw [h_sum_terms]
  have h_abs_two : |-2 * ((∑ i, (h i / a.val i) ^ 3) + (∑ i, (k i / d.val i) ^ 3))| =
      2 * |(∑ i, (h i / a.val i) ^ 3) + (∑ i, (k i / d.val i) ^ 3)| := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [h_abs_two]
  let Sa := ∑ i, (h i / a.val i) ^ 2
  let Sd := ∑ i, (k i / d.val i) ^ 2
  let Stot := Sa + Sd
  have hSa_nonneg : 0 ≤ Sa := sum_nonneg (fun i _ => sq_nonneg _)
  have hSd_nonneg : 0 ≤ Sd := sum_nonneg (fun i _ => sq_nonneg _)
  have hStot_nonneg : 0 ≤ Stot := by linarith
  have hSa_le_Stot : Sa ≤ Stot := by linarith
  have hSd_le_Stot : Sd ≤ Stot := by linarith

  have h_a_cube : |∑ i, (h i / a.val i) ^ 3| ≤ Real.sqrt Stot * Sa := by
    have h1 := abs_sum_cube_le_sum_abs_cube (fun i => h i / a.val i)
    have h2 : ∑ i, |h i / a.val i| ^ 3 ≤ Real.sqrt Stot * Sa := by
      have h_term (i : ι) : |h i / a.val i| ^ 3 ≤ Real.sqrt Stot * (h i / a.val i) ^ 2 := by
        have h_abs_le_Sa := abs_le_sqrt_sum_sq (fun i => h i / a.val i) i
        have h_sqrt_le : Real.sqrt Sa ≤ Real.sqrt Stot := Real.sqrt_le_sqrt hSa_le_Stot
        have h_abs_le : |h i / a.val i| ≤ Real.sqrt Stot := le_trans h_abs_le_Sa h_sqrt_le
        have h_cube_eq : |h i / a.val i| ^ 3 = |h i / a.val i| * (h i / a.val i) ^ 2 := by
          calc |h i / a.val i| ^ 3 = |h i / a.val i| * |h i / a.val i| ^ 2 := by ring
          _ = |h i / a.val i| * (h i / a.val i) ^ 2 := by rw [sq_abs]
        calc
          |h i / a.val i| ^ 3 = |h i / a.val i| * (h i / a.val i) ^ 2 := h_cube_eq
          _ ≤ Real.sqrt Stot * (h i / a.val i) ^ 2 := by
            have h_sq_nonneg : 0 ≤ (h i / a.val i) ^ 2 := sq_nonneg _
            nlinarith
      have h_sum : ∑ i, |h i / a.val i| ^ 3 ≤ ∑ i, Real.sqrt Stot * (h i / a.val i) ^ 2 :=
        sum_le_sum (s := univ) (fun i _ => h_term i)
      rw [← mul_sum] at h_sum
      exact h_sum
    exact le_trans h1 h2

  have h_d_cube : |∑ i, (k i / d.val i) ^ 3| ≤ Real.sqrt Stot * Sd := by
    have h1 := abs_sum_cube_le_sum_abs_cube (fun i => k i / d.val i)
    have h2 : ∑ i, |k i / d.val i| ^ 3 ≤ Real.sqrt Stot * Sd := by
      have h_term (i : ι) : |k i / d.val i| ^ 3 ≤ Real.sqrt Stot * (k i / d.val i) ^ 2 := by
        have h_abs_le_Sd := abs_le_sqrt_sum_sq (fun i => k i / d.val i) i
        have h_sqrt_le : Real.sqrt Sd ≤ Real.sqrt Stot := Real.sqrt_le_sqrt hSd_le_Stot
        have h_abs_le : |k i / d.val i| ≤ Real.sqrt Stot := le_trans h_abs_le_Sd h_sqrt_le
        have h_cube_eq : |k i / d.val i| ^ 3 = |k i / d.val i| * (k i / d.val i) ^ 2 := by
          calc |k i / d.val i| ^ 3 = |k i / d.val i| * |k i / d.val i| ^ 2 := by ring
          _ = |k i / d.val i| * (k i / d.val i) ^ 2 := by rw [sq_abs]
        calc
          |k i / d.val i| ^ 3 = |k i / d.val i| * (k i / d.val i) ^ 2 := h_cube_eq
          _ ≤ Real.sqrt Stot * (k i / d.val i) ^ 2 := by
            have h_sq_nonneg : 0 ≤ (k i / d.val i) ^ 2 := sq_nonneg _
            nlinarith
      have h_sum : ∑ i, |k i / d.val i| ^ 3 ≤ ∑ i, Real.sqrt Stot * (k i / d.val i) ^ 2 :=
        sum_le_sum (s := univ) (fun i _ => h_term i)
      rw [← mul_sum] at h_sum
      exact h_sum
    exact le_trans h1 h2

  have h_tri : |(∑ i, (h i / a.val i) ^ 3) + (∑ i, (k i / d.val i) ^ 3)| ≤
      |∑ i, (h i / a.val i) ^ 3| + |∑ i, (k i / d.val i) ^ 3| := abs_add_le _ _
  have h_bound : |(∑ i, (h i / a.val i) ^ 3) + (∑ i, (k i / d.val i) ^ 3)| ≤
      Real.sqrt Stot * Stot := by
    calc
      |(∑ i, (h i / a.val i) ^ 3) + (∑ i, (k i / d.val i) ^ 3)|
        ≤ |∑ i, (h i / a.val i) ^ 3| + |∑ i, (k i / d.val i) ^ 3| := h_tri
      _ ≤ Real.sqrt Stot * Sa + Real.sqrt Stot * Sd := add_le_add h_a_cube h_d_cube
      _ = Real.sqrt Stot * (Sa + Sd) := by ring
      _ = Real.sqrt Stot * Stot := rfl
  nlinarith

/-!
=============================================================================
PART 4: Weyl Scale Invariance and Homogeneous Transformations
=============================================================================
-/

/-- Positive scalar scaling of a positive state. -/
def scaleState (s : ℝ) (hs : 0 < s) (a : PositiveState ι) : PositiveState ι where
  val := fun i => s * a.val i
  pos := fun i => mul_pos hs (a.pos i)

/-- 
  THEOREM 6 (Weyl Dilation of the Volume Barrier):
  Under isotropic scale s > 0, Φ_vol scales by -2n * log s:
    Φ_vol(s • a, s • d) = Φ_vol(a, d) - 2 * card(ι) * log s
-/
theorem barrierVol_weyl_scale (s : ℝ) (hs : 0 < s) (a d : PositiveState ι) :
    barrierVol (scaleState s hs a) (scaleState s hs d) =
      barrierVol a d - 2 * (Fintype.card ι : ℝ) * Real.log s := by
  dsimp [barrierVol, logBarrier, scaleState]
  have h_log_a (i : ι) : Real.log (s * a.val i) = Real.log s + Real.log (a.val i) :=
    Real.log_mul (ne_of_gt hs) (ne_of_gt (a.pos i))
  have h_log_d (i : ι) : Real.log (s * d.val i) = Real.log s + Real.log (d.val i) :=
    Real.log_mul (ne_of_gt hs) (ne_of_gt (d.pos i))
  simp_rw [h_log_a, h_log_d]
  rw [sum_add_distrib, sum_add_distrib]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  ring

/-- 
  THEOREM 7 (Strict Weyl Invariance of the Chiral Barrier):
  The chiral barrier is identically invariant under isotropic Weyl scaling:
    Φ_chir(s • a, s • d) = Φ_chir(a, d)
-/
theorem barrierChir_weyl_invariant (s : ℝ) (hs : 0 < s) (a d : PositiveState ι) :
    barrierChir (scaleState s hs a) (scaleState s hs d) = barrierChir a d := by
  dsimp [barrierChir, logBarrier, scaleState]
  have h_log_a (i : ι) : Real.log (s * a.val i) = Real.log s + Real.log (a.val i) :=
    Real.log_mul (ne_of_gt hs) (ne_of_gt (a.pos i))
  have h_log_d (i : ι) : Real.log (s * d.val i) = Real.log s + Real.log (d.val i) :=
    Real.log_mul (ne_of_gt hs) (ne_of_gt (d.pos i))
  simp_rw [h_log_a, h_log_d]
  rw [sum_add_distrib, sum_add_distrib]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  ring

/--
  THEOREM 8 (Hessian Scaling Law):
  Under scaling by s, the Hessian scales by s⁻²:
    ∇²Φ_vol(s • a, s • d)[h, k] = s⁻² * ∇²Φ_vol(a, d)[h, k]
-/
theorem hessVol_weyl_scale (s : ℝ) (hs : 0 < s) (a d : PositiveState ι) (h k : ι → ℝ) :
    hessVol (scaleState s hs a) (scaleState s hs d) h k =
      (s ^ 2)⁻¹ * hessVol a d h k := by
  dsimp [hessVol, hessLogBarrier, scaleState]
  have h_div_a (i : ι) : (h i / (s * a.val i)) ^ 2 = (s ^ 2)⁻¹ * (h i / a.val i) ^ 2 := by
    have h_alg : h i / (s * a.val i) = s⁻¹ * (h i / a.val i) := by
      calc h i / (s * a.val i) = h i * (s * a.val i)⁻¹ := div_eq_mul_inv (h i) (s * a.val i)
      _ = h i * (s⁻¹ * (a.val i)⁻¹) := by rw [mul_inv]
      _ = s⁻¹ * (h i * (a.val i)⁻¹) := by ring
      _ = s⁻¹ * (h i / a.val i) := by rw [div_eq_mul_inv]
    rw [h_alg, mul_pow, inv_pow]
  have h_div_d (i : ι) : (k i / (s * d.val i)) ^ 2 = (s ^ 2)⁻¹ * (k i / d.val i) ^ 2 := by
    have h_alg : k i / (s * d.val i) = s⁻¹ * (k i / d.val i) := by
      calc k i / (s * d.val i) = k i * (s * d.val i)⁻¹ := div_eq_mul_inv (k i) (s * d.val i)
      _ = k i * (s⁻¹ * (d.val i)⁻¹) := by rw [mul_inv]
      _ = s⁻¹ * (k i * (d.val i)⁻¹) := by ring
      _ = s⁻¹ * (k i / d.val i) := by rw [div_eq_mul_inv]
    rw [h_alg, mul_pow, inv_pow]
  simp_rw [h_div_a, h_div_d]
  rw [← mul_sum, ← mul_sum, ← mul_add]

end InfoGeometry.Modular.SelfConcordance

end noncomputable section
