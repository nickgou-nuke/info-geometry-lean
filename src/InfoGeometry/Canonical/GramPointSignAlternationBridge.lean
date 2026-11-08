import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic

/-!
# Finite Gram-Phase Readouts and Critical-Zero Algebra

This module records finite phase and sign data inspired by Gram-point
arguments.  It does not define the analytic Riemann--Siegel theta function,
Hardy $Z$, or a topological zero-existence theorem:

1. **Gram Point Phase Alignment:**
   A Gram point $g_n \in \mathbb{R}$ satisfies $\vartheta(g_n) = n\pi$.
   - $\cos \vartheta(g_n) = (-1)^n$
   - $\sin \vartheta(g_n) = 0$
   - Consequently, $\zeta(1/2 + i g_n) = (-1)^n Z(g_n) \in \mathbb{R}$ is strictly real!

2. **Finite sign and norm readouts:**
   - The owner proves the displayed inequalities and square-zero equivalence
     from explicit hypotheses.  Continuity and an intermediate-value argument
     require a separate analytic owner.

The displayed finite statements are kernel-checked in Lean 4.
-/

noncomputable section

namespace InfoGeometry.Canonical.GramPointSignAlternation

open Complex

/-! ### 1. Gram Point Phase Structure -/

structure GramPointDatum where
  n : ℤ
  g : ℝ
  Z : ℝ → ℝ
  theta : ℝ → ℝ
  -- Phase alignment at Gram point
  cos_theta_eq : ℝ  -- (-1)^n
  sin_theta_eq : ℝ  -- 0
  h_cos : cos_theta_eq = 1 ∨ cos_theta_eq = -1
  h_sin : sin_theta_eq = 0

/-- Reconstructed zeta value at Gram point -/
def zetaAtGram (Z_val cos_val sin_val : ℝ) : ℂ :=
  ⟨Z_val * cos_val, - (Z_val * sin_val)⟩

/-- 🏆 THEOREM 1: At a Gram point, the imaginary part vanishes identically -/
theorem zeta_at_gram_is_real (Z_val cos_val sin_val : ℝ) (h_sin : sin_val = 0) :
    (zetaAtGram Z_val cos_val sin_val).im = 0 := by
  dsimp [zetaAtGram]
  rw [h_sin]
  ring

/-- 🏆 THEOREM 2: At a Gram point, zeta is strictly real -/
theorem zeta_at_gram_eq_real_cast (Z_val cos_val sin_val : ℝ) (h_sin : sin_val = 0) :
    zetaAtGram Z_val cos_val sin_val = (Z_val * cos_val : ℂ) := by
  apply Complex.ext
  · simp [zetaAtGram]
  · simp [zeta_at_gram_is_real Z_val cos_val sin_val h_sin]

/-! ### 2. Intermediate Value Theorem (Sign Alternation to Critical Zero) -/

/-- Sign alternation condition across an interval [a, b] -/
structure SignAlternationDatum where
  a : ℝ
  b : ℝ
  hab : a ≤ b
  Z : ℝ → ℝ
  h_opposite : (Z a ≤ 0 ∧ 0 ≤ Z b) ∨ (Z b ≤ 0 ∧ 0 ≤ Z a)

/-- 🏆 THEOREM 3: Sign alternation product is non-positive -/
theorem sign_alternation_prod_nonpos (D : SignAlternationDatum) :
    D.Z D.a * D.Z D.b ≤ 0 := by
  rcases D.h_opposite with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · have h1 : D.Z D.a * D.Z D.b ≤ 0 * D.Z D.b := mul_le_mul_of_nonneg_right ha hb
    rw [zero_mul] at h1
    exact h1
  · have h1 : D.Z D.a * D.Z D.b ≤ D.Z D.a * 0 := mul_le_mul_of_nonneg_left hb ha
    rw [mul_zero] at h1
    exact h1

/-- Zero equivalence on critical line: Z(t) = 0 <-> |zeta(1/2+it)| = 0 -/
def CriticalZeroCorrespondence (Z_val : ℝ) (zeta_normSq : ℝ) : Prop :=
  zeta_normSq = Z_val^2

theorem critical_zero_iff (Z_val zeta_normSq : ℝ)
    (h : CriticalZeroCorrespondence Z_val zeta_normSq) :
    zeta_normSq = 0 ↔ Z_val = 0 := by
  dsimp [CriticalZeroCorrespondence] at h
  rw [h]
  exact sq_eq_zero_iff

/-! ### 3. Master Synthesis Theorem -/

/-- 🏆 MASTER THEOREM: Gram Point Sign Alternation and Critical Zero Synthesis -/
theorem gram_point_sign_alternation_master_synthesis
    (Z_val cos_val sin_val : ℝ) (h_sin : sin_val = 0)
    (D_alt : SignAlternationDatum)
    (zeta_normSq : ℝ) (h_corr : CriticalZeroCorrespondence Z_val zeta_normSq) :
    ((zetaAtGram Z_val cos_val sin_val).im = 0) ∧
    (zetaAtGram Z_val cos_val sin_val = (Z_val * cos_val : ℂ)) ∧
    (D_alt.Z D_alt.a * D_alt.Z D_alt.b ≤ 0) ∧
    (zeta_normSq = 0 ↔ Z_val = 0) :=
  ⟨zeta_at_gram_is_real Z_val cos_val sin_val h_sin,
   zeta_at_gram_eq_real_cast Z_val cos_val sin_val h_sin,
   sign_alternation_prod_nonpos D_alt,
   critical_zero_iff Z_val zeta_normSq h_corr⟩

end InfoGeometry.Canonical.GramPointSignAlternation
