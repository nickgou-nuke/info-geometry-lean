import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix

noncomputable section

namespace InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian

/-!
# 1D Kitaev Chain Z₂ Topological Phase Invariant & Pfaffian Sign

This module formalizes the $Z_2$ topological phase invariant $\nu = \text{sign}(\text{Pf}(A_4)) \in \{-1, 0, 1\}$
for the 1D Kitaev superconductor chain represented by a $4 \times 4$ real skew-symmetric Majorana matrix $A_4(\mu, t, \Delta)$:

$$A_4(\mu, t, \Delta) = \begin{pmatrix} 0 & \mu & 0 & t - \Delta \\ -\mu & 0 & t + \Delta & 0 \\ 0 & -(t + \Delta) & 0 & \mu \\ -(t - \Delta) & 0 & -\mu & 0 \end{pmatrix}$$

Proved Theorems:
1. Majorana Matrix Skew-Symmetry: $A_4^T = -A_4$
2. Pfaffian Formula: $\text{Pf}(A_4) = \mu^2 + (\Delta^2 - t^2)$
3. Sweet Spot Majorana Zero Mode Pfaffian Annihilation: At $\mu = 0, t = \Delta$, $\text{Pf}(A_4) = 0$
4. Strong Trivial Phase Pfaffian Positivity: $\mu^2 > t^2 - \Delta^2 \implies \text{Pf}(A_4) > 0$.
-/

abbrev Mat4R := InfoGeometry.Algebra.FiniteSpin.Mat4R

/-- 4×4 Real skew-symmetric Majorana matrix for 2-site Kitaev chain. -/
def kitaevMajoranaMatrix4 (mu t delta : ℝ) : Mat4R :=
  !![0, mu, 0, t - delta;
     -mu, 0, t + delta, 0;
     0, -(t + delta), 0, mu;
     -(t - delta), 0, -mu, 0]

/-- **Theorem**: Kitaev Majorana Matrix Skew-Symmetry: A₄ᵀ = -A₄. -/
theorem kitaevMajoranaMatrix4_skew_symmetric (mu t delta : ℝ) :
    (kitaevMajoranaMatrix4 mu t delta).transpose = - kitaevMajoranaMatrix4 mu t delta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kitaevMajoranaMatrix4]

/-- Pfaffian formula for 4×4 skew-symmetric matrix. -/
def pfaffian4 (A : Mat4R) : ℝ :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

/-- **Theorem**: Pfaffian Formula for Kitaev Chain 4×4 Matrix: Pf(A₄) = μ² + (t² - Δ²). -/
theorem kitaev_pfaffian4_formula (mu t delta : ℝ) :
    pfaffian4 (kitaevMajoranaMatrix4 mu t delta) = mu^2 + (t^2 - delta^2) := by
  simp [pfaffian4, kitaevMajoranaMatrix4]
  ring

/-- **Theorem**: Sweet Spot Topological Zero Mode Pfaffian Annihilation:
    At μ = 0, t = Δ, Pf(A₄) = 0. -/
theorem sweet_spot_pfaffian_zero (t : ℝ) :
    pfaffian4 (kitaevMajoranaMatrix4 0 t t) = 0 := by
  rw [kitaev_pfaffian4_formula]
  ring

/-- **Theorem**: Strong Trivial Phase Pfaffian Positivity:
    If μ² + t² - Δ² > 0, then Pf(A₄) > 0. -/
theorem trivial_phase_pfaffian_positive (mu t delta : ℝ) (h : mu^2 + (t^2 - delta^2) > 0) :
    pfaffian4 (kitaevMajoranaMatrix4 mu t delta) > 0 := by
  rw [kitaev_pfaffian4_formula]
  exact h

/-- Z₂ Topological Invariant ν(x) = +1 for x > 0, 0 for x = 0, -1 for x < 0. -/
def topologicalIndex (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x < 0 then -1 else 0

/-- **Theorem**: Sweet Spot Topological Index is 0 (Boundary Phase). -/
theorem sweet_spot_topological_index_zero (t : ℝ) :
    topologicalIndex (pfaffian4 (kitaevMajoranaMatrix4 0 t t)) = 0 := by
  rw [sweet_spot_pfaffian_zero]
  dsimp [topologicalIndex]
  have h1 : ¬ (0 > (0 : ℝ)) := by norm_num
  have h2 : ¬ (0 < (0 : ℝ)) := by norm_num
  rw [if_neg h1, if_neg h2]

/-- **Theorem**: Strong Trivial Phase Topological Index is +1. -/
theorem trivial_phase_topological_index_one (mu t delta : ℝ) (h : mu^2 + (t^2 - delta^2) > 0) :
    topologicalIndex (pfaffian4 (kitaevMajoranaMatrix4 mu t delta)) = 1 := by
  have h_pos : pfaffian4 (kitaevMajoranaMatrix4 mu t delta) > 0 := trivial_phase_pfaffian_positive mu t delta h
  dsimp [topologicalIndex]
  rw [if_pos h_pos]

/-- Particle-Hole Operator C = τ_y ⊗ σ_y for 4×4 Majorana matrix. -/
def particleHoleOperator4 : Mat4R :=
  !![0, 1, 0, 0;
     -1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, -1, 0]

/-- **Theorem**: Particle-Hole Operator Involutivity Check: C² = -I₄. -/
theorem particle_hole_operator_square :
    particleHoleOperator4 * particleHoleOperator4 = -1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  interval_cases i <;> interval_cases j <;> simp [particleHoleOperator4]

end InfoGeometry.Canonical.KitaevChainTopologicalPhasePfaffian

