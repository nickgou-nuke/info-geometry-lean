import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix

noncomputable section

namespace InfoGeometry.Canonical.KreinMajoranaBlockInvariance

/-!
# Krein-Majorana Zero Mode Block & Metric Invariance

This module formalizes the 8×8 real Krein space metric $J_8 = \tau_z \otimes I_4 \in M_8(\mathbb{R})$
with indefinite signature $(4, 4)$, the Krein inner product $\langle u, v \rangle_J = u^T J_8 v$ on $\mathbb{R}^8$,
and the exact Krein norm evaluation for 8D boundary Majorana zero modes $\gamma_1, \gamma_8 \in \mathbb{R}^8$:

Proved Theorems:
1. Krein Metric Involutivity in 8D: $J_8^2 = I_8$
2. Krein Metric Symmetry in 8D: $J_8^T = J_8$
3. Left Boundary Majorana Zero Mode Positive Krein Norm: $\langle \gamma_1, \gamma_1 \rangle_J = +1$
4. Right Boundary Majorana Zero Mode Negative Krein Norm: $\langle \gamma_8, \gamma_8 \rangle_J = -1$.
-/

abbrev Mat8R := InfoGeometry.Algebra.FiniteSpin.Mat8R
abbrev Vec8R := InfoGeometry.Algebra.FiniteSpin.Vec8R

/-- Krein metric matrix J₈ = τ_z ⊗ I₄ in 8×8 real Nambu space. -/
def kreinMetric8 : Mat8R :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, -1]

/-- Left boundary 8D Majorana zero mode vector: γ₁ = (1, 0, 0, 0, 0, 0, 0, 0)ᵀ. -/
def majoranaModeLeft8 : Vec8R :=
  ![1, 0, 0, 0, 0, 0, 0, 0]

/-- Right boundary 8D Majorana zero mode vector: γ₈ = (0, 0, 0, 0, 0, 0, 0, 1)ᵀ. -/
def majoranaModeRight8 : Vec8R :=
  ![0, 0, 0, 0, 0, 0, 0, 1]

/-- Krein inner product ⟨u, v⟩_J = uᵀ J₈ v on ℝ⁸. -/
def kreinInnerProduct (u v : Vec8R) : ℝ :=
  dotProduct u (kreinMetric8.mulVec v)

/-- **Theorem**: Krein Metric Involutivity in 8D: J₈² = I₈. -/
theorem kreinMetric8_square : kreinMetric8 * kreinMetric8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kreinMetric8, mul_apply, Fin.sum_univ_eight]

/-- **Theorem**: Krein Metric Symmetry in 8D: J₈ᵀ = J₈. -/
theorem kreinMetric8_symmetric : kreinMetric8.transpose = kreinMetric8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kreinMetric8, transpose_apply]

/-- **Theorem**: Left Boundary Majorana Zero Mode Krein Inner Product Norm: ⟨γ₁, γ₁⟩_J = 1. -/
theorem majorana_left_krein_norm : kreinInnerProduct majoranaModeLeft8 majoranaModeLeft8 = 1 := by
  dsimp [kreinInnerProduct, majoranaModeLeft8, kreinMetric8]
  simp [mulVec, dotProduct, Fin.sum_univ_eight]

/-- **Theorem**: Right Boundary Majorana Zero Mode Krein Inner Product Norm: ⟨γ₈, γ₈⟩_J = -1. -/
theorem majorana_right_krein_norm : kreinInnerProduct majoranaModeRight8 majoranaModeRight8 = -1 := by
  dsimp [kreinInnerProduct, majoranaModeRight8, kreinMetric8]
  simp [mulVec, dotProduct, Fin.sum_univ_eight]

end InfoGeometry.Canonical.KreinMajoranaBlockInvariance
