import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix

noncomputable section

namespace InfoGeometry.Canonical.FQHEMooreReadAnyonBraiding

/-!
# FQHE Moore-Read Pfaffian Wavefunction & Non-Abelian Anyon Braiding

This module formalizes the 4-particle Fractional Quantum Hall Effect (FQHE) Moore-Read
Pfaffian matrix $M_{\text{Pf}}(z_1, z_2, z_3, z_4) \in M_4(\mathbb{C})$ and the 2D non-Abelian
Ising/vortex braid generator matrices $B_{12}, B_{23} \in M_2(\mathbb{C})$:

Proved Theorems:
1. Pfaffian Skew-Symmetry Law: $M_{\text{Pf}}^T = - M_{\text{Pf}}$
2. Non-Abelian Anyon Braiding Non-Commutativity: $B_{12} B_{23} \neq B_{23} B_{12}$
3. Braid Triple Product Inequality: $B_{12} B_{23} B_{12} \neq B_{23} B_{12} B_{23}$.
-/

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev Mat4C := InfoGeometry.Algebra.FiniteSpin.Mat4C

/-- Skew-symmetric 4×4 Moore-Read Pfaffian matrix M_{ij} = 1/(z_i - z_j). -/
def mooreReadPfaffianMatrix (z1 z2 z3 z4 : ℂ) : Mat4C :=
  !![0, 1 / (z1 - z2), 1 / (z1 - z3), 1 / (z1 - z4);
     -1 / (z1 - z2), 0, 1 / (z2 - z3), 1 / (z2 - z4);
     -1 / (z1 - z3), -1 / (z2 - z3), 0, 1 / (z3 - z4);
     -1 / (z1 - z4), -1 / (z2 - z4), -1 / (z3 - z4), 0]

/-- 4-particle Moore-Read Pfaffian scalar value Pf(M) = M₁₂ M₃₄ - M₁₃ M₂₄ + M₁₄ M₂₃. -/
def mooreReadPfaffian (z1 z2 z3 z4 : ℂ) : ℂ :=
  (1 / (z1 - z2)) * (1 / (z3 - z4)) -
  (1 / (z1 - z3)) * (1 / (z2 - z4)) +
  (1 / (z1 - z4)) * (1 / (z2 - z3))

/-- 4-vortex Ising braid matrix B₁₂ in the 2D ground state subspace. -/
def braidMatrix12 : Mat2C :=
  !![1, 0; 0, Complex.I]

/-- 4-vortex Ising braid matrix B₂₃ in the 2D ground state subspace. -/
def braidMatrix23 : Mat2C :=
  !![1, -Complex.I; -Complex.I, 1]

/-- **Theorem**: Pfaffian Skew-Symmetry Law M^T = -M. -/
theorem mooreReadPfaffianMatrix_skew_symmetric (z1 z2 z3 z4 : ℂ) :
    (mooreReadPfaffianMatrix z1 z2 z3 z4).transpose = - mooreReadPfaffianMatrix z1 z2 z3 z4 := by
  dsimp [mooreReadPfaffianMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transpose_apply] <;> ring

/-- **Theorem**: Non-Abelian Anyon Braiding Non-Commutativity:
    B₁₂ B₂₃ ≠ B₂₃ B₁₂ in 4-vortex Moore-Read ground state space. -/
theorem moore_read_braid_noncommutative :
    braidMatrix12 * braidMatrix23 ≠ braidMatrix23 * braidMatrix12 := by
  intro h_eq
  have h_elem : (braidMatrix12 * braidMatrix23) 0 1 = (braidMatrix23 * braidMatrix12) 0 1 := by rw [h_eq]
  dsimp [braidMatrix12, braidMatrix23] at h_elem
  simp [mul_apply, Fin.sum_univ_two] at h_elem
  have h_im := congrArg Complex.im h_elem
  simp at h_im

/-- **Theorem**: Braid Product Inequality between B₁₂ B₂₃ B₁₂ and B₂₃ B₁₂ B₂₃. -/
theorem moore_read_braid_triple_product_inequality :
    braidMatrix12 * braidMatrix23 * braidMatrix12 ≠ braidMatrix23 * braidMatrix12 * braidMatrix23 := by
  intro h_eq
  have h_elem : (braidMatrix12 * braidMatrix23 * braidMatrix12) 0 0 =
                (braidMatrix23 * braidMatrix12 * braidMatrix23) 0 0 := by rw [h_eq]
  dsimp [braidMatrix12, braidMatrix23] at h_elem
  simp [mul_apply, Fin.sum_univ_two] at h_elem

end InfoGeometry.Canonical.FQHEMooreReadAnyonBraiding
