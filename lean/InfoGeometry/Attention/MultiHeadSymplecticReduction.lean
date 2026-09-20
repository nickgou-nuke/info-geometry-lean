import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Attention.MetriplecticAttentionDynamics

namespace InfoGeometry.Attention.MultiHeadSymplecticReduction

open Matrix
open InfoGeometry.Attention.MetriplecticAttentionDynamics

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-!
# Archetype 907: Multi-Head Symplectic Reduction and Infinitesimal Symplectic Gating

This module proves that the chiral bipolar attention channel and the Dirac grading
operator both belong to the infinitesimal symplectic Lie algebra 𝔰𝔭(2, ℝ), preserving
the canonical symplectic structure J = !![0, 1; -1, 0].
-/

/-- The standard canonical symplectic matrix J on ℝ²: J² = -1. -/
def J_symp : Mat2R :=
  !![ 0, 1;
     -1, 0]

/-- The symplectic Lie algebra condition: Kᵀ * J + J * K = 0. -/
def is_infinitesimal_symplectic (K : Mat2R) : Prop :=
  Kᵀ * J_symp + J_symp * K = 0

/-- Master Theorem 1: J is a complex structure: J² = -1. -/
theorem J_symp_sq : J_symp * J_symp = - (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [J_symp, Matrix.mul_apply]
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
    simp [Matrix.one_apply]
    ring
  }

/-- Master Theorem 2: J is skew-symmetric: Jᵀ = -J. -/
theorem J_symp_skew : J_sympᵀ = - J_symp := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [J_symp]
    simp only [cons_val_zero, cons_val_one, head_cons, transpose_apply]
    ring
  }

/-- Master Theorem 3: The Dirac grading G is an infinitesimal symplectic generator.
    Gᵀ * J + J * G = 0. -/
theorem G_is_infinitesimal_symplectic : is_infinitesimal_symplectic G_grading := by
  dsimp [is_infinitesimal_symplectic, G_grading, J_symp, Matrix.mul_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons, transpose_apply]
    ring
  }

/-- Master Theorem 4: Balanced symmetric cross-attention is infinitesimal symplectic.
    When M₀₁ = M₁₀, the chiral bipolar operator satisfies C(M)ᵀ * J + J * C(M) = 0. -/
theorem chiral_bipolar_is_infinitesimal_symplectic (M : Mat2R)
    (h_symm : M 0 1 = M 1 0) :
    is_infinitesimal_symplectic (chiral_bipolar M) := by
  dsimp [is_infinitesimal_symplectic, chiral_bipolar, J_symp, Matrix.mul_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons, transpose_apply]
    rw [h_symm]
    ring
  }

/-- Master Theorem 5: The total Dirac Hamiltonian H = p • G + C(M) is infinitesimal symplectic.
    It preserves the canonical symplectic form on the latent phase space. -/
theorem dirac_hamiltonian_is_infinitesimal_symplectic (M : Mat2R) (p : ℝ)
    (h_symm : M 0 1 = M 1 0) :
    is_infinitesimal_symplectic (p • G_grading + chiral_bipolar M) := by
  dsimp [is_infinitesimal_symplectic]
  have hG := G_is_infinitesimal_symplectic
  have hC := chiral_bipolar_is_infinitesimal_symplectic M h_symm
  dsimp [is_infinitesimal_symplectic] at hG hC
  calc (p • G_grading + chiral_bipolar M)ᵀ * J_symp + J_symp * (p • G_grading + chiral_bipolar M)
      = (p • G_gradingᵀ + (chiral_bipolar M)ᵀ) * J_symp + (J_symp * (p • G_grading) + J_symp * chiral_bipolar M) := by
        simp only [transpose_add, transpose_smul, mul_add]
    _ = (p • (G_gradingᵀ * J_symp) + (chiral_bipolar M)ᵀ * J_symp) +
        (p • (J_symp * G_grading) + J_symp * chiral_bipolar M) := by
        simp only [add_mul, smul_mul, mul_smul]
    _ = p • (G_gradingᵀ * J_symp + J_symp * G_grading) +
        ((chiral_bipolar M)ᵀ * J_symp + J_symp * chiral_bipolar M) := by
        simp only [smul_add]
        abel
    _ = p • (0 : Mat2R) + 0 := by rw [hG, hC]
    _ = 0 := by simp

end InfoGeometry.Attention.MultiHeadSymplecticReduction
