/- Polar Decomposition via Newton-Schulz Iteration -/
/- The Newton-Schulz iteration computes the unitary factor U = msign(G) of the polar decomposition
   G = P * U without requiring a full SVD. Uses only matrix addition, transposition, and inversion. -/

import Mathlib.Data.Matrix.Basic
import InfoGeometry.Singular.MoorePenrose

open Matrix
open scoped Matrix

namespace InfoGeometry.Optimization

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One step of the generalized Newton-Schulz iteration for Polar Decomposition. -/
noncomputable def PolarNewtonStep (X X_inv : Matrix n n ℝ) : Matrix n n ℝ :=
  (1/2 : ℝ) • (X + X_invᵀ)

/-- The formal structure of the Polar Decomposition G = P * U -/
structure PolarDecomposition (G : Matrix n n ℝ) where
  U : Matrix n n ℝ  -- The unitary factor (msign(G))
  P : Matrix n n ℝ  -- The positive semidefinite factor
  decomp : G = P * U
  unitary : U * Uᵀ = 1
  self_adjoint : Pᵀ = P

/-- 
  If the Newton iteration converges to a fixed point U, U must be orthogonal.
  X_{k+1} = X_k ⟹ U = 1/2(U + U^{-T}) ⟹ U = U^{-T} ⟹ U * Uᵀ = I.
-/
theorem polar_newton_limit_unitary (U U_inv : Matrix n n ℝ) 
    (h_inv : U * U_inv = 1) (h_fixed : PolarNewtonStep U U_inv = U) : 
    U * Uᵀ = 1 := by
  dsimp [PolarNewtonStep] at h_fixed
  have h₁ : (1/2 : ℝ) • (U + U_invᵀ) = U := h_fixed
  have h₂ : U + U_invᵀ = 2 • U := by
    rw [← sub_eq_zero, smul_smul] at h₁
    simp [two_smul] at h₁ ⊢
    <;>
    (try simp_all [Matrix.ext_iff]) <;>
    (try abel_nf at * <;> simp_all [Matrix.ext_iff]) <;>
    (try linarith)
  have h₃ : U_invᵀ = U := by
    have h₄ : U + U_invᵀ = U + U := by
      calc
        U + U_invᵀ = 2 • U := h₂
        _ = U + U := by simp [two_smul]
    have h₅ : U_invᵀ = U := by
      apply_fun (fun X => X - U) h₄
      <;> simp [sub_self, add_comm]
      <;> abel
    exact h₅
  calc
    U * Uᵀ = U * U_inv := by rw [h₃]
    _ = 1 := h_inv

end InfoGeometry.Optimization