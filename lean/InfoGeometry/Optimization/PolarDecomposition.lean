/- Polar Decomposition via Newton-Schulz Iteration -/
/- The Newton-Schulz iteration computes the unitary factor U = msign(G) of the polar decomposition
   G = P * U without requiring a full SVD. Uses only matrix addition, transposition, and inversion. -/

import Mathlib.Tactic

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
  have h_transpose_inv : Uᵀ = U_inv := by
    ext i j
    have hij := congrFun (congrFun h_fixed j) i
    simp [PolarNewtonStep] at hij
    have hij₂ : U j i + U_inv i j = 2 * U j i := by
      have hmul := congrArg (fun x : ℝ => (2 : ℝ) * x) hij
      norm_num [mul_add, mul_assoc] at hmul
      simpa [two_mul] using hmul
    simpa using (by linarith : U j i = U_inv i j)
  calc
    U * Uᵀ = U * U_inv := by rw [h_transpose_inv]
    _ = 1 := h_inv

end InfoGeometry.Optimization
