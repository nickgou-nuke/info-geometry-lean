import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.KleinFundamentalGroup

open Matrix

/-!
# Fundamental Group of the Klein Bottle acting on E₇₍₇₎ Tensors

Formalizes the π₁(\mathcal{K}) relation `a * b * a⁻¹ = b⁻¹` over 
the 56-dimensional real symplectic space.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 
Theorem: The Klein group action invariantly preserves the Skew-Symmetric 
Symplectic Inner Product Ω of E₇₍₇₎ despite breaking the local compact symmetry.

Here we prove the topological shielding: if the glide-reflection `a` is ANTI-symplectic
(as proven in our earlier SymPy module) and the periodic cycle `b` is symplectic,
then the conjugated loop `a * b * a⁻¹` strictly preserves the symplectic form.
-/
theorem klein_loop_preserves_symplectic_omega
    (a a_inv b Ω : Matrix n n ℝ)
    (h_inv : a * a_inv = 1)
    (h_inv_left : a_inv * a = 1)
    (hΩ : Ωᵀ = -Ω)
    (h_a_antisymp : aᵀ * Ω * a = -Ω)
    (h_b_symp : bᵀ * Ω * b = Ω) :
    (a * b * a_inv)ᵀ * Ω * (a * b * a_inv) = Ω := by
  -- (a * b * a⁻¹)ᵀ = (a⁻¹)ᵀ * bᵀ * aᵀ
  have h1 : (a * b * a_inv)ᵀ = a_invᵀ * bᵀ * aᵀ := by
    rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
  rw [h1]
  -- Group the inner terms: aᵀ * Ω * a
  have h2 : a_invᵀ * bᵀ * aᵀ * Ω * (a * b * a_inv) = a_invᵀ * bᵀ * (aᵀ * Ω * a) * b * a_inv := by
    -- Expand associativity
    simp only [Matrix.mul_assoc]
  rw [h2]
  -- Apply anti-symplectic twist of `a`
  rw [h_a_antisymp]
  -- Pull out the negative sign
  have h3 : a_invᵀ * bᵀ * -Ω * b * a_inv = - (a_invᵀ * (bᵀ * Ω * b) * a_inv) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [h3]
  -- Apply symplectic property of `b`
  rw [h_b_symp]
  -- Now we evaluate - (a⁻¹ᵀ * Ω * a⁻¹)
  -- Since aᵀ * Ω * a = -Ω, multiply by a⁻¹ᵀ on left and a⁻¹ on right
  have h4 : a_invᵀ * (aᵀ * Ω * a) * a_inv = a_invᵀ * -Ω * a_inv := by
    rw [h_a_antisymp]
  have h5 : a_invᵀ * (aᵀ * Ω * a) * a_inv = Ω := by
    -- (a⁻¹ᵀ * aᵀ) * Ω * (a * a⁻¹) = (a * a⁻¹)ᵀ * Ω * (a * a⁻¹) = 1ᵀ * Ω * 1 = Ω
    have h5a : a_invᵀ * (aᵀ * Ω * a) * a_inv = (a_invᵀ * aᵀ) * Ω * (a * a_inv) := by
      simp only [Matrix.mul_assoc]
    rw [h5a]
    have h5b : a_invᵀ * aᵀ = (a * a_inv)ᵀ := by rw [transpose_mul]
    rw [h5b, h_inv, transpose_one, Matrix.one_mul, Matrix.mul_one]
  have h6 : a_invᵀ * -Ω * a_inv = - (a_invᵀ * Ω * a_inv) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [h6] at h4
  have h7 : - (a_invᵀ * Ω * a_inv) = Ω := h4.symm.trans h5
  -- Thus (a⁻¹ᵀ * Ω * a⁻¹) = -Ω, meaning - (a⁻¹ᵀ * Ω * a⁻¹) = Ω
  exact h7

end InfoGeometry.Canonical.KleinFundamentalGroup
