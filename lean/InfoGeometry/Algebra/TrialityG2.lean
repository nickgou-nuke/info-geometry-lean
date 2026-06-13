import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra

namespace InfoGeometry.Algebra.TrialityG2

/--
  Triality automorphism structure on a Lie algebra `L` over a commutative ring `K`.
  It is formalized as a Lie algebra equivalence of order 3.
-/
structure TrialityAutomorphism (K : Type*) [CommRing K] (L : Type*) [LieRing L] [LieAlgebra K L] where
  toEquiv : L ≃ₗ⁅K⁆ L
  order_three : ∀ x : L, toEquiv (toEquiv (toEquiv x)) = x

variable {K : Type*} [CommRing K] {L : Type*} [LieRing L] [LieAlgebra K L]

/--
  The invariant (fixed point) subalgebra under the triality automorphism.
  This represents the algebraic construction of g₂ from d₄.
-/
def fixedSubalgebra (σ : TrialityAutomorphism K L) : LieSubalgebra K L where
  carrier := { x | σ.toEquiv x = x }
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, hx, hy]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hx]
  lie_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [LieEquiv.map_lie, hx, hy]

/--
  A representation of the eigenspaces of the triality operator.
  This allows us to segment the d₄ algebra into cyclotomic components
  matching the ℤ₃ parafermion phase data.
-/
def TrialityEigenspace (ω : K) (σ : TrialityAutomorphism K L) : Submodule K L where
  carrier := { x | σ.toEquiv x = ω • x }
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, smul_zero]
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, hx, hy, smul_add]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hx, smul_comm]

/--
  The fundamental grading theorem: bracket interaction between eigenspaces
  follows the additive cyclic group ℤ₃.
-/
theorem eigenspace_bracket_grading 
    (σ : TrialityAutomorphism K L) 
    (ω : K) (h_omega : ω^3 = 1)
    (x y : L) 
    (hx : x ∈ TrialityEigenspace ω σ) 
    (hy : y ∈ TrialityEigenspace (ω^2) σ) :
    ⁅x, y⁆ ∈ fixedSubalgebra σ := by
  change σ.toEquiv ⁅x, y⁆ = ⁅x, y⁆
  rw [LieEquiv.map_lie]
  -- Extract eigen-equations
  have h_ex : σ.toEquiv x = ω • x := hx
  have h_ey : σ.toEquiv y = (ω^2) • y := hy
  rw [h_ex, h_ey]
  -- Use Lie bracket bilinear scaling
  rw [lie_smul, smul_lie, ← mul_smul]
  -- ω² * ω = ω³ = 1
  have h_mul : ω^2 * ω = 1 := by
    calc ω^2 * ω = ω^3 := by ring
    _ = 1 := h_omega
  rw [h_mul, one_smul]

end InfoGeometry.Algebra.TrialityG2
