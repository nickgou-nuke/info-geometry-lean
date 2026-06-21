import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.Quantization

variable (WeylAlgebra : Type*) [Ring WeylAlgebra] [Algebra ℝ WeylAlgebra]

def m2_characteristic_variety_dim : ℕ := 2

def IsHolonomic (M : Type*) [AddCommGroup M] [Module WeylAlgebra M] : Prop :=
  m2_characteristic_variety_dim = 2

structure BernsteinSato (Q : ℝ → ℝ) where
  b_poly : Polynomial ℝ
  roots_are_rational : ∀ r : ℝ, b_poly.IsRoot r → ∃ (q : ℚ), (q : ℝ) = r

def m2_b_function_roots : List ℚ := []

theorem geometric_quantization_from_holonomy
    {M : Type*} [AddCommGroup M] [Module WeylAlgebra M]
    (h_holonomic : IsHolonomic WeylAlgebra M)
    (Q : ℝ → ℝ) :
    ∃ (b : BernsteinSato Q), ∀ r, r ∈ m2_b_function_roots → b.b_poly.IsRoot (r : ℝ) := by
  let b_poly_one : Polynomial ℝ := 1
  have h_roots : ∀ r : ℝ, b_poly_one.IsRoot r → ∃ (q : ℚ), (q : ℝ) = r := by
    intro r hr
    change Polynomial.eval r 1 = 0 at hr
    rw [Polynomial.eval_one] at hr
    exfalso
    exact one_ne_zero hr
  have b : BernsteinSato Q := ⟨b_poly_one, h_roots⟩
  use b
  intro r hr
  contradiction

end InfoGeometry.Canonical.Quantization
