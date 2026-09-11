import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.ZMod.Basic
import InfoGeometry.Carrier.HestenesKrein

namespace InfoGeometry.Carrier

/-- 
The supergraded hopping structure on the binary tree. 
Operators are graded into Even (Parity 0) and Odd (Parity 1).
-/
class SupergradedHopping (A : Type*) [Ring A] where
  grade : A → ZMod 2
  -- The grading respects multiplication (Super-algebra rule)
  grade_mul : ∀ x y : A, grade (x * y) = grade x + grade y
  
  -- The Null/Nilpotent operators generating the hops MUST be in the odd sector.
  -- This forces the super-charge constraint on transitions.
  nilpotent_is_odd : ∀ {N : A}, N * N = 0 → grade N = 1

/-- 
A Tilt operator acts as a local Lorentz/Bogoliubov boost on the Krein space.
It preserves the indefinite Krein form but mixes the supergraded sectors.
-/
structure BogoliubovTilt (V : Type*) [AddCommGroup V] [Module ℝ V] [HestenesKreinSpace V] where
  tilt : V →ₗ[ℝ] V
  -- Preserves the Krein adjoint structure (Hyperbolic isometry)
  preserves_krein : ∀ u v : V, 
    HestenesKreinSpace.krein_form (tilt u) (tilt v) = HestenesKreinSpace.krein_form u v

section

variable {A : Type*} [Ring A] [SupergradedHopping A]

/-- Nilpotent elements in a supergraded setting are declared odd by design. -/
theorem odd_of_nilpotent {N : A} (hN : N * N = 0) :
    SupergradedHopping.grade N = 1 :=
  SupergradedHopping.nilpotent_is_odd hN

/-- The square of a nilpotent odd element has even superdegree. -/
theorem grade_of_nilpotent_square_zero {N : A} (hN : N * N = 0) :
    SupergradedHopping.grade (N * N) = 0 := by
  have hNodd : SupergradedHopping.grade N = 1 := odd_of_nilpotent hN
  calc
    SupergradedHopping.grade (N * N)
        = SupergradedHopping.grade N + SupergradedHopping.grade N := by
          rw [SupergradedHopping.grade_mul]
    _ = (0 : ZMod 2) := by
      rw [hNodd]
      decide

/-- Parity of products is additive in `ZMod 2`; this is the basic Koszul sign input. -/
theorem grade_mul_self (x : A) :
    SupergradedHopping.grade (x * x) = 0 := by
  calc
    SupergradedHopping.grade (x * x) = SupergradedHopping.grade x + SupergradedHopping.grade x := by
      rw [SupergradedHopping.grade_mul]
    _ = 0 := by
      have hpar : ∀ a : ZMod 2, a + a = (0 : ZMod 2) := by decide
      exact hpar (SupergradedHopping.grade x)

/-- Square parity statement in multiplicative form for algebraic rewriting. -/
theorem grade_mul_self_mul (x : A) :
    SupergradedHopping.grade (x * x) = 2 * SupergradedHopping.grade x := by
  rw [SupergradedHopping.grade_mul]
  simp [two_mul]

/-- If one factor is odd and one is even, the product is odd. -/
theorem grade_mul_eq_sum
    {x y : A} (hx : SupergradedHopping.grade x = 1) (hy : SupergradedHopping.grade y = 0) :
    SupergradedHopping.grade (x * y) = 1 := by
  rw [SupergradedHopping.grade_mul, hx, hy]
  decide

/-- The supercommuting core for even factors: even*even is even. -/
theorem grade_mul_even_even
    {x y : A} (hx : SupergradedHopping.grade x = 0) (hy : SupergradedHopping.grade y = 0) :
    SupergradedHopping.grade (x * y) = 0 := by
  rw [SupergradedHopping.grade_mul, hx, hy]
  decide

end

end InfoGeometry.Carrier
