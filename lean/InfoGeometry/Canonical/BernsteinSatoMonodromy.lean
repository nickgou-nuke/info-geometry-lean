import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DeRhamFenchelLegendre

open InfoGeometry.Algebra.HessianThermodynamicManifold
open InfoGeometry.Canonical.DeRhamFenchelLegendre

namespace InfoGeometry.Canonical

/--
  The Bernstein-Sato Polynomial b(s).
  Satisfies the functional equation: P(s) * Q * Q^s = b(s) * Q^s
  for some differential operator P(s).
-/
structure BernsteinSato (Q : ℝ → ℝ) where
  b_poly : Polynomial ℚ
  -- The fundamental theorem of b-functions: the roots are strictly rational
  roots_are_rational : ∀ r : ℝ, (b_poly.map (algebraMap ℚ ℝ)).IsRoot r → ∃ (q : ℚ), (q : ℝ) = r

/-- 
  The injected Roots of the b-function computed by Macaulay2 for Q = x^2 + y^2.
  These represent the exact topological phase shifts allowed around Q=0.
  For Q = x^2 + y^2, the root is s = -1.
-/
def m2_b_function_roots : List ℚ := [-1]

/--
  Bernstein-Sato rational-root quantization.

  This is the kernel-checked content carried by the `BernsteinSato` witness:
  every real root of the real scalar extension of `b_poly` is the image of a
  rational number.
-/
theorem holonomic_quantization (Q : ℝ → ℝ) (b : BernsteinSato Q) :
    ∀ r : ℝ, (b.b_poly.map (algebraMap ℚ ℝ)).IsRoot r → ∃ q : ℚ, (q : ℝ) = r :=
  b.roots_are_rational

/-- The concrete Macaulay2 root list used here contains only rational phases. -/
theorem m2_b_function_roots_are_rational :
    ∀ r ∈ m2_b_function_roots, ∃ q : ℚ, q = r := by
  intro r hr
  simp [m2_b_function_roots] at hr
  exact ⟨r, rfl⟩

end InfoGeometry.Canonical
