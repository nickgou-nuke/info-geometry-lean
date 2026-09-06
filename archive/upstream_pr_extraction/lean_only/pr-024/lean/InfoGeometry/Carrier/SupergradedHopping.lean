import Mathlib.Algebra.Ring.Basic
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

end InfoGeometry.Carrier
