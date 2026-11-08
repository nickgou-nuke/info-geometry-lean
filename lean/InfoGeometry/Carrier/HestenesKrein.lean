import Mathlib.LinearAlgebra.BilinearForm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Carrier

/-- 
The real Bogoliubov-doubled Hestenes-Krein space.
It carries an indefinite real bilinear form representing the physical adjoint.
-/
class HestenesKreinSpace (V : Type*) [AddCommGroup V] [Module ℝ V] where
  -- The indefinite Krein metric
  krein_form : LinearMap.BilinForm ℝ V
  -- The fundamental symmetry / fundamental involution (Tomita's J)
  J : V →ₗ[ℝ] V
  J_involution : J.comp J = LinearMap.id
  
  /-- 
  The induced Hilbert inner product (krein_form v (J w)) is strictly positive-definite.
  -/
  induced_hilbert_identity : ∀ v : V, v ≠ 0 → 0 < (krein_form v (J v))

/-- A linear tilt preserving the chosen indefinite Krein form. This is a
Krein-isometry datum; it carries no supergrading assumption. -/
structure BogoliubovTilt (V : Type*) [AddCommGroup V] [Module ℝ V]
    [HestenesKreinSpace V] where
  tilt : V →ₗ[ℝ] V
  preserves_krein : ∀ u v : V,
    HestenesKreinSpace.krein_form (tilt u) (tilt v) =
      HestenesKreinSpace.krein_form u v

end InfoGeometry.Carrier
