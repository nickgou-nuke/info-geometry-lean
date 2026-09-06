import Mathlib.LinearAlgebra.BilinearForm.Basic
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

end InfoGeometry.Carrier
