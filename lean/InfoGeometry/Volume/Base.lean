import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic

/-!
# Multiplicative Volume Foundation

Defines the abstract multiplicative volume homomorphism interface.
The primary instantiation is the determinant on linear automorphisms.
-/

namespace Base

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
The abstract Volume Homomorphism.
Maps linear automorphisms to the scalar group of units ℝˣ.
-/
noncomputable def VolumeHom : (V ≃ₗ[ℝ] V) →* ℝˣ :=
  LinearEquiv.det

end Base
