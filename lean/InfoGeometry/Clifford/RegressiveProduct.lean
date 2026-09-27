import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

universe u v

namespace InfoGeometry.Grassmann

variable (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]

/-- A Typeclass providing a Hodge star isomorphism on the exterior algebra. -/
class HasHodgeStar (R : Type u) (V : Type v) [CommRing R] [AddCommGroup V] [Module R V] where
  star : ExteriorAlgebra R V ≃ₗ[R] ExteriorAlgebra R V
  star_inv : ExteriorAlgebra R V ≃ₗ[R] ExteriorAlgebra R V
  inv_star_cancel : ∀ x, star_inv (star x) = x
  star_inv_cancel : ∀ x, star (star_inv x) = x

/-- 
The Regressive Product (meet/join) `∨` as defined by DeMorgan's law:
A ∨ B = ⋆⁻¹(⋆A ∧ ⋆B)
-/
def regressiveProduct [HasHodgeStar R V] : 
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V where
  toFun A := {
    toFun := fun B => 
      HasHodgeStar.star_inv (HasHodgeStar.star A * HasHodgeStar.star B)
    map_add' := by 
      intro x y
      simp only [map_add, mul_add]
    map_smul' := by 
      intro r x
      simp only [LinearEquiv.map_smul, mul_smul_comm, RingHom.id_apply]
  }
  map_add' := by 
    intro x y
    ext B
    simp only [map_add, add_mul, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  map_smul' := by 
    intro r x
    ext B
    simp only [LinearEquiv.map_smul, smul_mul_assoc, LinearMap.smul_apply, 
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]

end InfoGeometry.Grassmann
