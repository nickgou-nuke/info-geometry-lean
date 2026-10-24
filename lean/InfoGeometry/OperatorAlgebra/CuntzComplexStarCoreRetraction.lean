/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitCoreRange

/-! Linear retraction through the actual equal-length core. It is not asserted
to preserve multiplication on the full quotient. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection

def coreMap : Carrier →ₗ[ℂ] core :=
  quotientAlgHom.toLinearMap.codRestrict core quotientHom_mem_core

theorem coreMap_bijective : Function.Bijective coreMap := by
  constructor
  · intro x y h
    exact quotientHom_injective (congrArg Subtype.val h)
  · intro x
    have hx : (x : ComplexStarCuntzAlg Bool) ∈ LinearMap.range quotientAlgHom.toLinearMap := by
      rw [range_quotientAlgHom]
      exact x.property
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩

def coreEquiv : Carrier ≃ₗ[ℂ] core :=
  LinearEquiv.ofBijective coreMap coreMap_bijective

@[simp] theorem coreEquiv_val (x : Carrier) :
    (coreEquiv x : ComplexStarCuntzAlg Bool) = quotientHom x := rfl

def coreRetraction : ComplexStarCuntzAlg Bool →ₗ[ℂ] Carrier :=
  coreEquiv.symm.toLinearMap.comp (projection.codRestrict core projection_mem_core)

theorem quotientHom_coreRetraction (x : ComplexStarCuntzAlg Bool) :
    quotientHom (coreRetraction x) = projection x := by
  have h := congrArg Subtype.val
    (coreEquiv.apply_symm_apply (⟨projection x, projection_mem_core x⟩ : core))
  exact h

@[simp] theorem coreRetraction_quotientHom (x : Carrier) :
    coreRetraction (quotientHom x) = x := by
  apply quotientHom_injective
  rw [quotientHom_coreRetraction, projection_eq_self_of_mem (quotientHom_mem_core x)]

@[simp] theorem coreRetraction_one : coreRetraction 1 = 1 := by
  apply quotientHom_injective
  rw [quotientHom_coreRetraction, projection_one, map_one]

theorem coreRetraction_star (x : ComplexStarCuntzAlg Bool) :
    coreRetraction (star x) = star (coreRetraction x) := by
  apply quotientHom_injective
  rw [quotientHom_coreRetraction, map_star quotientHom,
    quotientHom_coreRetraction, projection_star]

end InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding
end
