import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# AFP CBO Riesz and adjoint adapters

This file exposes the complex Hilbert-space Riesz representation map and the
continuous adjoint (`cadjoint` in the AFP vocabulary) as Lean-native APIs.
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace RieszAdjoint

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Riesz map into the strong dual. -/
abbrev rieszMap (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    E →ₗᵢ⋆[ℂ] StrongDual ℂ E :=
  InnerProductSpace.toDualMap ℂ E

omit [CompleteSpace E] in
@[simp]
theorem rieszMap_apply_apply (x y : E) :
    rieszMap E x y = ⟪x, y⟫_ℂ :=
  InnerProductSpace.toDualMap_apply_apply (𝕜 := ℂ)

/-- Riesz representation equivalence for complete complex inner-product spaces. -/
abbrev rieszEquiv (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    E ≃ₗᵢ⋆[ℂ] StrongDual ℂ E :=
  InnerProductSpace.toDual ℂ E

omit [CompleteSpace E] in
@[simp]
theorem rieszEquiv_apply_apply [CompleteSpace E] (x y : E) :
    rieszEquiv E x y = ⟪x, y⟫_ℂ :=
  InnerProductSpace.toDual_apply_apply (𝕜 := ℂ)

omit [CompleteSpace E] in
theorem rieszEquiv_symm_apply [CompleteSpace E] (φ : StrongDual ℂ E) (x : E) :
    ⟪(rieszEquiv E).symm φ, x⟫_ℂ = φ x :=
  InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)

/-- AFP `cadjoint`, Lean-native as `ContinuousLinearMap.adjoint`. -/
abbrev cadjoint (T : E →L[ℂ] F) : F →L[ℂ] E :=
  ContinuousLinearMap.adjoint T

@[simp]
theorem cadjoint_apply (T : E →L[ℂ] F) (y : F) :
    cadjoint T y = ContinuousLinearMap.adjoint T y :=
  rfl

/-- Characterizing equation for the continuous adjoint. -/
theorem cadjoint_inner_right (T : E →L[ℂ] F) (x : E) (y : F) :
    ⟪x, cadjoint T y⟫_ℂ = ⟪T x, y⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right T x y

theorem cadjoint_inner_left (T : E →L[ℂ] F) (x : E) (y : F) :
    ⟪cadjoint T y, x⟫_ℂ = ⟪y, T x⟫_ℂ := by
  simpa [cadjoint] using ContinuousLinearMap.adjoint_inner_left T x y

@[simp]
theorem cadjoint_id :
    cadjoint (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ E :=
  ContinuousLinearMap.adjoint_id

theorem cadjoint_comp (S : F →L[ℂ] G) (T : E →L[ℂ] F) :
    cadjoint (S.comp T) = (cadjoint T).comp (cadjoint S) :=
  ContinuousLinearMap.adjoint_comp S T

@[simp]
theorem cadjoint_cadjoint (T : E →L[ℂ] F) :
    cadjoint (cadjoint T) = T := by
  simp [cadjoint]

@[simp]
theorem norm_cadjoint (T : E →L[ℂ] F) :
    ‖cadjoint T‖ = ‖T‖ := by
  simp [cadjoint, LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint T]

theorem cadjoint_eq_iff (S : E →L[ℂ] F) (T : F →L[ℂ] E) :
    S = cadjoint T ↔ ∀ x y, ⟪S x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  simpa [cadjoint] using ContinuousLinearMap.eq_adjoint_iff S T

theorem star_eq_cadjoint (T : E →L[ℂ] E) :
    star T = cadjoint T := by
  simpa [cadjoint] using ContinuousLinearMap.star_eq_adjoint T

theorem isSelfAdjoint_iff_cadjoint_eq {T : E →L[ℂ] E} :
    IsSelfAdjoint T ↔ cadjoint T = T := by
  simpa [cadjoint] using (ContinuousLinearMap.isSelfAdjoint_iff' (A := T))

theorem isSelfAdjoint.cadjoint_eq {T : E →L[ℂ] E}
    (hT : IsSelfAdjoint T) :
    cadjoint T = T := by
  simpa [cadjoint] using hT.adjoint_eq

theorem cadjoint_innerSL_apply (x : E) :
    cadjoint (innerSL ℂ x) = ContinuousLinearMap.toSpanSingleton ℂ x :=
  ContinuousLinearMap.adjoint_innerSL_apply x

theorem cadjoint_toSpanSingleton (x : E) :
    cadjoint (ContinuousLinearMap.toSpanSingleton ℂ x) = innerSL ℂ x :=
  ContinuousLinearMap.adjoint_toSpanSingleton x

end RieszAdjoint
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
