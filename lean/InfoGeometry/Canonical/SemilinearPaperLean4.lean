import Mathlib

/-!
# Lean 4 / mathlib4 surface for semilinear-map paper snippets
-/

noncomputable section

namespace SemilinearPaperLean4

universe u v w

section LinearMapExamples

variable (R : Type u) (M₁ : Type v) (M₂ : Type w)
variable [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M₁] [Module R M₂]

#check LinearMap
#check (M₁ →ₗ[R] M₂)
#check (M₁ →ₛₗ[(RingHom.id R)] M₂)

example : M₁ →ₗ[R] M₂ :=
{ toFun := fun _ => 0
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro c x
    simp }

#check LinearEquiv
#check (M₁ ≃ₗ[R] M₁)

end LinearMapExamples

section SemilinearMapExamples

variable {R S : Type*} [Semiring R] [Semiring S]
variable (σ : R →+* S)
variable (M₁ M₂ : Type*) [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M₁] [Module S M₂]

#check (M₁ →ₛₗ[σ] M₂)

example : M₁ →ₛₗ[σ] M₂ :=
{ toFun := fun _ => 0
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro c x
    simp }

end SemilinearMapExamples

section SemilinearEquivExamples

variable {R S : Type*} [Semiring R] [Semiring S]
variable (σ : R →+* S) (τ : S →+* R)
variable [RingHomInvPair σ τ] [RingHomInvPair τ σ]
variable (M₁ M₂ : Type*) [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M₁] [Module S M₂]

#check LinearEquiv
#check (M₁ ≃ₛₗ[σ] M₂)

end SemilinearEquivExamples

section RingHomComp

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable (σ₁₂ : R₁ →+* R₂) (σ₂₃ : R₂ →+* R₃) (σ₁₃ : R₁ →+* R₃)

#check RingHomCompTriple
#check RingHomInvPair
#check RingHomSurjective

example {σ₁₂ : R₁ →+* R₂} :
    RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂ :=
  inferInstance

example : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁) :=
  inferInstance

variable {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

example (g : M₂ →ₛₗ[σ₂₃] M₃) (f : M₁ →ₛₗ[σ₁₂] M₂) :
    M₁ →ₛₗ[σ₁₃] M₃ :=
  g.comp f

end RingHomComp

section HilbertSpaceContext

variable {𝕜 E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

#check RCLike
#check HilbertSpace
#check InnerProductSpace
#check (inner 𝕜)

end HilbertSpaceContext

section FrechetRiesz

variable {𝕜 E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

#check InnerProductSpace.toDual
#check InnerProductSpace.toDual_apply_apply
#check StrongDual

example (x y : E) :
    ((InnerProductSpace.toDual 𝕜 E) x) y = inner 𝕜 x y :=
  InnerProductSpace.toDual_apply_apply

end FrechetRiesz

section Adjoint

variable {𝕜 E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
variable [CompleteSpace E] [CompleteSpace F]

#check ContinuousLinearMap.adjoint
#check ContinuousLinearMap.adjoint_inner_left
#check ContinuousLinearMap.adjoint_inner_right
#check ContinuousLinearMap.adjoint_adjoint
#check ContinuousLinearMap.adjoint_comp

example (A : E →L[𝕜] F) (x : E) (y : F) :
    inner 𝕜 ((ContinuousLinearMap.adjoint A) y) x = inner 𝕜 y (A x) :=
  ContinuousLinearMap.adjoint_inner_left A x y

#check IsSelfAdjoint
#check IsStarNormal

end Adjoint

section AnalysisChecks

#check PiLp
#check lp
#check Memℓp
#check OrthogonalFamily.linearIsometry
#check IsHilbertSum
#check IsHilbertSum.linearIsometryEquiv
#check IsCompactOperator
#check LinearMap.IsSymmetric.diagonalization
#check LinearMap.IsSymmetric.diagonalization_apply_self_apply

end AnalysisChecks

section IsocrystalChecks

#check WittVector.frobenius
#check WittVector.coeff_frobenius_charP
#check WittVector.Isocrystal
#check WittVector.FractionRing.frobeniusRingHom
#check WittVector.Isocrystal.frobenius
#check WittVector.isocrystal_classification

end IsocrystalChecks

end SemilinearPaperLean4
