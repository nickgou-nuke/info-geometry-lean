import InfoGeometry.Krein.Automorphisms
import InfoGeometry.Krein.OrthogonalGroup
import InfoGeometry.Architecture.SymmetricSpace

/-!
# Cartan Decomposition of the Krein Lie Algebra

Cartan decomposition for neutral-space endomorphisms induced by conjugation with `neutralJ`.
This version is rebased onto the current bridge surface, using `neutralJ` directly.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace
open KreinSpace NeutralSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lie subalgebra of infinitesimal isometries of the neutral Hessian form. -/
noncomputable abbrev neutralLieAlgebra
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  InfoGeometry.Krein.NeutralSpace.neutralLieSubalgebra (E := E)

section Endomorphism

private lemma neutralJ_toContinuousLinearEquiv_symm_eq :
    ((neutralJ (E := E)).toContinuousLinearEquiv).symm
      = (neutralJ (E := E)).toContinuousLinearEquiv := by
  rw [← LinearIsometryEquiv.toContinuousLinearEquiv_symm]
  rfl

/-- Cartan involution `θ(A) = J ∘ A ∘ J`. -/
noncomputable def cartanInvolution (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    NeutralSpace E →L[ℝ] NeutralSpace E :=
  conjugateCLM ((neutralJ (E := E)).toContinuousLinearEquiv) A

lemma cartanInvolution_add (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) (A + B)
      = cartanInvolution (E := E) A + cartanInvolution (E := E) B := by
  apply ContinuousLinearMap.ext
  intro x
  apply NeutralSpace.ext
  simp [cartanInvolution, conjugateCLM, conjEnd]

lemma cartanInvolution_smul (a : ℝ) (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) (a • A) = a • cartanInvolution (E := E) A := by
  apply ContinuousLinearMap.ext
  intro x
  apply NeutralSpace.ext
  simp [cartanInvolution, conjugateCLM, conjEnd]

lemma cartanInvolution_involutive (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) (cartanInvolution (E := E) A) = A := by
  apply ContinuousLinearMap.ext
  intro x
  apply NeutralSpace.ext
  simp [cartanInvolution, conjugateCLM, conjEnd,
    KreinSpace.J_invol, neutralJ_toContinuousLinearEquiv_symm_eq]

lemma cartanInvolution_comp (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) (A.comp B)
      = (cartanInvolution (E := E) A).comp (cartanInvolution (E := E) B) := by
  apply ContinuousLinearMap.ext
  intro x
  apply NeutralSpace.ext
  simp [cartanInvolution, conjugateCLM, conjEnd, ContinuousLinearMap.comp_apply]

/-- Cartan involution intertwined with the ambient Lie bracket. -/
lemma cartanInvolution_lie (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) ⁅A, B⁆
      = ⁅cartanInvolution (E := E) A, cartanInvolution (E := E) B⁆ := by
  have hmul : ∀ X Y : NeutralSpace E →L[ℝ] NeutralSpace E,
      cartanInvolution (E := E) (X * Y) =
        cartanInvolution (E := E) X * cartanInvolution (E := E) Y :=
    fun X Y => cartanInvolution_comp (E := E) X Y
  have hsub : ∀ X Y : NeutralSpace E →L[ℝ] NeutralSpace E,
      cartanInvolution (E := E) (X - Y) =
        cartanInvolution (E := E) X - cartanInvolution (E := E) Y :=
    fun X Y => by
      apply ContinuousLinearMap.ext
      intro x
      apply NeutralSpace.ext
      simp [cartanInvolution, conjugateCLM, conjEnd]
  simp only [Ring.lie_def, hsub, hmul]

end Endomorphism

section Group

/-- Group-level Cartan involution `Θ(U) = J ∘ U ∘ J` on the Hessian orthogonal group. -/
noncomputable def cartanInvolutionGroup (U : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E :=
  modular_jHessianOrthogonal * U * modular_jHessianOrthogonal

lemma modular_jHessianOrthogonal_square :
    (modular_jHessianOrthogonal (E := E)) *
        modular_jHessianOrthogonal (E := E) = 1 := by
  apply HessianOrthogonalGroup.ext
  intro x
  change neutralJ (E := E) (neutralJ (E := E) x) = x
  exact KreinSpace.J_invol x

@[simp] lemma cartanInvolutionGroup_one :
    cartanInvolutionGroup (E := E) 1 = 1 := by
  simp [cartanInvolutionGroup, modular_jHessianOrthogonal_square]

lemma cartanInvolutionGroup_mul (U V : HessianOrthogonalGroup E) :
    cartanInvolutionGroup (E := E) (U * V) =
      cartanInvolutionGroup (E := E) U *
        cartanInvolutionGroup (E := E) V := by
  simp only [cartanInvolutionGroup]
  calc
    modular_jHessianOrthogonal (E := E) * U * V *
          modular_jHessianOrthogonal (E := E) =
        modular_jHessianOrthogonal (E := E) * U *
          (modular_jHessianOrthogonal (E := E) *
            modular_jHessianOrthogonal (E := E)) * V *
          modular_jHessianOrthogonal (E := E) := by
            rw [modular_jHessianOrthogonal_square]
            simp
    _ = (modular_jHessianOrthogonal (E := E) * U *
          modular_jHessianOrthogonal (E := E)) *
        (modular_jHessianOrthogonal (E := E) * V *
          modular_jHessianOrthogonal (E := E)) := by
            simp only [mul_assoc]

@[simp] lemma cartanInvolutionGroup_involutive
    (U : HessianOrthogonalGroup E) :
    cartanInvolutionGroup (E := E)
        (cartanInvolutionGroup (E := E) U) = U := by
  simp only [cartanInvolutionGroup]
  calc
    modular_jHessianOrthogonal (E := E) *
          (modular_jHessianOrthogonal (E := E) * U *
            modular_jHessianOrthogonal (E := E)) *
          modular_jHessianOrthogonal (E := E) =
        (modular_jHessianOrthogonal (E := E) *
          modular_jHessianOrthogonal (E := E)) * U *
          (modular_jHessianOrthogonal (E := E) *
            modular_jHessianOrthogonal (E := E)) := by
              simp only [mul_assoc]
    _ = U := by
          rw [modular_jHessianOrthogonal_square]
          simp

noncomputable def cartanInvolutionGroupHom :
    HessianOrthogonalGroup E →* HessianOrthogonalGroup E where
  toFun := cartanInvolutionGroup
  map_one' := cartanInvolutionGroup_one (E := E)
  map_mul' := cartanInvolutionGroup_mul (E := E)

@[simp] lemma cartanInvolutionGroupHom_apply
    (U : HessianOrthogonalGroup E) :
    cartanInvolutionGroupHom (E := E) U =
      cartanInvolutionGroup (E := E) U :=
  rfl

lemma cartanInvolutionGroup_inv (U : HessianOrthogonalGroup E) :
    cartanInvolutionGroup (E := E) U⁻¹ =
      (cartanInvolutionGroup (E := E) U)⁻¹ := by
  exact map_inv (cartanInvolutionGroupHom (E := E)) U

lemma cartanInvolutionGroup_injective :
    Function.Injective (cartanInvolutionGroup (E := E)) := by
  intro U V h
  have h' := congrArg (cartanInvolutionGroup (E := E)) h
  simpa only [cartanInvolutionGroup_involutive] using h'

lemma cartanInvolutionGroup_surjective :
    Function.Surjective (cartanInvolutionGroup (E := E)) := by
  intro U
  refine ⟨cartanInvolutionGroup (E := E) U, ?_⟩
  exact cartanInvolutionGroup_involutive (E := E) U

noncomputable def cartanInvolutionGroupEquiv :
    HessianOrthogonalGroup E ≃* HessianOrthogonalGroup E where
  toFun := cartanInvolutionGroup (E := E)
  invFun := cartanInvolutionGroup (E := E)
  left_inv := cartanInvolutionGroup_involutive (E := E)
  right_inv := cartanInvolutionGroup_involutive (E := E)
  map_mul' := cartanInvolutionGroup_mul (E := E)

end Group

end InfoGeometry.Krein
