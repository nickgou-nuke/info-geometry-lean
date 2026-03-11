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
  ext x
  simp [cartanInvolution, conjugateCLM, conjEnd]

lemma cartanInvolution_smul (a : ℝ) (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) (a • A) = a • cartanInvolution (E := E) A := by
  ext x
  simp [cartanInvolution, conjugateCLM, conjEnd]

lemma cartanInvolution_involutive (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) (cartanInvolution (E := E) A) = A := by
  ext x
  simp [cartanInvolution, conjugateCLM, conjEnd,
    KreinSpace.J_invol, neutralJ_toContinuousLinearEquiv_symm_eq]

lemma cartanInvolution_comp (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) (A.comp B)
      = (cartanInvolution (E := E) A).comp (cartanInvolution (E := E) B) := by
  ext x
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
    fun X Y => by ext x; simp [cartanInvolution, conjugateCLM, conjEnd]
  simp only [Ring.lie_def, hsub, hmul]

end Endomorphism

section Group

/-- Group-level Cartan involution `Θ(U) = J ∘ U ∘ J` on the Hessian orthogonal group. -/
noncomputable def cartanInvolutionGroup (U : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E :=
  modular_jHessianOrthogonal * U * modular_jHessianOrthogonal

end Group

end InfoGeometry.Krein
