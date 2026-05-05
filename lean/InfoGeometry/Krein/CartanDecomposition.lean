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

end Group

section HessianFrameConjugation

/--
Conjugation by a Hessian-orthogonal Krein frame.

Repository interpretation: this is the real Bogoliubov frame action on
neutral-space endomorphisms.
-/
noncomputable abbrev hessianFrameConjugation
    (U : HessianOrthogonalGroup E) :
    (NeutralSpace E →L[ℝ] NeutralSpace E) ≃ₐ[ℝ]
      (NeutralSpace E →L[ℝ] NeutralSpace E) :=
  conjEnd U.equiv

@[simp] lemma hessianFrameConjugation_apply
    (U : HessianOrthogonalGroup E)
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) U A =
      conjugateCLM U.equiv A := rfl

@[simp] lemma hessianFrameConjugation_mul
    (U : HessianOrthogonalGroup E)
    (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) U (A * B)
      =
    hessianFrameConjugation (E := E) U A *
      hessianFrameConjugation (E := E) U B := by
  exact (hessianFrameConjugation (E := E) U).map_mul A B

@[simp] lemma hessianFrameConjugation_add
    (U : HessianOrthogonalGroup E)
    (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) U (A + B)
      =
    hessianFrameConjugation (E := E) U A +
      hessianFrameConjugation (E := E) U B := by
  exact (hessianFrameConjugation (E := E) U).map_add A B

@[simp] lemma hessianFrameConjugation_neg
    (U : HessianOrthogonalGroup E)
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) U (-A)
      =
    -hessianFrameConjugation (E := E) U A := by
  exact (hessianFrameConjugation (E := E) U).map_neg A

@[simp] lemma hessianFrameConjugation_one
    (U : HessianOrthogonalGroup E) :
    hessianFrameConjugation (E := E) U
      (ContinuousLinearMap.id ℝ (NeutralSpace E))
      =
    ContinuousLinearMap.id ℝ (NeutralSpace E) := by
  exact (hessianFrameConjugation (E := E) U).map_one

/--
The existing Cartan involution is exactly conjugation by the modular-J
Hessian-orthogonal frame.

This is the constructive repository statement behind:
“the Cartan diagonal frame is obtained by the real Bogoliubov/Krein frame.”
-/
theorem cartanInvolution_eq_hessianFrameConjugation_modularJ
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (E := E) A
      =
    hessianFrameConjugation (E := E)
      (modular_jHessianOrthogonal (E := E)) A := by
  rfl

/--
Frame conjugation by the modular-J Hessian frame is involutive.

This is a direct constructive consequence of the existing Cartan involution.
-/
theorem hessianFrameConjugation_modularJ_involutive
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E)
      (modular_jHessianOrthogonal (E := E))
      (hessianFrameConjugation (E := E)
        (modular_jHessianOrthogonal (E := E)) A)
      =
    A := by
  simpa [← cartanInvolution_eq_hessianFrameConjugation_modularJ]
    using cartanInvolution_involutive (E := E) A

/--
Frame conjugation by the modular-J Hessian frame preserves composition.

This is the operator-algebraic “Bogoliubov frame preserves products” lemma.
-/
theorem hessianFrameConjugation_modularJ_comp
    (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E)
      (modular_jHessianOrthogonal (E := E)) (A.comp B)
      =
    (hessianFrameConjugation (E := E)
      (modular_jHessianOrthogonal (E := E)) A).comp
    (hessianFrameConjugation (E := E)
      (modular_jHessianOrthogonal (E := E)) B) := by
  simpa [← cartanInvolution_eq_hessianFrameConjugation_modularJ]
    using cartanInvolution_comp (E := E) A B

/--
Frame conjugation by the modular-J Hessian frame preserves the Lie bracket.
-/
theorem hessianFrameConjugation_modularJ_lie
    (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E)
      (modular_jHessianOrthogonal (E := E)) ⁅A, B⁆
      =
    ⁅hessianFrameConjugation (E := E)
        (modular_jHessianOrthogonal (E := E)) A,
      hessianFrameConjugation (E := E)
        (modular_jHessianOrthogonal (E := E)) B⁆ := by
  simpa [← cartanInvolution_eq_hessianFrameConjugation_modularJ]
    using cartanInvolution_lie (E := E) A B

end HessianFrameConjugation

end InfoGeometry.Krein
