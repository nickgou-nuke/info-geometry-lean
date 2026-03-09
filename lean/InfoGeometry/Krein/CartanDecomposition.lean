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
  ext x
  simp [neutralJ, KreinSpace.J_invol]

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
  simp [Ring.lie_def, cartanInvolution_comp, cartanInvolution_add,
    cartanInvolution_smul, sub_eq_add_neg]

end Endomorphism

section Group

/-- Group-level Cartan involution `Θ(U) = J ∘ U ∘ J` on the Hessian orthogonal group. -/
noncomputable def cartanInvolutionGroup (U : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E where
  equiv := (neutralJ (E := E)).trans (U.equiv.trans (neutralJ (E := E)))
  is_isometry := by
    intro u v
    have hJ :
        KreinSpace.IsKreinIsometry
          (((neutralJ (E := E)).toContinuousLinearEquiv.toContinuousLinearMap)
            : NeutralSpace E →L[ℝ] NeutralSpace E) := by
      simpa [neutralJ] using KreinSpace.IsKreinIsometry.J (H := NeutralSpace E)
    calc
      KreinSpace.kreinInner
          ((neutralJ (E := E)) (U.equiv ((neutralJ (E := E)) u)))
          ((neutralJ (E := E)) (U.equiv ((neutralJ (E := E)) v)))
          = KreinSpace.kreinInner
              (U.equiv ((neutralJ (E := E)) u))
              (U.equiv ((neutralJ (E := E)) v)) := by
            simpa [neutralJ] using hJ _ _
        _ = KreinSpace.kreinInner ((neutralJ (E := E)) u) ((neutralJ (E := E)) v) := by
          exact U.is_isometry _ _
      _ = KreinSpace.kreinInner u v := by
          simpa [neutralJ] using hJ _ _

end Group

end InfoGeometry.Krein
