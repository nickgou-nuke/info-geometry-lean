import InfoGeometry.Krein.Automorphisms
import InfoGeometry.Krein.OrthogonalGroup
import InfoGeometry.Architecture.SymmetricSpace

/-!
# Cartan Decomposition of the Krein Lie Algebra

Cartan decomposition for neutral-space endomorphisms induced by conjugation with `neutralJ`.
Uses the hardened `NeutralSpace` newtype and centralized conjugation.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace
open KreinSpace NeutralSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lie subalgebra of infinitesimal isometries of the neutral Hessian form. -/
noncomputable abbrev neutralLieAlgebra (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  neutralLieSubalgebra (E := E)

section Endomorphism

private lemma neutralJ_symm_eq : (neutralJ (E := E)).symm = neutralJ (E := E) := by
  apply LinearIsometryEquiv.ext
  intro x
  apply (neutralJ (E := E)).injective
  rw [(neutralJ (E := E)).apply_symm_apply, neutralJ_invol (E := E) x]

/-- Cartan involution `θ(A) = J ∘ A ∘ J`. -/
noncomputable def cartanInvolution (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    NeutralSpace E →L[ℝ] NeutralSpace E :=
  conjugateCLM (neutralJEquiv (E := E)) A

lemma cartanInvolution_add (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (A + B) = cartanInvolution A + cartanInvolution B :=
  conjugateCLM_add _ _ _

lemma cartanInvolution_smul (a : ℝ) (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (a • A) = a • cartanInvolution A := by
  ext x
  simp [cartanInvolution, conjugateCLM, conjEnd]

lemma cartanInvolution_involutive (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (cartanInvolution A) = A := by
  ext x
  simp [cartanInvolution, conjugateCLM, conjEnd, neutralJEquiv, neutralJ_invol, neutralJ_symm_eq]

lemma cartanInvolution_comp (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution (A.comp B) = (cartanInvolution A).comp (cartanInvolution B) :=
  conjugateCLM_mul _ _ _

/-- Cartan involution intertwined with the ambient Lie bracket. -/
lemma cartanInvolution_lie (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    cartanInvolution ⁅A, B⁆ = ⁅cartanInvolution A, cartanInvolution B⁆ := by
  simp [Ring.lie_def, cartanInvolution, conjugateCLM, conjEnd]

end Endomorphism

section Group

/-- Group-level Cartan involution `Θ(U) = J ∘ U ∘ J` on the Hessian orthogonal group. -/
noncomputable def cartanInvolutionGroup (U : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E where
  equiv := neutralJEquiv.trans (U.equiv.trans neutralJEquiv)
  is_isometry := by
    intro u v
    have hJ : KreinSpace.IsKreinIsometry
        ((KreinSpace.J (H := NeutralSpace E)) : NeutralSpace E →L[ℝ] NeutralSpace E) :=
      KreinSpace.IsKreinIsometry.J (H := NeutralSpace E)
    change KreinSpace.kreinInner
        ((KreinSpace.J (H := NeutralSpace E)) (U.equiv ((KreinSpace.J (H := NeutralSpace E)) u)))
        ((KreinSpace.J (H := NeutralSpace E)) (U.equiv ((KreinSpace.J (H := NeutralSpace E)) v)))
        = KreinSpace.kreinInner u v
    calc
      KreinSpace.kreinInner
          ((KreinSpace.J (H := NeutralSpace E)) (U.equiv ((KreinSpace.J (H := NeutralSpace E)) u)))
          ((KreinSpace.J (H := NeutralSpace E)) (U.equiv ((KreinSpace.J (H := NeutralSpace E)) v)))
          = KreinSpace.kreinInner (U.equiv ((KreinSpace.J (H := NeutralSpace E)) u))
              (U.equiv ((KreinSpace.J (H := NeutralSpace E)) v)) :=
        hJ _ _
      _ = KreinSpace.kreinInner ((KreinSpace.J (H := NeutralSpace E)) u)
            ((KreinSpace.J (H := NeutralSpace E)) v) :=
        U.is_isometry _ _
      _ = KreinSpace.kreinInner u v := hJ _ _

end Group

end InfoGeometry.Krein
