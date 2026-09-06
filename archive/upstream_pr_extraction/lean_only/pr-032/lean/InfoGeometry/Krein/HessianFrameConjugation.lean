import InfoGeometry.Krein.CartanDecomposition

/-!
# Hessian Frame Conjugation

This file isolates the real Bogoliubov/Krein frame action from the basic Cartan
decomposition file.

The public declarations here are algebraic preservation theorems for conjugation by a
Hessian-orthogonal frame.  The definitional unfolding into `conjugateCLM` is kept as an
implementation detail rather than as a theorem-level bridge, so the file contributes
mathematical content instead of a public `rfl` alias.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace
open KreinSpace NeutralSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Conjugation by a Hessian-orthogonal Krein frame.

Repository interpretation: this is the real Bogoliubov frame action on neutral-space
endomorphisms.
-/
noncomputable abbrev hessianFrameConjugation
    (U : HessianOrthogonalGroup E) :
    (NeutralSpace E →L[ℝ] NeutralSpace E) ≃ₐ[ℝ]
      (NeutralSpace E →L[ℝ] NeutralSpace E) :=
  conjEnd U.equiv

/-
The group multiplication on `HessianOrthogonalGroup` uses composition of the
underlying frame equivalences.  Consequently conjugation by a product is the
corresponding ordered composition of the two frame conjugations.
-/
theorem hessianFrameConjugation_mul_frames
    (U V : HessianOrthogonalGroup E)
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) (U * V) A =
      hessianFrameConjugation (E := E) V
        (hessianFrameConjugation (E := E) U A) := by
  apply ContinuousLinearMap.ext
  intro x
  change
    V.equiv (U.equiv
      (A (U.equiv.symm (V.equiv.symm x)))) =
      V.equiv (U.equiv
        (A (U.equiv.symm (V.equiv.symm x))))
  rfl

theorem hessianFrameConjugation_inv_frames
    (U : HessianOrthogonalGroup E)
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
  hessianFrameConjugation (E := E) U⁻¹
        (hessianFrameConjugation (E := E) U A) = A := by
  rw [← hessianFrameConjugation_mul_frames]
  simp only [mul_inv_cancel]
  change (ContinuousLinearEquiv.refl ℝ (NeutralSpace E)).conjContinuousAlgEquiv A = A
  rfl

theorem hessianFrameConjugation_inv_frames_left
    (U : HessianOrthogonalGroup E)
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) U
        (hessianFrameConjugation (E := E) U⁻¹ A) = A := by
  rw [← hessianFrameConjugation_mul_frames]
  simp only [inv_mul_cancel]
  change (ContinuousLinearEquiv.refl ℝ (NeutralSpace E)).conjContinuousAlgEquiv A = A
  rfl

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

@[simp] lemma hessianFrameConjugation_smul
    (U : HessianOrthogonalGroup E)
    (a : ℝ)
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) U (a • A)
      =
    a • hessianFrameConjugation (E := E) U A := by
  exact (hessianFrameConjugation (E := E) U).toLinearEquiv.map_smul a A

@[simp] lemma hessianFrameConjugation_neg
    (U : HessianOrthogonalGroup E)
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) U (-A)
      =
    -hessianFrameConjugation (E := E) U A := by
  exact (hessianFrameConjugation (E := E) U).map_neg A

@[simp] lemma hessianFrameConjugation_sub
    (U : HessianOrthogonalGroup E)
    (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) U (A - B) =
      hessianFrameConjugation (E := E) U A -
        hessianFrameConjugation (E := E) U B := by
  exact (hessianFrameConjugation (E := E) U).map_sub A B

@[simp] lemma hessianFrameConjugation_lie
    (U : HessianOrthogonalGroup E)
    (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E) U ⁅A, B⁆ =
      ⁅hessianFrameConjugation (E := E) U A,
        hessianFrameConjugation (E := E) U B⁆ := by
  simp only [Ring.lie_def, hessianFrameConjugation_sub,
    hessianFrameConjugation_mul]

@[simp] lemma hessianFrameConjugation_one
    (U : HessianOrthogonalGroup E) :
    hessianFrameConjugation (E := E) U
      (ContinuousLinearMap.id ℝ (NeutralSpace E))
      =
    ContinuousLinearMap.id ℝ (NeutralSpace E) := by
  exact (hessianFrameConjugation (E := E) U).map_one

/--
Frame conjugation by the modular-J Hessian frame is involutive.

This is a constructive consequence of the existing Cartan involution theorem, not an
uninterpreted property field.
-/
theorem hessianFrameConjugation_modularJ_involutive
    (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    hessianFrameConjugation (E := E)
      (modular_jHessianOrthogonal (E := E))
      (hessianFrameConjugation (E := E)
        (modular_jHessianOrthogonal (E := E)) A)
      =
    A := by
  simpa [hessianFrameConjugation, cartanInvolution]
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
  simpa [hessianFrameConjugation, cartanInvolution]
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
  simpa [hessianFrameConjugation, cartanInvolution]
    using cartanInvolution_lie (E := E) A B

end InfoGeometry.Krein
