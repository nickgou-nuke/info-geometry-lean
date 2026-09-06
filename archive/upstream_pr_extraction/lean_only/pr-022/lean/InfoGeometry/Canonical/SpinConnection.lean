import InfoGeometry.Canonical.Krein
import Mathlib.Algebra.Lie.OfAssociative

open scoped InnerProductSpace

namespace InfoGeometry.Canonical

open InfoGeometry.Krein
open InfoGeometry.Krein.NeutralSpace

/--
Minimal spin-transport datum: a one-parameter family of neutral isometries.
This is a group-valued flow in the Hessian orthogonal group.
-/
structure SpinConnection (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  U : ℝ → HessianOrthogonalGroup E
  U_zero : U 0 = 1
  U_add : ∀ s t, U (s + t) = U s * U t

section

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Conjugation transport of endomorphisms along a spin connection. -/
noncomputable def transportEnd (S : SpinConnection E) (t : ℝ) :
    (NeutralSpace E →L[ℝ] NeutralSpace E) → (NeutralSpace E →L[ℝ] NeutralSpace E) :=
  fun A => conjugateCLM (U := (S.U t : NeutralSpace E ≃L[ℝ] NeutralSpace E)) A

@[simp] lemma transportEnd_add (S : SpinConnection E) (t : ℝ)
    (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    transportEnd S t (A + B) = transportEnd S t A + transportEnd S t B := by
  unfold transportEnd
  exact conjugateCLM_add
    (U := (S.U t : NeutralSpace E ≃L[ℝ] NeutralSpace E)) A B

@[simp] lemma transportEnd_zero (S : SpinConnection E) (t : ℝ) :
    transportEnd S t (0 : NeutralSpace E →L[ℝ] NeutralSpace E) = 0 := by
  unfold transportEnd
  exact conjugateCLM_zero
    (U := (S.U t : NeutralSpace E ≃L[ℝ] NeutralSpace E))

@[simp] lemma transportEnd_smul (S : SpinConnection E) (t : ℝ)
    (a : ℝ) (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    transportEnd S t (a • A) = a • transportEnd S t A := by
  unfold transportEnd
  exact conjugateCLM_smul
    (U := (S.U t : NeutralSpace E ≃L[ℝ] NeutralSpace E)) a A

@[simp] lemma transportEnd_mul (S : SpinConnection E) (t : ℝ)
    (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    transportEnd S t (A * B) = transportEnd S t A * transportEnd S t B := by
  unfold transportEnd
  exact conjugateCLM_mul
    (U := (S.U t : NeutralSpace E ≃L[ℝ] NeutralSpace E)) A B

@[simp] lemma transportEnd_lie (S : SpinConnection E) (t : ℝ)
    (A B : NeutralSpace E →L[ℝ] NeutralSpace E) :
    transportEnd S t ⁅A, B⁆ = ⁅transportEnd S t A, transportEnd S t B⁆ := by
  simp [Ring.lie_def, transportEnd]

end

end InfoGeometry.Canonical
