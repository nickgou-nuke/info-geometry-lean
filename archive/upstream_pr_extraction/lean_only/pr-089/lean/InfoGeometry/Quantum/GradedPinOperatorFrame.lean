import Mathlib

/-!
# Finite graded Real/Pin operator frames

This is the operator-module layer above a finite tetrad frame.  The involution
called `pinInvolution` is deliberately neutral terminology: a later consumer
may interpret it as CPT-like only after the required physical hypotheses have
been supplied.
-/

namespace InfoGeometry.Quantum.GradedPinOperatorFrame

noncomputable section

variable {S : Type*} [AddCommGroup S] [Module ℝ S]

structure Frame where
  grading : Module.End ℝ S
  pinInvolution : Module.End ℝ S
  axis : Fin 3 → Module.End ℝ S
  axisPerm : Equiv.Perm (Fin 3)
  flow : Fin 3 → ℝ → Module.End ℝ S
  grading_sq : ∀ x, grading (grading x) = x
  pin_sq : ∀ x, pinInvolution (pinInvolution x) = x
  pin_reverses_grading : ∀ x,
    pinInvolution (grading x) = -grading (pinInvolution x)
  axis_transport : ∀ a x,
    pinInvolution (axis a x) = axis (axisPerm a) (pinInvolution x)
  flow_zero : ∀ a x, flow a 0 x = x
  flow_add : ∀ a s t x, flow a (s + t) x = flow a s (flow a t x)
  pin_flow : ∀ a t x,
    pinInvolution (flow a t x) = flow (axisPerm a) (-t) (pinInvolution x)

def complexStructure (F : Frame (S := S)) : Module.End ℝ S :=
  F.grading.comp F.pinInvolution

theorem complexStructure_apply (F : Frame (S := S)) (x : S) :
    complexStructure F x = F.grading (F.pinInvolution x) :=
  rfl

theorem complexStructure_sq (F : Frame (S := S)) (x : S) :
    complexStructure F (complexStructure F x) = -x := by
  change F.grading (F.pinInvolution (F.grading (F.pinInvolution x))) = -x
  rw [F.pin_reverses_grading]
  simp [F.grading_sq, F.pin_sq]

theorem grading_complexStructure_anticommute (F : Frame (S := S)) (x : S) :
    F.grading (complexStructure F x) =
      -(complexStructure F (F.grading x)) := by
  change F.grading (F.grading (F.pinInvolution x)) =
    -(F.grading (F.pinInvolution (F.grading x)))
  rw [F.grading_sq, F.pin_reverses_grading]
  simp [F.grading_sq]

theorem pin_complexStructure_anticommute (F : Frame (S := S)) (x : S) :
    F.pinInvolution (complexStructure F x) =
      -(complexStructure F (F.pinInvolution x)) := by
  change F.pinInvolution (F.grading (F.pinInvolution x)) =
    -(F.grading (F.pinInvolution (F.pinInvolution x)))
  rw [F.pin_reverses_grading, F.pin_sq]

theorem flow_inverse_right (F : Frame (S := S)) (a : Fin 3) (t : ℝ) (x : S) :
    F.flow a t (F.flow a (-t) x) = x := by
  have h := F.flow_add a t (-t) x
  rw [add_neg_cancel t, F.flow_zero] at h
  exact h.symm

theorem flow_inverse_left (F : Frame (S := S)) (a : Fin 3) (t : ℝ) (x : S) :
    F.flow a (-t) (F.flow a t x) = x := by
  have h := F.flow_add a (-t) t x
  rw [neg_add_cancel t, F.flow_zero] at h
  exact h.symm

theorem pin_flow_inverse (F : Frame (S := S)) (a : Fin 3) (t : ℝ) (x : S) :
    F.pinInvolution (F.flow a t x) =
      F.flow (F.axisPerm a) (-t) (F.pinInvolution x) :=
  F.pin_flow a t x

end

end InfoGeometry.Quantum.GradedPinOperatorFrame
