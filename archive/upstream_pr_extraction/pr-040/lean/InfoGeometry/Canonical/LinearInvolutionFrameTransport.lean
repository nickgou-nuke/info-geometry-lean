import Mathlib

/-!
# Transport of linear involutions between frame carriers

An involution can be moved between carriers only after a linear equivalence is
supplied.  This is the precise algebraic seam used by frame/Bogoliubov
transport; no multiplicative or complex structure is inferred from it.
-/

namespace InfoGeometry.Canonical.LinearInvolutionFrameTransport

universe u v w

variable {R : Type u} {F : Type v} {V : Type w}
variable [Semiring R] [AddCommMonoid F] [AddCommMonoid V]
variable [Module R F] [Module R V]

def transport (e : F ≃ₗ[R] V) (f : F ≃ₗ[R] F) : V ≃ₗ[R] V :=
  e.symm.trans f |>.trans e

theorem transport_apply (e : F ≃ₗ[R] V) (f : F ≃ₗ[R] F) (x : V) :
    transport e f x = e (f (e.symm x)) :=
  rfl

theorem transport_involutive
    (e : F ≃ₗ[R] V) (f : F ≃ₗ[R] F)
    (hf : ∀ x, f (f x) = x) (x : V) :
    transport e f (transport e f x) = x := by
  rw [transport_apply, transport_apply]
  rw [e.symm_apply_apply, hf, e.apply_symm_apply]

end InfoGeometry.Canonical.LinearInvolutionFrameTransport
