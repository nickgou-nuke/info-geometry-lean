import Mathlib

/-! Transport of an involutive linear operator through an existing linear
equivalence.  This is the carrier-level core of a transported Hodge operator;
it does not identify unrelated products or bases. -/

namespace InfoGeometry.Canonical.TransportedInvolution

variable {R V W : Type*} [Semiring R]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

def transport (F : V ≃ₗ[R] W) (J : V →ₗ[R] V) : W →ₗ[R] W :=
  F.toLinearMap.comp (J.comp F.symm.toLinearMap)

theorem transport_apply (F : V ≃ₗ[R] W) (J : V →ₗ[R] V) (x : W) :
    transport F J x = F (J (F.symm x)) :=
  rfl

theorem transport_involutive (F : V ≃ₗ[R] W) (J : V →ₗ[R] V)
    (hJ : J.comp J = LinearMap.id) :
    (transport F J).comp (transport F J) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change F (J (F.symm (F (J (F.symm x))))) = x
  rw [F.symm_apply_apply]
  have h := congrArg (fun L : V →ₗ[R] V => L (F.symm x)) hJ
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  rw [h]
  exact F.apply_symm_apply x

end InfoGeometry.Canonical.TransportedInvolution
