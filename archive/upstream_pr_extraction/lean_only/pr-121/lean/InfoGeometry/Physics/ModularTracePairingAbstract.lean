/-!
# Abstract trace-pairing transport

This owner isolates the algebraic part of finite-flow invariance.  It does
not identify a particular exponential, inverse, or analytic flow.
-/

namespace InfoGeometry.Physics.ModularTracePairingAbstract

universe u v w

variable {A : Type u} {R : Type v} {T : Type w}
variable [Mul A]

def tracePairing (τ : A → R) (X Y : A) : R := τ (X * Y)

theorem tracePairing_invariant
    (τ : A → R) (α : T → A → A)
    (h_mul : ∀ (t : T) (X Y : A), α t (X * Y) = α t X * α t Y)
    (h_trace : ∀ (t : T) (X : A), τ (α t X) = τ X)
    (t : T) (X Y : A) :
    tracePairing τ (α t X) (α t Y) = tracePairing τ X Y := by
  unfold tracePairing
  rw [← h_mul t X Y, h_trace]

theorem tracePairing_symm_of_cyclic
    (τ : A → R)
    (h_cyclic : ∀ (X Y : A), τ (X * Y) = τ (Y * X))
    (X Y : A) :
    tracePairing τ X Y = tracePairing τ Y X := by
  exact h_cyclic X Y

end InfoGeometry.Physics.ModularTracePairingAbstract
