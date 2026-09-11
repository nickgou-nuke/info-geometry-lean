import Mathlib.RingTheory.TensorProduct.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Algebra.SupergradedBracket

/-!
# Bosonized odd coproduct

This file proves the finite algebraic identity behind the bosonized coproduct
of an odd generator.  The symmetry coproduct is kept distinct from any map on
state spaces and from irreversible dynamics.

For an involution `Γ` and an odd element `G`, satisfying
`Γ * G = -(G * Γ)`, define

`ΔΓ(G) = G ⊗ 1 + Γ ⊗ G`.

The mixed terms in `ΔΓ(G)²` cancel.  Consequently, if `Γ² = 1` and
`G² = E`, the odd--odd anticommutator closes on the primitive even element
`E ⊗ 1 + 1 ⊗ E`.
-/

namespace InfoGeometry.Algebra.BosonizedOSpCoproduct

open scoped TensorProduct

variable {R A : Type*}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Primitive coproduct expression for an even element. -/
def primitiveEven (E : A) : A ⊗[R] A :=
  E ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] E

/-- Bosonized coproduct expression for an odd element. -/
def bosonizedOdd (Γ G : A) : A ⊗[R] A :=
  G ⊗ₜ[R] (1 : A) + Γ ⊗ₜ[R] G

/--
The square of the bosonized odd coproduct has no mixed terms.

This is the tensor-algebra form of the Koszul cancellation produced by the
parity relation `ΓG = -GΓ`.
-/
theorem bosonizedOdd_sq
    (Γ G : A) (hodd : Γ * G = -(G * Γ)) :
    bosonizedOdd (R := R) Γ G * bosonizedOdd (R := R) Γ G =
      (G * G) ⊗ₜ[R] (1 : A) + (Γ * Γ) ⊗ₜ[R] (G * G) := by
  unfold bosonizedOdd
  rw [add_mul, mul_add, mul_add]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hodd, TensorProduct.neg_tmul]
  abel

/-- With involutive parity, the square is the primitive coproduct of `G²`. -/
theorem bosonizedOdd_sq_of_involution
    (Γ G : A) (hΓ : Γ * Γ = 1) (hodd : Γ * G = -(G * Γ)) :
    bosonizedOdd (R := R) Γ G * bosonizedOdd (R := R) Γ G =
      primitiveEven (R := R) (G * G) := by
  rw [bosonizedOdd_sq (R := R) Γ G hodd, hΓ]
  rfl

/--
Odd--odd closure is preserved by the bosonized coproduct.

If `G² = E`, then the self-anticommutator of `ΔΓ(G)` is twice the primitive
coproduct of `E`.
-/
theorem bosonizedOdd_self_anticommutator
    (Γ G E : A)
    (hΓ : Γ * Γ = 1)
    (hodd : Γ * G = -(G * Γ))
    (hGsq : G * G = E) :
    InfoGeometry.Algebra.SupergradedBracket.anticommutator
        (bosonizedOdd (R := R) Γ G) (bosonizedOdd (R := R) Γ G) =
      (2 : R) • primitiveEven (R := R) E := by
  rw [InfoGeometry.Algebra.SupergradedBracket.anticommutator]
  rw [bosonizedOdd_sq_of_involution (R := R) Γ G hΓ hodd, hGsq]
  simp [two_smul]

end InfoGeometry.Algebra.BosonizedOSpCoproduct
