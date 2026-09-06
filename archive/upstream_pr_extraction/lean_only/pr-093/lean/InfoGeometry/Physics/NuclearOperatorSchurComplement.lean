import Mathlib
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev
import InfoGeometry.Physics.NuclearFiniteNilpotentSoul

/-!
# Noncommutative Schur-complement layer for operator Soloviev systems

A Berezinian or determinant is not required to define the operator-level
elimination of one block.  Given an explicit two-sided inverse `B⁻¹`, the
left effective operator is

`E₀ - V * B⁻¹ * W`.

This construction is valid in an arbitrary associative ring and is exactly
invariant under simultaneous reflection of the two off-diagonal channels.

The finite nilpotent-soul owner supplies a canonical example: `1+s` has the
exact polynomial inverse when `s` is nilpotent.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearOperatorSchurComplement

open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearFiniteNilpotentSoul

variable {A : Type*} [Ring A]

/-- Explicit two-sided inverse data, kept proof-carrying rather than inferred
from a field assumption. -/
structure InversePair (B Binv : A) : Prop where
  left_inv : Binv * B = 1
  right_inv : B * Binv = 1

/-- A denominator/resolvent block with an explicit inverse. -/
structure ResolventData (A : Type*) [Ring A] where
  denom : A
  inv : A
  inverse_pair : InversePair denom inv

/-- Noncommutative left Schur/effective operator. -/
def effectiveOperator (E0 V W Binv : A) : A :=
  E0 - V * Binv * W

/-- Reflection of both off-diagonal channels leaves the effective operator
unchanged. -/
theorem effectiveOperator_reflection
    (E0 V W Binv : A) :
    effectiveOperator E0 (-V) (-W) Binv =
      effectiveOperator E0 V W Binv := by
  unfold effectiveOperator
  noncomm_ring

/-- The same theorem packaged through explicit resolvent data. -/
theorem effectiveOperator_reflection_resolvent
    (R : ResolventData A) (E0 V W : A) :
    effectiveOperator E0 (-V) (-W) R.inv =
      effectiveOperator E0 V W R.inv :=
  effectiveOperator_reflection E0 V W R.inv

/-- Hermitian-style channel uses `star V` as the reverse transition. -/
section Star

variable [StarRing A]

/-- Effective operator for a star-paired off-diagonal channel. -/
def starEffectiveOperator (E0 V Binv : A) : A :=
  effectiveOperator E0 V (star V) Binv

/-- Simultaneous sign reversal of a star-paired channel leaves the effective
operator invariant. -/
theorem starEffectiveOperator_reflection
    (E0 V Binv : A) :
    starEffectiveOperator E0 (-V) Binv =
      starEffectiveOperator E0 V Binv := by
  unfold starEffectiveOperator
  simpa using effectiveOperator_reflection E0 V (star V) Binv

end Star

/-- Every finite nilpotent soul gives exact resolvent data for `1+s`. -/
def soulResolvent (S : FiniteSoul A) : ResolventData A where
  denom := 1 + S.value
  inv := S.inversePolynomial
  inverse_pair :=
    ⟨S.inversePolynomial_mul_one_add,
      S.one_add_mul_inversePolynomial⟩

@[simp] theorem soulResolvent_denom (S : FiniteSoul A) :
    (soulResolvent S).denom = 1 + S.value := rfl

@[simp] theorem soulResolvent_inv (S : FiniteSoul A) :
    (soulResolvent S).inv = S.inversePolynomial := rfl

/-- Nilpotent-soul effective operator: no infinite resolvent series is needed. -/
def soulEffectiveOperator
    (S : FiniteSoul A) (E0 V W : A) : A :=
  effectiveOperator E0 V W (soulResolvent S).inv

/-- Exact reflection invariance survives the finite-soul resolvent. -/
theorem soulEffectiveOperator_reflection
    (S : FiniteSoul A) (E0 V W : A) :
    soulEffectiveOperator S E0 (-V) (-W) =
      soulEffectiveOperator S E0 V W := by
  exact effectiveOperator_reflection E0 V W (soulResolvent S).inv

/-- Consolidated noncommutative Schur/nilpotent packet. -/
theorem soul_schur_packet
    (S : FiniteSoul A) (E0 V W : A) :
    (soulResolvent S).inv * (soulResolvent S).denom = 1 ∧
      (soulResolvent S).denom * (soulResolvent S).inv = 1 ∧
      soulEffectiveOperator S E0 (-V) (-W) =
        soulEffectiveOperator S E0 V W :=
  ⟨(soulResolvent S).inverse_pair.left_inv,
    (soulResolvent S).inverse_pair.right_inv,
    soulEffectiveOperator_reflection S E0 V W⟩

end InfoGeometry.Physics.NuclearOperatorSchurComplement

end noncomputable section
