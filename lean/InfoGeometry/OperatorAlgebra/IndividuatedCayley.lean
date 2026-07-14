/-
InfoGeometry/OperatorAlgebra/IndividuatedCayley.lean

Individuated Cayley transform.

This module eliminates the unitary shadow of the Cayley transform.

Given:
  D K = K D,
  D* = D,
  K* = -K,
  (D + K) has a two-sided inverse,

the bounded Cayley transform

  U = (D - K)(D + K)^(-1)

is proved to be unitary:

  U* U = 1,
  U U* = 1.

The proof is algebraic and works in any starred ring.
-/

import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace IndividuatedCayley

/-! ## 1. Phase-linearity in a noncommutative ring -/

/-- `T` is phase-linear relative to `K` when it commutes with `K`. -/
def PhaseLinear
    {A : Type*} [Mul A]
    (K T : A) : Prop :=
  T * K = K * T

namespace PhaseLinear

variable {A : Type*} [Ring A] {K : A}

/-- The phase axis is phase-linear relative to itself. -/
theorem self :
    PhaseLinear K K :=
  rfl

/-- Sums of phase-linear elements are phase-linear. -/
theorem add
    {T S : A}
    (hT : PhaseLinear K T)
    (hS : PhaseLinear K S) :
    PhaseLinear K (T + S) := by
  dsimp [PhaseLinear] at hT hS ⊢
  rw [right_distrib, left_distrib, hT, hS]

/-- Negatives of phase-linear elements are phase-linear. -/
theorem neg
    {T : A}
    (hT : PhaseLinear K T) :
    PhaseLinear K (-T) := by
  dsimp [PhaseLinear] at hT ⊢
  rw [mul_neg, neg_mul, hT]

/-- Differences of phase-linear elements are phase-linear. -/
theorem sub
    {T S : A}
    (hT : PhaseLinear K T)
    (hS : PhaseLinear K S) :
    PhaseLinear K (T - S) := by
  simpa [sub_eq_add_neg] using add hT (neg hS)

end PhaseLinear

/-! ## 2. Inverse commutation -/

/--
If `B` is invertible with inverse `Binv`, and `X` commutes with `B`, then
`X` commutes with `Binv`.

This is the algebraic core that eliminates phase-linearity hypotheses for
resolvent inverses.
-/
theorem inverse_commutes_of_commutes
    {A : Type*} [Monoid A]
    {X B Binv : A}
    (h_right : B * Binv = 1)
    (h_left : Binv * B = 1)
    (hXB : X * B = B * X) :
    X * Binv = Binv * X := by
  calc
    X * Binv
        = 1 * (X * Binv) := by
            rw [one_mul]
    _ = (Binv * B) * (X * Binv) := by
            rw [h_left]
    _ = Binv * (B * X) * Binv := by
            simp only [mul_assoc]
    _ = Binv * (X * B) * Binv := by
            rw [hXB.symm]
    _ = (Binv * X) * (B * Binv) := by
            simp only [mul_assoc]
    _ = (Binv * X) * 1 := by
            rw [h_right]
    _ = Binv * X := by
            rw [mul_one]

/-- If `B` is phase-linear and invertible, then its inverse is phase-linear. -/
theorem inverse_phaseLinear
    {A : Type*} [Ring A]
    {K B Binv : A}
    (hB : PhaseLinear K B)
    (h_right : B * Binv = 1)
    (h_left : Binv * B = 1) :
    PhaseLinear K Binv := by
  dsimp [PhaseLinear] at hB ⊢
  exact
    (inverse_commutes_of_commutes
      (X := K)
      (B := B)
      (Binv := Binv)
      h_right
      h_left
      hB.symm).symm

/-! ## 3. Verified resolvent -/

/--
A verified phase resolvent for `D + K`.

Only `D_phase_linear` is supplied. Phase-linearity of the inverse of `D + K`
is proved.
-/
structure VerifiedPhaseResolvent
    (A : Type*) [Ring A]
    (K D : A) where
  /-- Bounded inverse of `D + K`. -/
  denomInv : A

  /-- Right inverse law. -/
  denom_right :
    (D + K) * denomInv = 1

  /-- Left inverse law. -/
  denom_left :
    denomInv * (D + K) = 1

  /-- `D` commutes with the phase axis. -/
  D_phase_linear :
    PhaseLinear K D

namespace VerifiedPhaseResolvent

variable {A : Type*} [Ring A]
variable {K D : A}

/-- The denominator `D + K` is phase-linear. -/
theorem denom_phase_linear
    (R : VerifiedPhaseResolvent A K D) :
    PhaseLinear K (D + K) :=
  PhaseLinear.add (VerifiedPhaseResolvent.D_phase_linear R) PhaseLinear.self

variable (R : VerifiedPhaseResolvent A K D)

/--
The denominator inverse is phase-linear.

This is not an assumption.
-/
theorem denomInv_phase_linear :
    PhaseLinear K R.denomInv :=
  inverse_phaseLinear
    (denom_phase_linear R)
    R.denom_right
    R.denom_left

/-- `D + K` commutes with its inverse. -/
theorem denom_commutes_inverse :
    (D + K) * R.denomInv =
      R.denomInv * (D + K) := by
  rw [R.denom_right, R.denom_left]

end VerifiedPhaseResolvent

/-! ## 3b. Operator Cayley identities -/

/--
Right Cayley transform relation.

Let `U` be a right inverse witness for `1 - X` in the sense

`U * (1 - X) = 1`.

For the right Cayley expression

`Y = (1 + X) * U`,

we have

`(Y - 1) * (1 - X) = 2 * X`.

This is the noncommutative operator version of the scalar identity underlying
`C⁻¹(C(x)) = x`, before dividing by `2`.
-/
@[rep_depth operator]
theorem operator_cayley_right_sub_relation
    {R : Type*} [Ring R]
    (X U : R)
    (hU : U * (1 - X) = 1) :
    (((1 + X) * U) - 1) * (1 - X) = (2 : R) * X := by
  calc
    (((1 + X) * U) - 1) * (1 - X)
        = (1 + X) * (U * (1 - X)) - (1 - X) := by
          noncomm_ring
    _ = (1 + X) * 1 - (1 - X) := by
          rw [hU]
    _ = X + X := by
          noncomm_ring
    _ = (2 : R) * X := by
          simp [two_mul]

/--
Right Cayley denominator relation.

Under the same hypothesis,

`(((1 + X) * U) + 1) * (1 - X) = 2`.

This is the operator denominator identity behind the inverse Cayley formula.
-/
@[rep_depth operator]
theorem operator_cayley_right_add_relation
    {R : Type*} [Ring R]
    (X U : R)
    (hU : U * (1 - X) = 1) :
    (((1 + X) * U) + 1) * (1 - X) = (2 : R) := by
  calc
    (((1 + X) * U) + 1) * (1 - X)
        = (1 + X) * (U * (1 - X)) + (1 - X) := by
          noncomm_ring
    _ = (1 + X) * 1 + (1 - X) := by
          rw [hU]
    _ = 2 := by
          norm_num

/-! ## 4. Constructive Cayley transform -/

/-- The bounded Cayley transform: `U = (D - K)(D + K)^(-1)`. -/
def boundedCayley
    {A : Type*} [Ring A]
    {K D : A}
    (R : VerifiedPhaseResolvent A K D) : A :=
  (D - K) * R.denomInv

/-- If `D` commutes with `K`, then `D + K` commutes with `D - K`. -/
theorem D_add_K_commutes_D_sub_K
    {A : Type*} [Ring A]
    {K D : A}
    (hD : PhaseLinear K D) :
    (D + K) * (D - K) =
      (D - K) * (D + K) := by
  have hKD : K * D = D * K := hD.symm
  have hL :
      (D + K) * (D - K) = D * D - K * K := by
    calc
      (D + K) * (D - K)
          = (D * D + K * D) - (D * K + K * K) := by
              rw [mul_sub, add_mul, add_mul]
      _ = (D * D + D * K) - (D * K + K * K) := by
              rw [hKD]
      _ = D * D - K * K := by
              abel
  have hR :
      (D - K) * (D + K) = D * D - K * K := by
    calc
      (D - K) * (D + K)
          = (D * D - K * D) + (D * K - K * K) := by
              rw [mul_add, sub_mul, sub_mul]
      _ = (D * D - D * K) + (D * K - K * K) := by
              rw [hKD]
      _ = D * D - K * K := by
              abel
  rw [hL, hR]

/-- Constructive proof: `(D - K)` commutes with `(D + K)^(-1)`. -/
theorem cayley_factors_commute
    {A : Type*} [Ring A]
    {K D : A}
    (R : VerifiedPhaseResolvent A K D) :
    (D - K) * R.denomInv =
      R.denomInv * (D - K) := by
  have hAB :
      (D - K) * (D + K) =
        (D + K) * (D - K) :=
    (D_add_K_commutes_D_sub_K R.D_phase_linear).symm
  exact
    inverse_commutes_of_commutes
      (X := D - K)
      (B := D + K)
      (Binv := R.denomInv)
      R.denom_right
      R.denom_left
      hAB

/-- Constructive proof: the Cayley transform is phase-linear. -/
theorem boundedCayley_is_phase_linear
    {A : Type*} [Ring A]
    {K D : A}
    (R : VerifiedPhaseResolvent A K D) :
    PhaseLinear K (boundedCayley R) := by
  dsimp [boundedCayley, PhaseLinear]
  have hNum :
      PhaseLinear K (D - K) :=
    PhaseLinear.sub R.D_phase_linear PhaseLinear.self
  have hInv :
      PhaseLinear K R.denomInv :=
    R.denomInv_phase_linear
  calc
    ((D - K) * R.denomInv) * K
        = (D - K) * (R.denomInv * K) := by
            rw [mul_assoc]
    _ = (D - K) * (K * R.denomInv) := by
            rw [hInv]
    _ = ((D - K) * K) * R.denomInv := by
            rw [← mul_assoc]
    _ = (K * (D - K)) * R.denomInv := by
            rw [hNum]
    _ = K * ((D - K) * R.denomInv) := by
            rw [mul_assoc]

/-! ## 5. Verified unitary Cayley -/

/--
A verified unitary Cayley resolvent.

This supplies the real adjoint geometry:

* `D* = D`;
* `K* = -K`.

The adjoint inverse law for `(D + K)^(-1)` is no longer a field. It is proved.
-/
structure VerifiedUnitaryResolvent
    (A : Type*) [Ring A] [StarRing A]
    (K D : A) where
  /-- Bounded inverse of `D + K`. -/
  denomInv : A

  /-- Right inverse law. -/
  denom_right :
    (D + K) * denomInv = 1

  /-- Left inverse law. -/
  denom_left :
    denomInv * (D + K) = 1

  /-- `D` commutes with the phase axis. -/
  D_phase_linear :
    PhaseLinear K D

  /-- `D` is self-adjoint. -/
  D_selfAdjoint :
    star D = D

  /-- `K` is skew-adjoint. -/
  K_skewAdjoint :
    star K = -K

namespace VerifiedUnitaryResolvent

variable {A : Type*} [Ring A] [StarRing A]
variable {K D : A}

/-- Forget the adjoint geometry and keep the phase resolvent data. -/
def toVerifiedPhaseResolvent
    (R : VerifiedUnitaryResolvent A K D) :
    VerifiedPhaseResolvent A K D where
  denomInv := VerifiedUnitaryResolvent.denomInv R
  denom_right := VerifiedUnitaryResolvent.denom_right R
  denom_left := VerifiedUnitaryResolvent.denom_left R
  D_phase_linear := VerifiedUnitaryResolvent.D_phase_linear R

/-- Adjoint of the denominator: `(D + K)* = D - K`. -/
theorem star_denom
    (R : VerifiedUnitaryResolvent A K D) :
    star (D + K) = D - K := by
  rw [
    star_add,
    VerifiedUnitaryResolvent.D_selfAdjoint R,
    VerifiedUnitaryResolvent.K_skewAdjoint R
  ]
  simp [sub_eq_add_neg]

/-- Adjoint of the numerator: `(D - K)* = D + K`. -/
theorem star_num
    (R : VerifiedUnitaryResolvent A K D) :
    star (D - K) = D + K := by
  rw [
    star_sub,
    VerifiedUnitaryResolvent.D_selfAdjoint R,
    VerifiedUnitaryResolvent.K_skewAdjoint R
  ]
  simp

variable (R : VerifiedUnitaryResolvent A K D)

/--
The adjoint of the denominator inverse is a left inverse for `D - K`.

This was previously an explicit hypothesis. It is now proved by taking the
adjoint of `(D + K)(D + K)^(-1) = 1`.
-/
theorem star_denomInv_mul_num_eq_one :
    star R.denomInv * (D - K) = 1 := by
  have h := congrArg star R.denom_right
  simpa [star_mul, star_denom R] using h

/--
`D - K` has `star denomInv` as a right inverse.

This follows by taking the adjoint of `(D + K)^(-1)(D + K) = 1`.
-/
theorem num_mul_star_denomInv_eq_one :
    (D - K) * star R.denomInv = 1 := by
  have h := congrArg star R.denom_left
  simpa [star_mul, star_denom R] using h

/-- Constructive proof: `U*U = 1` for the Cayley transform. -/
theorem boundedCayley_star_mul_self :
    star (boundedCayley (R.toVerifiedPhaseResolvent)) *
    boundedCayley (R.toVerifiedPhaseResolvent) = 1 := by
  dsimp [boundedCayley]
  have hComm :
      (D + K) * (D - K) =
        (D - K) * (D + K) :=
    D_add_K_commutes_D_sub_K (VerifiedUnitaryResolvent.D_phase_linear R)
  calc
    star ((D - K) * R.denomInv) * ((D - K) * R.denomInv)
        = (star R.denomInv * star (D - K)) *
            ((D - K) * R.denomInv) := by
              rw [star_mul]
    _ = (star R.denomInv * (D + K)) *
            ((D - K) * R.denomInv) := by
              rw [star_num R]
    _ = star R.denomInv * ((D + K) * (D - K)) * R.denomInv := by
              simp only [mul_assoc]
    _ = star R.denomInv * ((D - K) * (D + K)) * R.denomInv := by
              rw [hComm]
    _ = (star R.denomInv * (D - K)) * ((D + K) * R.denomInv) := by
              simp only [mul_assoc]
    _ = 1 * 1 := by
              rw [star_denomInv_mul_num_eq_one R, R.denom_right]
    _ = 1 := by
              simp

/-- Constructive proof: `UU* = 1` for the Cayley transform. -/
theorem boundedCayley_mul_star_self :
    boundedCayley (R.toVerifiedPhaseResolvent) *
      star (boundedCayley (R.toVerifiedPhaseResolvent)) = 1 := by
  dsimp [boundedCayley]
  have hCayleyComm :
      (D - K) * R.denomInv =
        R.denomInv * (D - K) :=
    cayley_factors_commute (toVerifiedPhaseResolvent R)
  calc
    ((D - K) * R.denomInv) * star ((D - K) * R.denomInv)
        = ((D - K) * R.denomInv) *
            (star R.denomInv * star (D - K)) := by
              rw [star_mul]
    _ = ((D - K) * R.denomInv) *
            (star R.denomInv * (D + K)) := by
              rw [star_num R]
    _ = (R.denomInv * (D - K)) *
            (star R.denomInv * (D + K)) := by
              rw [hCayleyComm]
    _ = R.denomInv * ((D - K) * star R.denomInv) * (D + K) := by
              simp only [mul_assoc]
    _ = R.denomInv * 1 * (D + K) := by
              rw [num_mul_star_denomInv_eq_one R]
    _ = R.denomInv * (D + K) := by
              simp
    _ = 1 := by
              exact R.denom_left

/-- Bundled unitary Cayley statement. -/
theorem boundedCayley_is_unitary :
    star (boundedCayley (R.toVerifiedPhaseResolvent)) *
        boundedCayley (R.toVerifiedPhaseResolvent) = 1
      ∧
    boundedCayley (R.toVerifiedPhaseResolvent) *
        star (boundedCayley (R.toVerifiedPhaseResolvent)) = 1 := by
  exact ⟨
    boundedCayley_star_mul_self R,
    boundedCayley_mul_star_self R
  ⟩

end VerifiedUnitaryResolvent

/-! ## 6. Compact verified Cayley-resolvent API -/

/--
Verified algebraic data for the Cayley transform.

`D` is the self-adjoint operator.

`K` is the skew-adjoint phase axis.

`plusInv` is the two-sided inverse of `D + K`.
-/
structure VerifiedCayleyResolvent
    (A : Type*) [Ring A] [StarRing A] where
  /-- Self-adjoint operator. -/
  D : A

  /-- Skew-adjoint phase axis. -/
  K : A

  /-- Two-sided inverse of `D + K`. -/
  plusInv : A

  /-- `D* = D`. -/
  D_selfAdjoint :
    star D = D

  /-- `K* = -K`. -/
  K_skewAdjoint :
    star K = -K

  /-- `D` and `K` commute. -/
  D_comm_K :
    D * K = K * D

  /-- Right inverse law: `(D + K) * plusInv = 1`. -/
  plus_mul_plusInv :
    (D + K) * plusInv = 1

  /-- Left inverse law: `plusInv * (D + K) = 1`. -/
  plusInv_mul_plus :
    plusInv * (D + K) = 1

namespace VerifiedCayleyResolvent

variable {A : Type*} [Ring A] [StarRing A]
variable (R : VerifiedCayleyResolvent A)

/-- The denominator `D + K`. -/
def plus : A :=
  R.D + R.K

/-- The numerator `D - K`. -/
def minus : A :=
  R.D - R.K

/-- The Cayley transform `U = (D - K) * (D + K)^(-1)`. -/
def cayley : A :=
  R.minus * R.plusInv

/-- Convert to the existing unitary-resolvent API. -/
def toVerifiedUnitaryResolvent :
    VerifiedUnitaryResolvent A R.K R.D where
  denomInv := R.plusInv
  denom_right := R.plus_mul_plusInv
  denom_left := R.plusInv_mul_plus
  D_phase_linear := by
    dsimp [PhaseLinear]
    exact R.D_comm_K
  D_selfAdjoint := R.D_selfAdjoint
  K_skewAdjoint := R.K_skewAdjoint

/-- The adjoint of `D + K` is `D - K`. -/
theorem star_plus :
    star R.plus = R.minus := by
  exact VerifiedUnitaryResolvent.star_denom R.toVerifiedUnitaryResolvent

/-- The adjoint of `D - K` is `D + K`. -/
theorem star_minus :
    star R.minus = R.plus := by
  exact VerifiedUnitaryResolvent.star_num R.toVerifiedUnitaryResolvent

/--
The two Cayley factors commute:

`(D + K)(D - K) = (D - K)(D + K)`.
-/
theorem plus_mul_minus_comm :
    R.plus * R.minus = R.minus * R.plus := by
  exact
    D_add_K_commutes_D_sub_K
      (A := A) (K := R.K) (D := R.D)
      R.toVerifiedUnitaryResolvent.D_phase_linear

/-- The adjoint of the inverse of `D + K` is a left inverse of `D - K`. -/
theorem star_plusInv_mul_minus :
    star R.plusInv * R.minus = 1 := by
  exact
    VerifiedUnitaryResolvent.star_denomInv_mul_num_eq_one
      R.toVerifiedUnitaryResolvent

/-- The adjoint of the inverse of `D + K` is a right inverse of `D - K`. -/
theorem minus_mul_star_plusInv :
    R.minus * star R.plusInv = 1 := by
  exact
    VerifiedUnitaryResolvent.num_mul_star_denomInv_eq_one
      R.toVerifiedUnitaryResolvent

/-- The numerator commutes with the inverse of the denominator. -/
theorem minus_mul_plusInv_comm :
    R.minus * R.plusInv = R.plusInv * R.minus := by
  exact
    cayley_factors_commute R.toVerifiedUnitaryResolvent.toVerifiedPhaseResolvent

/-! ### Constructive unitarity -/

/-- Right-unitarity/isometry: `U* U = 1`. -/
theorem cayley_star_mul_cayley :
    star R.cayley * R.cayley = 1 := by
  exact
    VerifiedUnitaryResolvent.boundedCayley_star_mul_self
      R.toVerifiedUnitaryResolvent

/-- Left-unitarity/coisometry: `U U* = 1`. -/
theorem cayley_mul_star_cayley :
    R.cayley * star R.cayley = 1 := by
  exact
    VerifiedUnitaryResolvent.boundedCayley_mul_star_self
      R.toVerifiedUnitaryResolvent

/-- The Cayley transform is unitary: both `U*U = 1` and `UU* = 1`. -/
theorem cayley_unitary :
    star R.cayley * R.cayley = 1 ∧
      R.cayley * star R.cayley = 1 :=
  ⟨R.cayley_star_mul_cayley, R.cayley_mul_star_cayley⟩

end VerifiedCayleyResolvent

/-! ## 7. Cayley unitarity readout -/

/--
Constructive Cayley unitarity readout.

Given explicit self-adjoint/skew-adjoint resolvent data, the Cayley transform
is constructively unitary.
-/
theorem cayleyUnitarityOwnerTarget :
  ∀ (A : Type*) [Ring A] [StarRing A],
  ∀ R : VerifiedCayleyResolvent A,
    star R.cayley * R.cayley = 1 ∧
      R.cayley * star R.cayley = 1 := by
  intro A _ _ R
  exact R.cayley_unitary

attribute [rep_depth operator]
  PhaseLinear
  inverse_commutes_of_commutes
  inverse_phaseLinear
  VerifiedPhaseResolvent
  VerifiedPhaseResolvent.denomInv_phase_linear
  operator_cayley_right_sub_relation
  operator_cayley_right_add_relation
  boundedCayley
  D_add_K_commutes_D_sub_K
  cayley_factors_commute
  boundedCayley_is_phase_linear
  VerifiedUnitaryResolvent
  VerifiedUnitaryResolvent.star_denomInv_mul_num_eq_one
  VerifiedUnitaryResolvent.num_mul_star_denomInv_eq_one
  VerifiedUnitaryResolvent.boundedCayley_star_mul_self
  VerifiedUnitaryResolvent.boundedCayley_mul_star_self
  VerifiedUnitaryResolvent.boundedCayley_is_unitary
  VerifiedCayleyResolvent
  VerifiedCayleyResolvent.cayley_star_mul_cayley
  VerifiedCayleyResolvent.cayley_mul_star_cayley
  VerifiedCayleyResolvent.cayley_unitary

end IndividuatedCayley
