/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixPeirceZorn.MatrixZorn
import InfoGeometry.Canonical.MatrixPeirceZorn.DefectCalculus

/-!
# Involutions and exact defect identities on the matrix-valued Zorn product

The exchange map has a proved multiplicativity defect. The signed exchange is
an automorphism of the explicitly named bilinear product. All entries remain
arbitrary noncommuting square matrices.
-/

namespace InfoGeometry.Canonical.MatrixPeirceZorn.Zorn

variable {n : Type*} [Fintype n] [DecidableEq n]

def mulHom : Carrier n →+ Carrier n →+ Carrier n where
  toFun X :=
    { toFun := mul X
      map_zero' := mul_zero X
      map_add' := mul_add X }
  map_zero' := by
    apply AddMonoidHom.ext
    intro X
    exact zero_mul X
  map_add' X Y := by
    apply AddMonoidHom.ext
    intro Z
    exact add_mul X Y Z

@[simp] theorem mulHom_apply (X Y : Carrier n) : mulHom X Y = mul X Y := rfl

theorem teichmueller_identity (W X Y Z : Carrier n) :
    mul W (associator X Y Z) - associator (mul W X) Y Z +
      associator W (mul X Y) Z - associator W X (mul Y Z) +
      mul (associator W X Y) Z = 0 :=
  DefectCalculus.teichmueller mulHom W X Y Z

theorem associator_reassociation (W X Y Z : Carrier n) :
    associator (mul W X) Y Z + associator W X (mul Y Z) =
      mul (associator W X Y) Z + associator W (mul X Y) Z +
        mul W (associator X Y Z) :=
  DefectCalculus.associator_reassociation mulHom W X Y Z

theorem bracket_leibniz_defect (X Y Z : Carrier n) :
    bracket (mul X Y) Z - (mul X (bracket Y Z) + mul (bracket X Z) Y) =
      associator X Y Z - associator X Z Y + associator Z X Y :=
  DefectCalculus.commutator_leibniz_defect mulHom X Y Z

theorem jacobiator_eq_alternating_associator (X Y Z : Carrier n) :
    jacobiator X Y Z =
      associator X Y Z + associator Y Z X + associator Z X Y -
        associator Y X Z - associator Z Y X - associator X Z Y :=
  DefectCalculus.jacobiator_eq_alternating_associator mulHom X Y Z

def exchange (X : Carrier n) : Carrier n :=
  (X.2.2.2, X.2.2.1, X.2.1, X.1)

def signedExchange (X : Carrier n) : Carrier n :=
  (X.2.2.2, -X.2.2.1, -X.2.1, X.1)

def transport (X Y : Carrier n) : Carrier n :=
  (X.1 * Y.1 + dot X.2.1 Y.2.2.1,
   left X.1 Y.2.1 + right X.2.1 Y.2.2.2,
   right X.2.2.1 Y.1 + left X.2.2.2 Y.2.2.1,
   dot X.2.2.1 Y.2.1 + X.2.2.2 * Y.2.2.2)

def crossTerm (X Y : Carrier n) : Carrier n :=
  upper (-(cross X.2.2.1 Y.2.2.1)) + lower (cross X.2.1 Y.2.1)

omit [DecidableEq n] in
theorem mul_eq_transport_add_crossTerm (X Y : Carrier n) :
    mul X Y = transport X Y + crossTerm X Y := by
  simp [mul, transport, crossTerm, upper, lower, sub_eq_add_neg]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem exchange_involutive (X : Carrier n) : exchange (exchange X) = X := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem signedExchange_involutive (X : Carrier n) :
    signedExchange (signedExchange X) = X := by
  simp [signedExchange]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem exchange_upper (u : Vec n) : exchange (upper u) = lower u := rfl
omit [Fintype n] [DecidableEq n] in
@[simp] theorem exchange_lower (u : Vec n) : exchange (lower u) = upper u := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem signedExchange_add (X Y : Carrier n) :
    signedExchange (X + Y) = signedExchange X + signedExchange Y := by
  simp [signedExchange, add_comm]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem signedExchange_sub (X Y : Carrier n) :
    signedExchange (X - Y) = signedExchange X - signedExchange Y := by
  simp [signedExchange, sub_eq_add_neg, add_comm]

omit [DecidableEq n] in
theorem signedExchange_mul (X Y : Carrier n) :
    signedExchange (mul X Y) = mul (signedExchange X) (signedExchange Y) := by
  apply Prod.ext
  · simp [signedExchange, mul, dot_eq]
    abel
  · apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [signedExchange, mul, left, right, cross, Matrix.vecHead, Matrix.vecTail] <;>
        noncomm_ring
    · apply Prod.ext
      · funext i
        fin_cases i <;>
          simp [signedExchange, mul, left, right, cross, Matrix.vecHead, Matrix.vecTail] <;>
          noncomm_ring
      · simp [signedExchange, mul, dot_eq]
        abel

def signedExchangeEquiv : Carrier n ≃+ Carrier n where
  toFun := signedExchange
  invFun := signedExchange
  left_inv := signedExchange_involutive
  right_inv := signedExchange_involutive
  map_add' := signedExchange_add

omit [DecidableEq n] in
@[simp] theorem signedExchange_associator (X Y Z : Carrier n) :
    signedExchange (associator X Y Z) =
      associator (signedExchange X) (signedExchange Y) (signedExchange Z) := by
  simp only [associator, signedExchange_sub, signedExchange_mul]

omit [DecidableEq n] in
@[simp] theorem signedExchange_bracket (X Y : Carrier n) :
    signedExchange (bracket X Y) = bracket (signedExchange X) (signedExchange Y) := by
  simp only [bracket, signedExchange_sub, signedExchange_mul]

omit [DecidableEq n] in
theorem signedExchange_jacobiator (X Y Z : Carrier n) :
    signedExchange (jacobiator X Y Z) =
      jacobiator (signedExchange X) (signedExchange Y) (signedExchange Z) := by
  simp only [jacobiator, signedExchange_add, signedExchange_bracket]

/-- Exact failure of the unsigned exchange to preserve the bilinear product. -/
theorem exchange_multiplicativity_defect (X Y : Carrier n) :
    exchange (mul X Y) - mul (exchange X) (exchange Y) =
      2 • upper (cross X.2.1 Y.2.1) - 2 • lower (cross X.2.2.1 Y.2.2.1) := by
  apply Prod.ext
  · simp [exchange, mul, upper, lower, dot_eq]
    noncomm_ring
  · apply Prod.ext
    · funext i
      fin_cases i <;> simp [exchange, mul, upper, lower, cross] <;>
        noncomm_ring
    · apply Prod.ext
      · funext i
        fin_cases i <;> simp [exchange, mul, upper, lower, cross] <;>
          noncomm_ring
      · simp [exchange, mul, upper, lower, dot_eq]
        noncomm_ring

/-- Three channel associators cancel by the ordered matrix triple-product identity. -/
theorem upper_reflection_cancellation (u w v : Vec n) :
    associator (upper u) (lower w) (upper v) +
      associator (upper u) (exchange (lower w)) (exchange (upper v)) +
      associator (exchange (upper u)) (exchange (lower w)) (upper v) = 0 := by
  simp only [exchange_lower, exchange_upper]
  rw [associator_upper_lower_upper, associator_upper_upper_lower,
    associator_lower_upper_upper, bac_cab]
  simp only [upper_sub]
  abel

theorem lower_reflection_cancellation (u w v : Vec n) :
    associator (lower u) (upper w) (lower v) +
      associator (lower u) (exchange (upper w)) (exchange (lower v)) +
      associator (exchange (lower u)) (exchange (upper w)) (lower v) = 0 := by
  simp only [exchange_lower, exchange_upper]
  rw [associator_lower_upper_lower, associator_lower_lower_upper,
    associator_upper_lower_lower, bac_cab]
  simp only [lower_sub]
  abel

theorem corrected_reassociation (u w v : Vec n) :
    mul (mul (upper u) (lower w)) (upper v) =
      mul (upper u) (mul (lower w) (upper v)) -
        associator (upper u) (exchange (lower w)) (exchange (upper v)) -
        associator (exchange (upper u)) (exchange (lower w)) (upper v) := by
  have h := upper_reflection_cancellation u w v
  apply sub_eq_zero.mp
  convert h using 1
  dsimp only [associator]
  abel

end InfoGeometry.Canonical.MatrixPeirceZorn.Zorn
