/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotencyDefect
import InfoGeometry.Core.PeirceCompressionDefect
import InfoGeometry.OperatorAlgebra.SchurIdempotencyDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.RingTheory.Idempotents

/-!
# Exact Peirce defect readouts and Schur reduction

The four corners use the existing arbitrary-ring Peirce definitions. A head
inverse in the corner `pAp` has product `p`, not the ambient unit. All products
below retain their order. No involution, positivity, or analytic limit is used.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.SchurDefect

open InfoGeometry.Core.IdempotencyDefect

variable {A : Type*} [Ring A] {p : A}

/-- The head component of the quadratic defect includes the upper round trip. -/
theorem defect_11 (hp : p * p = p) (x : A) :
    peirce11 p (defect x) =
      peirce11 p x * peirce11 p x + conePlus p x * coneMinus p x - peirce11 p x := by
  have h := InfoGeometry.Core.PeirceCompressionDefect.compression_square_defect p x hp
  have h' := sub_eq_iff_eq_add.mp h
  change p * (x * x - x) * p = _
  rw [mul_sub, sub_mul, h']
  simp only [peirce11, conePlus, coneMinus]
  abel

/-- The upper mixed component retains both ordered head and tail actions. -/
theorem defect_10 (hp : p * p = p) (x : A) :
    conePlus p (defect x) =
      peirce11 p x * conePlus p x + conePlus p x * peirce00 p x - conePlus p x := by
  simp only [defect, peirce11, peirce00, conePlus]
  noncomm_ring [hp, P_mul_P' hp]

/-- The reverse mixed component has the opposite ordered products. -/
theorem defect_01 (hp : p * p = p) (x : A) :
    coneMinus p (defect x) =
      coneMinus p x * peirce11 p x + peirce00 p x * coneMinus p x - coneMinus p x := by
  simp only [defect, peirce11, peirce00, coneMinus]
  noncomm_ring [hp, P_mul_P' hp]

/-- The complementary component contains the reverse round trip. -/
theorem defect_00 (hp : p * p = p) (x : A) :
    peirce00 p (defect x) =
      coneMinus p x * conePlus p x + peirce00 p x * peirce00 p x - peirce00 p x := by
  have hq : (1 - p) * (1 - p) = 1 - p := by noncomm_ring [hp]
  simpa only [peirce11, peirce00, conePlus, coneMinus, sub_sub_cancel, add_comm] using
    defect_11 hq x

/-- The ordered Schur tail, with an explicitly supplied head resolvent. -/
def tail (p x r : A) : A := peirce00 p x - coneMinus p x * r * conePlus p x

theorem tail_left_support (hp : p * p = p) (x r : A) :
    (1 - p) * tail p x r = tail p x r := by
  simp only [tail, peirce00, conePlus, coneMinus]
  noncomm_ring [hp, P_mul_P' hp]

theorem tail_right_support (hp : p * p = p) (x r : A) :
    tail p x r * (1 - p) = tail p x r := by
  simp only [tail, peirce00, conePlus, coneMinus]
  noncomm_ring [hp, P_mul_P' hp]

theorem tail_complement_compression (hp : p * p = p) (x r : A) :
    peirce00 p (tail p x r) = tail p x r := by
  rw [peirce00, tail_left_support hp, tail_right_support hp]

/-- Exact transport of the full ambient defect into the Schur tail.
The inverse equations hold against the corner unit `p`; the resolvent is
never required to invert the head against the ambient unit `1`. -/
theorem tail_defect (hp : p * p = p) (x r : A)
    (har : peirce11 p x * r = p) (hra : r * peirce11 p x = p) :
    defect (tail p x r) =
      peirce00 p (defect x) -
      coneMinus p (defect x) * r * conePlus p x -
      coneMinus p x * r * conePlus p (defect x) +
      coneMinus p x * r * peirce11 p (defect x) * r * conePlus p x := by
  have hab : peirce11 p x * (r * conePlus p x) = conePlus p x := by
    rw [← mul_assoc, har, P_mul_conePlus hp]
  have hrab : r * (peirce11 p x * conePlus p x) = conePlus p x := by
    rw [← mul_assoc, hra, P_mul_conePlus hp]
  unfold tail
  rw [SchurIdempotencyDefect.schur_defect_of_coupling_inverse
      (peirce11 p x) (conePlus p x) (coneMinus p x) (peirce00 p x) r hab hrab,
    ← defect_00 hp x, ← defect_01 hp x, ← defect_10 hp x, ← defect_11 hp x]

/-- Idempotence descends provided the chosen head has a corner inverse.
The conclusion is derived from the defect identity, not stored as input. -/
theorem tail_isIdempotentElem (hp : p * p = p) (x r : A)
    (har : peirce11 p x * r = p) (hra : r * peirce11 p x = p)
    (hx : IsIdempotentElem x) : IsIdempotentElem (tail p x r) := by
  apply (defect_eq_zero_iff _).1
  rw [tail_defect hp x r har hra, (defect_eq_zero_iff x).2 hx]
  simp only [peirce00, coneMinus, conePlus, peirce11, mul_zero, zero_mul,
    sub_zero, add_zero]

/-- Native Mathlib corner units supply the correct inverse equations.
The unit of `hp.Corner` is `p`, including for a proper, noncentral cut. -/
theorem tail_isIdempotentElem_of_cornerUnit (hp : IsIdempotentElem p)
    (x : A) (u : hp.Cornerˣ) (hu : (u : hp.Corner).val = peirce11 p x)
    (hx : IsIdempotentElem x) :
    IsIdempotentElem (tail p x u.inv.val) := by
  have har : u.val.val * u.inv.val = p :=
    congrArg Subtype.val u.val_inv
  have hra : u.inv.val * u.val.val = p :=
    congrArg Subtype.val u.inv_val
  rw [hu] at har hra
  exact tail_isIdempotentElem hp.eq x u.inv.val har hra hx

/-- The tail expression is natural under unital ring homomorphisms. This
does not claim that Schur reduction itself is a ring homomorphism. -/
theorem map_tail {B : Type*} [Ring B] (f : A →+* B) (p x r : A) :
    f (tail p x r) = tail (f p) (f x) (f r) := by
  simp only [tail, peirce00, conePlus, coneMinus, map_sub, map_mul, map_one]

end InfoGeometry.OperatorAlgebra.PeirceSpine.SchurDefect
