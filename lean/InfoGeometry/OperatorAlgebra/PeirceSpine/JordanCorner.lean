/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.Core.JordanAssociator

/-!
# Existing Jordan triples on arbitrary associative Peirce corners

The outer corner support alone forces the existing symmetric Jordan triple
to remain in that corner; the middle argument may be arbitrary. This is a
ring-level support theorem, separate from the existing real-algebra
tripotent/extreme-grade Jordan-pair construction.

For square-zero inputs, the existing unnormalized anticommutator associator
is the diagonal triple. The normalized real Jordan product introduces the
factor `1/4`. No new product or bundled Kantor structure is introduced.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

section Ring

variable {B : Type*} [Ring B]

/-- Two upper-corner outer inputs suffice for upper-corner triple closure. -/
theorem conePlus_jordanTriple {P : B} (hP : P * P = P) (A₁ Y A₂ : B) :
    conePlus P (jordanTriple (conePlus P A₁) Y (conePlus P A₂)) =
      jordanTriple (conePlus P A₁) Y (conePlus P A₂) := by
  have hright (A : B) : conePlus P A * (1 - P) = conePlus P A := by
    rw [mul_sub, mul_one, conePlus_mul_P hP, sub_zero]
  have hs (U V : B) :
      conePlus P (conePlus P U * Y * conePlus P V) =
        conePlus P U * Y * conePlus P V := by
    change P * (conePlus P U * Y * conePlus P V) * (1 - P) = _
    calc
      _ = (P * conePlus P U) * Y * (conePlus P V * (1 - P)) := by
        simp only [mul_assoc]
      _ = _ := by rw [P_mul_conePlus hP, hright]
  simp only [jordanTriple, conePlus_add, hs]

/-- Two lower-corner outer inputs suffice for lower-corner triple closure. -/
theorem coneMinus_jordanTriple {P : B} (hP : P * P = P) (C₁ Y C₂ : B) :
    coneMinus P (jordanTriple (coneMinus P C₁) Y (coneMinus P C₂)) =
      jordanTriple (coneMinus P C₁) Y (coneMinus P C₂) := by
  have hleft (C : B) : (1 - P) * coneMinus P C = coneMinus P C := by
    rw [sub_mul, one_mul, P_mul_coneMinus hP, sub_zero]
  have hs (U V : B) :
      coneMinus P (coneMinus P U * Y * coneMinus P V) =
        coneMinus P U * Y * coneMinus P V := by
    change (1 - P) * (coneMinus P U * Y * coneMinus P V) * P = _
    calc
      _ = ((1 - P) * coneMinus P U) * Y * (coneMinus P V * P) := by
        simp only [mul_assoc]
      _ = _ := by rw [hleft, coneMinus_mul_P hP]
  simp only [jordanTriple, coneMinus_add, hs]

/-- The unnormalized Jordan associator on a square-zero outer input is the
existing diagonal triple, with no commutativity assumption. -/
theorem anticomm_associator_eq_jordanTriple_of_sq_zero (x y : B) (hx : x * x = 0) :
    anticomm (anticomm y x) x - anticomm y (anticomm x x) = jordanTriple x y x := by
  simp only [anticomm]
  rw [InfoGeometry.Core.JordanAssociator.symm_associator_eq_double_commutator]
  calc
    _ = x * y * x + x * y * x - (x * x) * y - y * (x * x) := by
      noncomm_ring
    _ = _ := by rw [hx]; simp [jordanTriple]

end Ring

section RealAlgebra

variable {B : Type*} [Ring B] [Algebra ℝ B]

open InfoGeometry.Core.JordanPeirceDecomposition

/-- The normalized product contributes the factor one quarter of the
unnormalized diagonal triple. -/
theorem jordanMul_associator_eq_quarter_jordanTriple_of_sq_zero
    (x y : B) (hx : x * x = 0) :
    jordanMul (jordanMul y x) x - jordanMul y (jordanMul x x) =
      (1 / 4 : ℝ) • jordanTriple x y x := by
  rw [InfoGeometry.Core.JordanAssociator.jordan_associator_eq_expanded_double_commutator]
  have h := anticomm_associator_eq_jordanTriple_of_sq_zero x y hx
  simp only [anticomm] at h
  rw [InfoGeometry.Core.JordanAssociator.symm_associator_eq_double_commutator] at h
  rw [h]

end RealAlgebra

end InfoGeometry.OperatorAlgebra.PeirceSpine
