/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.Core.JordanAssociatorRing

/-!
# Polarized Peirce triple support and a square-zero associator

The existing associative `jordanTriple X Y Z = X * Y * Z + Z * Y * X`
stays in either off-diagonal Peirce corner when its two outer inputs lie in
that corner. The middle input is arbitrary. The square-zero specialization
of the unnormalized Jordan associator recovers the repeated-entry triple.

The corner vocabulary and zero-product laws belong to `PeirceSpine.Basic`;
the triple belongs to `PeirceSpine.Bergman`; the division-free Jordan identity
belongs to `Core.JordanAssociatorRing`. These results hold over arbitrary
associative rings and do not assert a bundled Kantor triple system.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- A polarized triple of upper-corner outer inputs has upper-corner support,
regardless of its middle input. -/
theorem jordanTriple_conePlus_compression {P : B} (hP : P * P = P)
    (A₁ Y A₂ : B) :
    P * jordanTriple (conePlus P A₁) Y (conePlus P A₂) * (1 - P) =
      jordanTriple (conePlus P A₁) Y (conePlus P A₂) := by
  have hright (A : B) : conePlus P A * (1 - P) = conePlus P A := by
    rw [mul_sub, mul_one, conePlus_mul_P hP, sub_zero]
  calc
    P * jordanTriple (conePlus P A₁) Y (conePlus P A₂) * (1 - P) =
        (P * conePlus P A₁) * Y * (conePlus P A₂ * (1 - P)) +
          (P * conePlus P A₂) * Y * (conePlus P A₁ * (1 - P)) := by
      simp only [jordanTriple, mul_add, add_mul, mul_assoc]
    _ = jordanTriple (conePlus P A₁) Y (conePlus P A₂) := by
      simp only [P_mul_conePlus hP, hright, jordanTriple]

/-- A polarized triple of lower-corner outer inputs has lower-corner support,
regardless of its middle input. -/
theorem jordanTriple_coneMinus_compression {P : B} (hP : P * P = P)
    (C₁ Y C₂ : B) :
    (1 - P) * jordanTriple (coneMinus P C₁) Y (coneMinus P C₂) * P =
      jordanTriple (coneMinus P C₁) Y (coneMinus P C₂) := by
  have hleft (C : B) : (1 - P) * coneMinus P C = coneMinus P C := by
    rw [sub_mul, one_mul, P_mul_coneMinus hP, sub_zero]
  calc
    (1 - P) * jordanTriple (coneMinus P C₁) Y (coneMinus P C₂) * P =
        ((1 - P) * coneMinus P C₁) * Y * (coneMinus P C₂ * P) +
          ((1 - P) * coneMinus P C₂) * Y * (coneMinus P C₁ * P) := by
      simp only [jordanTriple, mul_add, add_mul, mul_assoc]
    _ = jordanTriple (coneMinus P C₁) Y (coneMinus P C₂) := by
      simp only [hleft, coneMinus_mul_P hP, jordanTriple]

/-- For a square-zero element, the unnormalized Jordan associator equals the
repeated-entry triple. The middle element has no corner hypothesis. -/
theorem symm_associator_eq_jordanTriple_of_square_zero {X : B}
    (hX : X * X = 0) (Y : B) :
    anticomm (anticomm Y X) X - anticomm Y (anticomm X X) =
      jordanTriple X Y X := by
  simpa only [anticomm, jordanTriple, hX, zero_add, add_zero, zero_mul,
    mul_zero, sub_zero, two_nsmul, add_comm] using
    InfoGeometry.Core.JordanAssociator.symm_quadratic_sandwich X Y

/-- The uploaded corner associator is the generic square-zero identity at an
upper Peirce corner. Its middle input need not lie in the opposite corner. -/
theorem symm_associator_conePlus {P : B} (hP : P * P = P) (A Y : B) :
    anticomm (anticomm Y (conePlus P A)) (conePlus P A) -
        anticomm Y (anticomm (conePlus P A) (conePlus P A)) =
      jordanTriple (conePlus P A) Y (conePlus P A) :=
  symm_associator_eq_jordanTriple_of_square_zero (conePlus_mul_conePlus hP A A) Y

/-- The same associator identity holds at a lower Peirce corner. -/
theorem symm_associator_coneMinus {P : B} (hP : P * P = P) (C Y : B) :
    anticomm (anticomm Y (coneMinus P C)) (coneMinus P C) -
        anticomm Y (anticomm (coneMinus P C) (coneMinus P C)) =
      jordanTriple (coneMinus P C) Y (coneMinus P C) :=
  symm_associator_eq_jordanTriple_of_square_zero (coneMinus_mul_coneMinus hP C C) Y

end InfoGeometry.OperatorAlgebra.PeirceSpine
