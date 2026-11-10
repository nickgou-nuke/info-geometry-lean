/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Alternating cubic products in the Peirce operator corner

The source notes identify a cyclic cubic commutator expression and a
three-factor alternating polynomial.  This file isolates that valid statement
inside the associative Peirce operator algebra.  It does not identify this
Lie-algebraic corner calculation with the nonassociative split-octonion
commutator.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The cyclic cubic contraction of three ordered operators. -/
def cyclicCommutatorTriple (X Y Z : B) : B :=
  X * comm Y Z + Y * comm Z X + Z * comm X Y

/-- The degree-three alternating standard polynomial, in the chosen order. -/
def alternatingProduct3 (X Y Z : B) : B :=
  X * Y * Z - X * Z * Y + Y * Z * X - Y * X * Z + Z * X * Y - Z * Y * X

/-- The cyclic commutator contraction is exactly the ordered alternating cubic. -/
theorem cyclicCommutatorTriple_eq_alternatingProduct3 (X Y Z : B) :
    cyclicCommutatorTriple X Y Z = alternatingProduct3 X Y Z := by
  simp only [cyclicCommutatorTriple, alternatingProduct3, comm]
  noncomm_ring

/-- The same cubic can be contracted with the commutators on the right. -/
theorem cyclicCommutatorTriple_eq_right_contraction (X Y Z : B) :
    cyclicCommutatorTriple X Y Z =
      comm Y Z * X + comm Z X * Y + comm X Y * Z := by
  rw [cyclicCommutatorTriple_eq_alternatingProduct3]
  simp only [alternatingProduct3, comm]
  noncomm_ring

/-- Swapping the first two ordered inputs reverses the cubic sign. -/
theorem alternatingProduct3_swap_left (X Y Z : B) :
    alternatingProduct3 Y X Z = - alternatingProduct3 X Y Z := by
  simp only [alternatingProduct3]
  noncomm_ring

/-- Swapping the last two ordered inputs reverses the cubic sign. -/
theorem alternatingProduct3_swap_right (X Y Z : B) :
    alternatingProduct3 X Z Y = - alternatingProduct3 X Y Z := by
  simp only [alternatingProduct3]
  noncomm_ring

/-- Repeated adjacent inputs annihilate the alternating cubic. -/
theorem alternatingProduct3_repeat_left (X Z : B) :
    alternatingProduct3 X X Z = 0 := by
  simp only [alternatingProduct3]
  noncomm_ring

/-- Repeated adjacent inputs annihilate the alternating cubic. -/
theorem alternatingProduct3_repeat_right (X Y : B) :
    alternatingProduct3 X Y Y = 0 := by
  simp only [alternatingProduct3]
  noncomm_ring

/-- A Peirce transition product is supported on the positive diagonal corner. -/
theorem qgtPlus_corner_support {P : B} (hP : P * P = P) (A C : B) :
    P * qgtPlus P A C * P = qgtPlus P A C := by
  simp only [qgtPlus, conePlus, coneMinus]
  peirce_nf hP

/-- The alternating cubic of three positive-sheet transition products stays in
the positive Peirce corner. -/
theorem peirce_alternating_transition_cubic_support {P : B}
    (hP : P * P = P) (A₁ C₁ A₂ C₂ A₃ C₃ : B) :
    P * cyclicCommutatorTriple (qgtPlus P A₁ C₁) (qgtPlus P A₂ C₂)
        (qgtPlus P A₃ C₃) * P =
      cyclicCommutatorTriple (qgtPlus P A₁ C₁) (qgtPlus P A₂ C₂)
        (qgtPlus P A₃ C₃) := by
  simp only [cyclicCommutatorTriple, comm, qgtPlus, conePlus, coneMinus]
  peirce_nf hP

/-- The ordered alternating cubic is neutral for the Peirce grading when its
three inputs are positive-sheet transition products. -/
theorem peirce_alternating_transition_cubic_neutral {P : B}
    (hP : P * P = P) (A₁ C₁ A₂ C₂ A₃ C₃ : B) :
    comm (invS P)
      (cyclicCommutatorTriple (qgtPlus P A₁ C₁) (qgtPlus P A₂ C₂)
        (qgtPlus P A₃ C₃)) = 0 := by
  simp only [cyclicCommutatorTriple, comm, invS, qgtPlus, conePlus, coneMinus]
  peirce_nf hP

/-- Reversing the last two transition links negates the oriented cubic while
keeping it in the same Peirce corner. This is the corner-valued orientation
law for three noncommuting transitions. -/
theorem peirce_alternating_transition_cubic_orientation {P : B}
    (hP : P * P = P) (A₁ C₁ A₂ C₂ A₃ C₃ : B) :
    P * cyclicCommutatorTriple (qgtPlus P A₁ C₁) (qgtPlus P A₃ C₃)
        (qgtPlus P A₂ C₂) * P =
      -cyclicCommutatorTriple (qgtPlus P A₁ C₁) (qgtPlus P A₂ C₂)
        (qgtPlus P A₃ C₃) := by
  rw [peirce_alternating_transition_cubic_support hP]
  calc
    cyclicCommutatorTriple (qgtPlus P A₁ C₁) (qgtPlus P A₃ C₃)
        (qgtPlus P A₂ C₂) =
      alternatingProduct3 (qgtPlus P A₁ C₁) (qgtPlus P A₃ C₃)
        (qgtPlus P A₂ C₂) := cyclicCommutatorTriple_eq_alternatingProduct3 _ _ _
    _ = -alternatingProduct3 (qgtPlus P A₁ C₁) (qgtPlus P A₂ C₂)
        (qgtPlus P A₃ C₃) := alternatingProduct3_swap_right _ _ _
    _ = -cyclicCommutatorTriple (qgtPlus P A₁ C₁) (qgtPlus P A₂ C₂)
        (qgtPlus P A₃ C₃) := by rw [cyclicCommutatorTriple_eq_alternatingProduct3]

end InfoGeometry.OperatorAlgebra.PeirceSpine
