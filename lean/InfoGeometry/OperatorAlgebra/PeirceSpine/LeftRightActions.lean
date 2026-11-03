/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation

/-!
# A₃₆: left and parity-twisted right multiplication

The sum and difference of the graded derivation and codifferential are
twice left multiplication and minus twice parity-twisted right
multiplication. Their squares retain the side of multiplication by V.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def diracLeftPhi (P A C X : B) : B :=
  superDerivPhi P A C X + superDerivPhiBar P A C X

def diracRightPhi (P A C X : B) : B :=
  superDerivPhi P A C X - superDerivPhiBar P A C X

theorem diracLeftPhi_eq (P A C X : B) :
    diracLeftPhi P A C X = (2 : ℤ) • (genPhi P A C * X) := by
  simp only [diracLeftPhi, superDerivPhi, superDerivPhiBar,
    superDerivPlus, superDerivMinus, superDerivPlusBar, superDerivMinusBar,
    genPhi, add_mul]
  abel

theorem diracRightPhi_eq (P A C X : B) :
    diracRightPhi P A C X = -((2 : ℤ) • (parityConj P X * genPhi P A C)) := by
  simp only [diracRightPhi, superDerivPhi, superDerivPhiBar,
    superDerivPlus, superDerivMinus, superDerivPlusBar, superDerivMinusBar,
    genPhi, mul_add]
  abel

variable {P : B} (hP : P * P = P)
-- The difference generator has square -V, reversing both square signs.
def diracLeftJ (P A C X : B) : B :=
  superDerivJ P A C X + superDerivJBar P A C X

def diracRightJ (P A C X : B) : B :=
  superDerivJ P A C X - superDerivJBar P A C X

theorem diracLeftJ_eq (P A C X : B) :
    diracLeftJ P A C X = (2 : ℤ) • (genJ P A C * X) := by
  simp only [diracLeftJ, superDerivJ, superDerivJBar,
    superDerivPlus, superDerivMinus, superDerivPlusBar, superDerivMinusBar,
    genJ, sub_mul]
  abel

theorem diracRightJ_eq (P A C X : B) :
    diracRightJ P A C X = -((2 : ℤ) • (parityConj P X * genJ P A C)) := by
  simp only [diracRightJ, superDerivJ, superDerivJBar,
    superDerivPlus, superDerivMinus, superDerivPlusBar, superDerivMinusBar,
    genJ, mul_sub]
  abel

include hP

theorem diracLeftPhi_square (A C X : B) :
    diracLeftPhi P A C (diracLeftPhi P A C X) =
      (4 : ℤ) • (genV P A C * X) := by
  simp only [diracLeftPhi_eq]
  simp only [two_zsmul]
  peirce_nf hP

theorem diracRightPhi_square (A C X : B) :
    diracRightPhi P A C (diracRightPhi P A C X) =
      -((4 : ℤ) • (X * genV P A C)) := by
  simp only [diracRightPhi_eq, parityConj]
  simp only [two_zsmul]
  peirce_nf hP

/-- On the principal right ideal `B P` (elements represented as `X * P`),
the squared left Dirac interaction remains in that ideal. The order of the
operator-valued mass term is retained. -/
theorem diracLeftPhi_square_right_principal_ideal (A C X : B) :
    diracLeftPhi P A C (diracLeftPhi P A C (X * P)) =
      (4 : ℤ) • (genV P A C * X * P) := by
  rw [diracLeftPhi_square hP]
  simp only [mul_assoc]

/-- On the principal left ideal `P B` (elements represented as `P * X`),
the squared parity-twisted right Dirac interaction remains in that ideal.
The right multiplication by the operator-valued mass term is kept on the
right. -/
theorem diracRightPhi_square_left_principal_ideal (A C X : B) :
    diracRightPhi P A C (diracRightPhi P A C (P * X)) =
      -((4 : ℤ) • (P * X * genV P A C)) := by
  rw [diracRightPhi_square hP]

theorem diracLeftRightPhi_anticommute (A C X : B) :
    diracLeftPhi P A C (diracRightPhi P A C X) +
      diracRightPhi P A C (diracLeftPhi P A C X) = 0 := by
  simp only [diracLeftPhi_eq, diracRightPhi_eq, parityConj]
  simp only [two_zsmul]
  peirce_nf hP

theorem diracLeftJ_square (A C X : B) :
    diracLeftJ P A C (diracLeftJ P A C X) =
      -((4 : ℤ) • (genV P A C * X)) := by
  simp only [diracLeftJ_eq]
  simp only [two_zsmul]
  peirce_nf hP

theorem diracRightJ_square (A C X : B) :
    diracRightJ P A C (diracRightJ P A C X) =
      (4 : ℤ) • (X * genV P A C) := by
  simp only [diracRightJ_eq, parityConj]
  simp only [two_zsmul]
  peirce_nf hP

theorem diracLeftRightJ_anticommute (A C X : B) :
    diracLeftJ P A C (diracRightJ P A C X) +
      diracRightJ P A C (diracLeftJ P A C X) = 0 := by
  simp only [diracLeftJ_eq, diracRightJ_eq, parityConj]
  simp only [two_zsmul]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
