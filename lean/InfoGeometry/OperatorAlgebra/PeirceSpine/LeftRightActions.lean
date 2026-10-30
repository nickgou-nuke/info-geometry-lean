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
