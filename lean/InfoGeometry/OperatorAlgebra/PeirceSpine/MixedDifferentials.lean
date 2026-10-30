import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation

/-!
# Mixed graded derivation identities

Corrected A₃₀ from the consolidated AI Studio packet. Both multiplication
orders are retained. These statements concern endomorphisms of an arbitrary
ring, without an ambient centrality or characteristic hypothesis.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

theorem superDerivPhiBar_square (A C X : B) :
    superDerivPhiBar P A C (superDerivPhiBar P A C X) = connV P A C X := by
  simp only [superDerivPhiBar, superDerivPlusBar, superDerivMinusBar, parityConj, connV]
  peirce_nf hP

theorem superDerivJBar_square (A C X : B) :
    superDerivJBar P A C (superDerivJBar P A C X) = -connV P A C X := by
  simp only [superDerivJBar, superDerivPlusBar, superDerivMinusBar, parityConj, connV]
  peirce_nf hP

theorem superDerivJ_anticomm_bar (A C X : B) :
    superDerivJ P A C (superDerivJBar P A C X) +
      superDerivJBar P A C (superDerivJ P A C X) =
      -((2 : ℤ) • (genV P A C * X + X * genV P A C)) := by
  simp only [superDerivJ, superDerivJBar, superDerivPlus, superDerivMinus, superDerivPlusBar, superDerivMinusBar, parityConj]
  peirce_nf hP

theorem superDerivJ_anticomm_phiBar (A C X : B) :
    superDerivJ P A C (superDerivPhiBar P A C X) +
      superDerivPhiBar P A C (superDerivJ P A C X) = 0 := by
  simp only [superDerivJ, superDerivPhiBar, superDerivPlus, superDerivMinus, superDerivPlusBar, superDerivMinusBar, parityConj]
  peirce_nf hP

theorem superDerivPhi_anticomm_jBar (A C X : B) :
    superDerivPhi P A C (superDerivJBar P A C X) +
      superDerivJBar P A C (superDerivPhi P A C X) = 0 := by
  simp only [superDerivPhi, superDerivJBar, superDerivPlus, superDerivMinus, superDerivPlusBar, superDerivMinusBar, parityConj]
  peirce_nf hP

theorem superDerivPlus_mixed_ordered (A C X : B) :
    superDerivPlus P A (superDerivMinusBar P C X) +
      superDerivPlusBar P A (superDerivMinus P C X) =
      (2 : ℤ) • (qgtPlus P A C * X + X * qgtMinus P A C) := by
  simp only [superDerivPlus, superDerivMinus, superDerivPlusBar, superDerivMinusBar, parityConj, qgtPlus, qgtMinus]
  peirce_nf hP

theorem superDerivMinus_mixed_ordered (A C X : B) :
    superDerivMinus P C (superDerivPlusBar P A X) +
      superDerivMinusBar P C (superDerivPlus P A X) =
      (2 : ℤ) • (qgtMinus P A C * X + X * qgtPlus P A C) := by
  simp only [superDerivPlus, superDerivMinus, superDerivPlusBar, superDerivMinusBar, parityConj, qgtPlus, qgtMinus]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
