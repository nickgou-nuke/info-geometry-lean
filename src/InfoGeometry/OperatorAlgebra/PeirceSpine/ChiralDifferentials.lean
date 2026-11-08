import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors

/-!
# Graded derivatives of Peirce factors

Dependencies: graded derivations and parity → chiral factors → exact closure
and codifferential residuals. The A₄₃ prose confuses the vanishing of the
codifferential on `Σ` with its vanishing on `1 - Σ`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

/-- The metric factor is closed for the odd graded derivation. -/
theorem superDerivPhi_zetaFactor (A C : B) :
    superDerivPhi P A C (zetaFactor P A C) = 0 := by
  simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj, zetaFactor]
  peirce_nf hP

/-- The even commutator generator is annihilated by the codifferential. -/
theorem superDerivPhiBar_genSig (A C : B) :
    superDerivPhiBar P A C (genSig P A C) = 0 := by
  simp only [superDerivPhiBar, superDerivPlusBar, superDerivMinusBar, parityConj]
  peirce_nf hP

/-- Adding the unit changes the codifferential: the factor has residual `2Φ`. -/
theorem superDerivPhiBar_chiralFactor (A C : B) :
    superDerivPhiBar P A C (chiralFactor P A C) =
      (2 : ℤ) • genPhi P A C := by
  simp only [superDerivPhiBar, superDerivPlusBar, superDerivMinusBar,
    parityConj, chiralFactor]
  peirce_nf hP

/-- Exact characteristic-free condition for the claimed coclosure. -/
theorem chiralFactor_coclosed_iff (A C : B) :
    superDerivPhiBar P A C (chiralFactor P A C) = 0 ↔
      (2 : ℤ) • genPhi P A C = 0 := by
  rw [superDerivPhiBar_chiralFactor hP]

end InfoGeometry.OperatorAlgebra.PeirceSpine
