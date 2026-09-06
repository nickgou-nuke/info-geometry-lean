import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas

/-! CAS-derived image used by the second inverse-peeling step.  It is kept as
    a basis lemma so subsequent recovery proofs do not unfold the full word. -/
lemma pc1Aut_pc6pc2_basis8_7 :
    G2TwoSylowPCAutomorphisms.pc1Aut.1
        (add ePlus (add eMinus (add (basis8 4)
          (add (basis8 6) (basis8 7))))) =
      add ePlus (add eMinus (add (basis8 4)
        (add (basis8 6) (add (basis8 2) (add (basis8 6) (basis8 7)))))) := by
  change G2TwoSylowPCGenerators.pc1Fun _ = _
  ext <;> simp [pc1Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2,
    Bool.xor_left_comm, Bool.xor_comm]

lemma pc1Aut_pc6pc2_basis8_7_reduced :
    G2TwoSylowPCAutomorphisms.pc1Aut.1
        (add ePlus (add eMinus (add (basis8 4)
          (add (basis8 6) (basis8 7))))) =
      add ePlus (add eMinus (add (basis8 4)
        (add (basis8 2) (basis8 7)))) := by
  rw [pc1Aut_pc6pc2_basis8_7]
  ext <;> simp [basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2,
    Bool.xor_left_comm, Bool.xor_comm]

end InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2
