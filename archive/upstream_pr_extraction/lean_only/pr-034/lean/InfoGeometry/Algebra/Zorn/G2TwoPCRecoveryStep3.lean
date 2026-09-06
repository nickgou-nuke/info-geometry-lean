import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep3

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2

lemma pc6pc3_basis8_7 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 7) =
      add ePlus (add eMinus (add (basis8 3)
        (add (basis8 6) (basis8 7)))) := by
  change pc3Fun (pc6Fun (basis8 7)) = _
  ext <;> dsimp [add, add2]
  all_goals simp [pc3Fun, pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

end InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep3
