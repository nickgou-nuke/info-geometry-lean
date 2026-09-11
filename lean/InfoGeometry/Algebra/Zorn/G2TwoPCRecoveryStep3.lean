import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

lemma peel2_basis8_7_readback (f : SplitOctF2Aut) :
    (peel2 f).1 (basis8 7) =
      if (f.1 (basis8 7)).x1 then
        f.1 (add ePlus (add eMinus (add (basis8 3)
          (add (basis8 6) (basis8 7)))))
      else f.1 (basis8 7) := by
  dsimp [peel2]
  split
  · rw [automorphism_mul_apply, pc6pc3_basis8_7]
  · rfl

lemma pc6pc3_basis8_5 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 5) = basis8 5 := by
  ext <;> rfl

lemma peel2_basis8_5 (f : SplitOctF2Aut) :
    (peel2 f).1 (basis8 5) = f.1 (basis8 5) := by
  dsimp [peel2]
  split
  · rw [automorphism_mul_apply, pc6pc3_basis8_5]
  · rfl

end InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep3
