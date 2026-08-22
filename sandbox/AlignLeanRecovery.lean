import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup

namespace AlignLeanRecovery

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

noncomputable def target : SplitOctF2Aut := swap01Aut⁻¹ * pcGenerator 0 * swap01Aut

example : extractBit0 target = false := by
  have hinv : swap01Aut⁻¹ = swap01Aut := by
    rw [inv_eq_iff_mul_eq_one]
    exact swap01Aut_sq
  simp [target, hinv, extractBit0, pcGenerator, pcTermFun,
    swap01Aut_apply,
    InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms.pc1Aut,
    involutiveEquiv,
    swap01Fun, basis8, pc1Fun, pc2Fun, pc3Fun, pc4Fun, pc5Fun, pc6Fun,
    down2]

end AlignLeanRecovery
