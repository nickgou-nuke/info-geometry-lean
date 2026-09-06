import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-!
# Audit of the proposed imaginary cross-product carrier

The coordinate operation `octCross` in the older parabolic file is not the
operation transported by the native split-Zorn automorphisms.  The theorem
below gives an explicit isotropic counterexample for the first PC generator.
Thus this operation cannot be used to transport the 63-point incidence
certificate or to prove a native flag action.
-/

namespace InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit

open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

def testPointU : OctImF2 := fun i => if i = 5 then 1 else 0
def testPointV : OctImF2 := fun i => if i = 2 then 1 else 0

theorem octCross_pc1_not_equivariant :
    octCross (octImAction pc1Aut testPointU) (octImAction pc1Aut testPointV) ≠
      octImAction pc1Aut (octCross testPointU testPointV) := by
  native_decide +revert

end InfoGeometry.Algebra.Zorn.G2CrossProductCarrierAudit
