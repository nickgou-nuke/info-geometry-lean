import InfoGeometry.Algebra.Zorn.G2PeirceParabolicStabilizer
import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

/-!
# Native full flag carrier

The native carrier is the dependent sum of isotropic points and the certified
three-element line fibre through each point.  This file is deliberately
independent of any automorphism action or quotient identification.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber

def NativeFlag := Σ p : OctImIsotropicPoint, LinesThroughPoint p.1

end InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
