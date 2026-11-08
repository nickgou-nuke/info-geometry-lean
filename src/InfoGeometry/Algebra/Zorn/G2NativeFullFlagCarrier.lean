import InfoGeometry.Algebra.Zorn.G2NativeLineFiber
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import Mathlib.Data.Fintype.Sigma

/-!
# Native full flag carrier

The native carrier is the dependent sum of isotropic points and the certified
native line-set fibre through each point.  It is kept distinct from the
intrinsic incidence carrier until an explicit incidence equivalence is proved.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ImaginaryPointAction
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber

def NativeFlag := Σ p : OctImIsotropicPoint, NativeLinesThroughPoint p.1

noncomputable instance : Fintype NativeFlag := by
  dsimp [NativeFlag]
  infer_instance

end InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
