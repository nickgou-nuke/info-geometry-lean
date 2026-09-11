import InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Minimal, reusable off-diagonal vocabulary for the ternary carrier. -/

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeMatrixUnitCalculus

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

def e12 : A := g.V1 * star g.V2
def e23 : A := g.V2 * star g.V3
def e31 : A := g.V3 * star g.V1

end InfoGeometry.Canonical.ToeplitzCuntzThreeMatrixUnitCalculus
