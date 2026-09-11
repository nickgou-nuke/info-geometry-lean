import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.GrandUnification.DrazinAffineCFTBoundary

The concrete central-charge arithmetic for the level-one `so(4,4)` / `D₄`
case lives in `OperatorAlgebra.AffineVirasoroBridge`.  This module does not
package speculative Drazin/Moore--Penrose/CFT boundary data; it only re-exports
the theorem-backed Sugawara calibration from the affine-Virasoro owner.
-/

noncomputable section

namespace InfoGeometry.GrandUnification

/--
Re-export the theorem-safe level-one `so(4,4)` / `D₄` Sugawara calibration
from the affine-Virasoro owner lane.
-/
theorem sugawaraCentralCharge_so44_levelOne :
    InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge
        1 28 6 = 4 :=
  InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge_so44_levelOne

end InfoGeometry.GrandUnification
