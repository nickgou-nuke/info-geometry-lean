import InfoGeometry.Clifford.Cl55CenterMatrixBridge
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv

namespace InfoGeometry.Clifford.Clifford55

/-!
# Scalarity of the native `Cl(5,5)` centre

The matrix centre theorem is already proved in the generic bridge.  This file
instantiates it with the native faithful spinor algebra equivalence; no centre
classification is re-proved here.
-/

theorem cl55_center_scalar
    {z : Cl55} (hz : z ∈ Subalgebra.center ℝ Cl55) :
    ∃ r : ℝ, algebraMap ℝ Cl55 r = z := by
  exact center_scalar_of_algEquiv_matrix cl55SpinorAlgEquiv hz

end InfoGeometry.Clifford.Clifford55
