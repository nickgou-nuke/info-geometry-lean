import InfoGeometry.Canonical.ConformalUnification
import Mathlib.LinearAlgebra.Determinant

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.BerryPhase

open InfoGeometry.Canonical.ConformalUnification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/--
The Information Berry Connection.
Measures the local 'tilt' or rotation of the chiral anomaly `χ`
as we move between belief states.
`A = log |det(χ * dχ)|`.
-/
noncomputable def berryConnection (CI : ConformalInference E) (dCI : ConformalInference E) : ℝ :=
  Real.log (|LinearMap.det (CI.chiralAnomaly * dCI.chiralAnomaly).toLinearMap|)

end InfoGeometry.Canonical.BerryPhase
