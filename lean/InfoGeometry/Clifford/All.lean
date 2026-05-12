import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Clifford.RealMod8Classification
import InfoGeometry.Clifford.CartanInstance
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.ClNNBilinear
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11Quaternion
import InfoGeometry.Clifford.ClNNSpecialization
import InfoGeometry.Clifford.Decomposition
import InfoGeometry.Clifford.GeneralizedMetricBField
import InfoGeometry.Clifford.Grading
import InfoGeometry.Clifford.Hestenes
import InfoGeometry.Clifford.Lift
import InfoGeometry.Clifford.MatrixCompat
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Clifford.NeutralPhaseSpaceRankOne
import InfoGeometry.Clifford.Relations
import InfoGeometry.Clifford.Soldering
import InfoGeometry.Clifford.Spacetime
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Clifford.SplitQ11Equivariance
import InfoGeometry.Clifford.SplitQ11PhaseFlip
import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.Clifford.Supercharge
import InfoGeometry.Clifford.Tower
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Clifford.ChiralBasis
import InfoGeometry.Clifford.HestenesDirac
import InfoGeometry.Clifford.GeometricRotor
import InfoGeometry.Clifford.RealDoubledHestenesAnchor

namespace InfoGeometry

/-!
# InfoGeometry.Clifford.All

Umbrella module for the Clifford algebra layer.

Authority note:

- `ClNN` and its downstream split-tower files own the recursive split
  `Cl(n,n)` presentation,
- `NeutralPhaseSpaceCore` and its downstream bridge files own the corrected
  neutral phase-space lane on `E × E*`,
- both lanes are imported here, but they should not be read as competing roots.
-/

end InfoGeometry
