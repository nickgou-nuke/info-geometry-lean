import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Clifford.BudinichCliqueSpinor
import InfoGeometry.Clifford.BudinichMaximumCliquePureSpinor
import InfoGeometry.Clifford.BudinichSpinorsNullVectors
import InfoGeometry.Clifford.CrawfordDiracBispinorDensities
import InfoGeometry.Clifford.RealMod8Classification
import InfoGeometry.Clifford.CartanInstance
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.ClNNBilinear
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.FiniteTiltDiracShell
import InfoGeometry.Clifford.FiniteTiltDiracShellChiralSplit
import InfoGeometry.Clifford.Cl11Quaternion
import InfoGeometry.Clifford.ClNNSpecialization
import InfoGeometry.Clifford.Decomposition
import InfoGeometry.Clifford.GeneralizedMetricBField
import InfoGeometry.Clifford.Grading
import InfoGeometry.Clifford.Hestenes
import InfoGeometry.Clifford.Hurwitz3DGeometricAlgebra
import InfoGeometry.Clifford.AlbertBottConformalBridge
import InfoGeometry.Clifford.ThreeDHurwitz
import InfoGeometry.Clifford.Lift
import InfoGeometry.Clifford.MatrixCompat
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Clifford.NeutralPhaseSpaceRankOne
import InfoGeometry.Clifford.Relations
import InfoGeometry.Clifford.Soldering
import InfoGeometry.Clifford.Spacetime
import InfoGeometry.Clifford.STAOperators
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Clifford.SplitQ11Equivariance
import InfoGeometry.Clifford.SplitQ11Sesquilinear
import InfoGeometry.Clifford.SplitQ11PhaseFlip
import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.Clifford.SplitQ11CausalCone
import InfoGeometry.Clifford.SplitQ11ChiralDecomposition
import InfoGeometry.Clifford.SplitCl44CausalEnvelope
import InfoGeometry.Clifford.SplitCl44Complexification
import InfoGeometry.Clifford.SplitCliffordBoundaryPacket
import InfoGeometry.Clifford.Cl44GenerationRotation
import InfoGeometry.Clifford.Cl44C8Comparison
import InfoGeometry.Clifford.Cl44QuaternionSplit
import InfoGeometry.Clifford.Cl44SignatureResidue
import InfoGeometry.Clifford.QuadraticPolarAnticommutator
import InfoGeometry.Krein.Superphysics
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
