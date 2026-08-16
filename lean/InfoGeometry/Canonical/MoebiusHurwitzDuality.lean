import InfoGeometry.Geometry.RealMoebiusAction
import InfoGeometry.Canonical.ModularSL2R
import InfoGeometry.Canonical.SplitQuaternionAssociativeCoassociativeCalibrationBridge
import InfoGeometry.OperatorAlgebra.SplitOctonionAssociativeCorner

/-!
# Routing marker: Möbius/quaternionic noncommutative owners

The former file bundled unrelated finite bookkeeping: Mersenne-number
equalities, string labels, a scalar norm readout, and an unconsumed `SU(2)`-style
matrix formula.  None of its declarations had maintained Lean consumers.

The maintained sources for the actual structures are imported above:
`RealMoebiusAction` owns the real fractional-linear action,
`ModularSL2R` owns the noncommutative `M₂(ℝ)` modular triple, and the
quaternionic/split-octonionic owners carry the associative corner and its
nonassociative ambient multiplication.  This file deliberately exports no
second toy correspondence API.
-/
