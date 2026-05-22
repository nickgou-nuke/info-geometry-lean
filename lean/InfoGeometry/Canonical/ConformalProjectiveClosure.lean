import InfoGeometry.Canonical.ConformalInversionCore
import InfoGeometry.Canonical.ConformalMobiusJacobian
import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Canonical.ConformalFiveGradeBracketAPI
import InfoGeometry.Canonical.BoundaryProjector
import InfoGeometry.Canonical.BoundaryMatrixUnitWick
import InfoGeometry.Canonical.BoundaryCurrentHeisenbergAPI
import InfoGeometry.Canonical.BoundaryMajoranaCircuitModel
import InfoGeometry.Canonical.MajoranaPHSZeroMode
import InfoGeometry.Canonical.VirasoroWardEquilibrium
import InfoGeometry.Canonical.FiveGradedTwistorIncidence

/-!
# InfoGeometry.Canonical.ConformalProjectiveClosure

Canonical one-line import surface for the conformal projective closure package.

This module is declaration-free and re-exports the conformal engine’s
boundary/grade/cocycle surface through direct imports.

The imported layers are kept separate:

* the five-grade Kantor/projective closure is algebraic;
* the modular/Jacobian/cocycle layer is operator-analytic;
* the boundary object is projection-selected, not an algebraic center;
* the current anomaly is supplied by matrix-unit Wick normal ordering and the
  completed crossing-count current theorem;
* any Riemann-spectrum statement remains a separate spectral conjecture, not a
  consequence of this import surface.
-/
