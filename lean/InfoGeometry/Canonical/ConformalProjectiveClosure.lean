import InfoGeometry.Canonical.ConformalInversionCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConformalMobiusJacobian
import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Canonical.ConformalFiveGradeBracketAPI
import InfoGeometry.Canonical.BoundaryProjector
import InfoGeometry.Canonical.NormalOrderedCurrent
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.BoundaryMajoranaCircuitModel
import InfoGeometry.Canonical.MajoranaPHSZeroMode
import InfoGeometry.Canonical.VirasoroWardEquilibrium
import InfoGeometry.Canonical.FiveGradedTwistorIncidence

/-!
# InfoGeometry.Canonical.ConformalProjectiveClosure

Canonical one-line import surface for the conformal projective closure package.

This module is declaration-free and gathers the conformal engine’s
boundary/grade/cocycle owner surfaces through direct imports.

The imported layers are kept separate:

* the five-grade Kantor/projective closure is algebraic;
* the modular/Jacobian/cocycle layer is operator-analytic;
* the boundary object is projection-selected, not an algebraic center;
* the current anomaly is supplied directly by the canonical matrix-unit Wick
  owner theorem and the completed crossing-count current theorem;
* any Riemann-spectrum statement remains a separate spectral conjecture, not a
  consequence of this import surface.
-/
