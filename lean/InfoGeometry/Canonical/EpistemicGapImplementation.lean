/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.RealSupportLogarithm
import InfoGeometry.OperatorAlgebra.UnboundedHilbertStrongGenerator
import InfoGeometry.OperatorAlgebra.RealL2BoundedTransform
import InfoGeometry.Canonical.ClosedTomitaAdjointSquare
import InfoGeometry.Clifford.FiniteRealFockIsometricTransport
import InfoGeometry.Canonical.AttentionFisherQuotient
import InfoGeometry.Canonical.SouriauKKSRadicalQuotient
import InfoGeometry.Geometry.CotangentDiracCE
import InfoGeometry.Canonical.AtiyahBottShapiroHemisphere
import InfoGeometry.Canonical.ABSZeroStepModuleComparison
import InfoGeometry.Routing.FiniteLogSinkhornConvergence
import InfoGeometry.Physics.SinkhornRelativeEntropyProjection
import InfoGeometry.Physics.SinkhornTotalSupport
import InfoGeometry.Physics.SinkhornKLExamples
import InfoGeometry.Canonical.SinkhornFoundation

/-!
# Explicit analytic and algebraic owners from the epistemic gap audit

This import surface exposes the constructions recorded in
`docs/EPISTEMIC_GAP_IMPLEMENTATION_20261126.md`. Each owner retains its actual
carrier and hypotheses: finite-dimensional positive support, the original
real Hilbert space and maximal operator domain, native exterior/Clifford
modules, radical quotients, and the genuine matrix normalization recurrence.

The imports do not assert identifications among these different carriers.
In particular, they do not supply a smooth coadjoint orbit, a continuous
crossed product, a complex Tomita polar decomposition, or a full topological
ABS/K-theory comparison.
-/
