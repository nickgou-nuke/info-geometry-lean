/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.UnitriangularBCH3
import InfoGeometry.Clifford.SplitQuaternionCurvature
import InfoGeometry.Geometry.AssociativeCurvatureSquare
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport
import InfoGeometry.Weyl.OperatorBraidingExamples

/-!
# Noncommutative holonomy and curvature owners

This entry point collects the explicit class-two BCH group, quaternion frame,
weighted-permutation plaquette holonomy, and the existing native
Chevalley--Eilenberg connection calculus. Its components have separate
hypotheses; importing them together does not assert a continuum limit or a
Clifford classification.

The Bianchi owner is
`InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.connectionCurvature_bianchi`.
The finite gauge-covariance owner in the same calculus is
`InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.connectionCurvature_gaugeOneForm`.
Both retain the correction from the Lie bracket of derivation directions.
-/
