/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.MatrixLogCentering
import InfoGeometry.Spectrometry.ColumnFirstSinkhornCovariance
import InfoGeometry.Spectrometry.SpectralOrientation
import InfoGeometry.Spectrometry.SpectralRestriction
import InfoGeometry.Spectrometry.TwoLineBalancedConstruction
import InfoGeometry.Spectrometry.TwoLineNonasymptoticBounds
import InfoGeometry.Spectrometry.InteriorStepAndRatioSignatures
import InfoGeometry.Spectrometry.ProjectionEnergy

/-!
# Spectral-table factorization and finite balancing

Focused entrypoint for the spectral table bridge. The carrier and theorem
boundaries are recorded in `docs/SPECTRAL_TABLE_BRIDGE_CONTRACT.md`.

This imports finite table centering and its existing matrix owner, additive
log least squares, actual finite Sinkhorn updates, orientation and restriction,
exact two-line balancing, and separate spatial-residual diagnostics.
It makes no general Sinkhorn convergence or physical identification claim.
-/
