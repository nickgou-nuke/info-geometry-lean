/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldBeltramiSmoothFlow
import InfoGeometry.Canonical.ArnoldBeltramiContact
import InfoGeometry.Canonical.ArnoldBeltramiVolume
import InfoGeometry.Canonical.ArnoldBeltramiVolumeCharacters
import InfoGeometry.Canonical.SmoothDiffeomorphismDensityOrbit
import InfoGeometry.Canonical.KLScaleItakuraSaito
import InfoGeometry.Projective.FisherRaoRadialShape
import InfoGeometry.Geometry.RealMatrixFisherRadial

/-!
# Real Arnold flow and information geometry

This integration surface connects the actual Beltrami flow to the native
measure action and its stabilizer. Its imports expose the independently
proved contact, cotangent determinant, Fisher mass/shape, matrix log-determinant
and KL radial identities. Their carriers and normalization conventions remain
explicit; no equivalence of unrelated entropy or Casimir foliations is assumed.
-/

