/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldBeltramiCotangentTransport
import InfoGeometry.Quantum.CotangentVolumeCharacters

/-!
# Determinant characters of the actual Beltrami flow derivative

The native matrix determinant already proved for the spatial Jacobian is
transported to the actual derivative linear equivalence, then to the existing
Euclidean tangent carrier. Its ordinary logarithmic volume vanishes, and its
cotangent relative block character is one. No orthogonality is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldBeltramiVolumeCharacters

open InfoGeometry.Canonical.NavierStokesShearReconstruction
open InfoGeometry.Canonical.ArnoldBeltramiFlow
open InfoGeometry.Canonical.ArnoldBeltramiCotangentTransport
open InfoGeometry.Quantum.CotangentVolumeCharacters
open InfoGeometry.Volume.LogPotential

/-- The derivative linear map is the native linear map of the existing
coordinate Jacobian, as verified by its action on every spatial vector. -/
theorem coordinateTangent_toLinearMap (s t : ℝ) (x : Space) :
    (coordinateTangent s t x).toLinearMap = Matrix.toLin' (flowJacobian s t x) := by
  apply LinearMap.ext
  intro v
  exact (flowJacobian_mulVec s t x v).symm

/-- The existing Jacobian determinant proof gives the native determinant
character of the actual derivative. -/
@[simp] theorem coordinateTangent_det (s t : ℝ) (x : Space) :
    LinearEquiv.det (coordinateTangent s t x) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det (coordinateTangent s t x).toLinearMap = (1 : ℝ)
  rw [coordinateTangent_toLinearMap,
    LinearMap.det_toLin', flowJacobian_det]

/-- The explicit coordinate-to-Euclidean conjugacy preserves that determinant. -/
@[simp] theorem tangentEquiv_det (s t : ℝ) (x : Space) :
    LinearEquiv.det (tangentEquiv s t x) = 1 := by
  change LinearEquiv.det
    ((coordinateEuclidean.symm.trans (coordinateTangent s t x)).trans
      coordinateEuclidean) = 1
  rw [LinearEquiv.det_conj, coordinateTangent_det]

/-- The actual tangent transport has zero ordinary logarithmic volume change. -/
@[simp] theorem tangentEquiv_logAbsVolume (s t : ℝ) (x : Space) :
    LogAbsVolume (tangentEquiv s t x) = 0 := by
  unfold LogAbsVolume Base.VolumeHom
  rw [tangentEquiv_det]
  simp

/-- Its inverse-dual transport has unit relative block character as well. -/
theorem tangentEquiv_relativeBlockCharacter (s t : ℝ) (x : Space) :
    relativeBlockCharacter (tangentEquiv s t x)
      (tangentEquiv s t x).symm.dualMap = 1 := by
  apply relativeBlockCharacter_cotangent_eq_one
  exact tangentEquiv_det s t x

end InfoGeometry.Canonical.ArnoldBeltramiVolumeCharacters
