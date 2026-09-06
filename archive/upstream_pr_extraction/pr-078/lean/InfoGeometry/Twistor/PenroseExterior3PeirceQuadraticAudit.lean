import InfoGeometry.Twistor.PenroseExterior3PeirceBridge
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Quadratic audit for the Penrose/exterior/Peirce soldering

The carrier equivalence is linear, but the repository's current real
coordinate polarization does not identify the diagonal Penrose `(2,2)` form
with the circular Peirce Witt form.  This file records a kernel-checked
counterexample rather than promoting a false norm-intertwining theorem.
-/

namespace InfoGeometry.Twistor.PenroseExterior3PeirceQuadraticAudit

open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenroseRealDoubledPeirceSoldering
open InfoGeometry.Twistor.PenroseExterior3PeirceBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

def twistorCoordinateZero : TwistorCarrier := fun i =>
  if i = 0 then 1 else 0

@[simp] theorem twistorCoordinateZero_realQuadraticForm :
    twistorRealQuadraticForm twistorCoordinateZero = 1 := by
  rw [twistorRealQuadraticForm_apply]
  rw [helicity, twistorHermitian_apply]
  simp [Fin.sum_univ_four, twistorCoordinateZero]

@[simp] theorem twistorCoordinateZero_zornDet :
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (twistorCircularPeirceEquiv twistorCoordinateZero) = 0 := by
  have hcoord := twistorCircularPeirceEquiv_circularCoordinates
    twistorCoordinateZero
  rw [circularPeirceBasis_norm_formula,
    circularPeirceBasis_coordinate_eq_equivFun]
  rw [hcoord]
  simp [penrosePeirceEquiv, twistorCoordinateZero]

theorem twistorCircularPeirceEquiv_not_quadratic_isometry :
    ∃ z : TwistorCarrier,
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          (twistorCircularPeirceEquiv z) ≠
        twistorRealQuadraticForm z := by
  refine ⟨twistorCoordinateZero, ?_⟩
  rw [twistorCoordinateZero_zornDet,
    twistorCoordinateZero_realQuadraticForm]
  norm_num

end InfoGeometry.Twistor.PenroseExterior3PeirceQuadraticAudit
