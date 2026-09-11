import InfoGeometry.Twistor.PenroseRealDoubledPeirceSoldering
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

/-!
# Penrose realification to the literal exterior-spinor carrier

The Peirce coordinate owner already fixes the repository's circular ordering.
This file supplies only the missing first arrow to the literal exterior
algebra; the exterior/Zorn equivalence remains owned by the Hodge--Dirac
bridge.  No quadratic or multiplicative compatibility is asserted here.
-/

namespace InfoGeometry.Twistor.PenroseExterior3PeirceBridge

open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenroseRealDoubledPeirceSoldering
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

noncomputable def twistorRealToExterior :
    TwistorCarrier ≃ₗ[ℝ] Exterior3 :=
  penrosePeirceEquiv.trans exterior3SplitOctonionCoordinateEquiv.symm

@[simp] theorem twistorRealToExterior_apply (z : TwistorCarrier) :
    twistorRealToExterior z =
      exterior3SplitOctonionCoordinateEquiv.symm (penrosePeirceEquiv z) := rfl

theorem twistorRealToExterior_coordinate_readback (z : TwistorCarrier) :
    exterior3SplitOctonionCoordinateEquiv (twistorRealToExterior z) =
      penrosePeirceEquiv z := by
  change exterior3SplitOctonionCoordinateEquiv
      (exterior3SplitOctonionCoordinateEquiv.symm (penrosePeirceEquiv z)) = _
  exact exterior3SplitOctonionCoordinateEquiv.apply_symm_apply _

noncomputable def twistorCircularPeirceEquiv :
    TwistorCarrier ≃ₗ[ℝ] CanonicalSplitOctonion :=
  twistorRealToExterior.trans exterior3CircularPeirceEquiv

@[simp] theorem twistorCircularPeirceEquiv_apply (z : TwistorCarrier) :
    twistorCircularPeirceEquiv z =
      exterior3CircularPeirceEquiv (twistorRealToExterior z) := rfl

theorem twistorCircularPeirceEquiv_circularCoordinates (z : TwistorCarrier) :
    InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun
        (twistorCircularPeirceEquiv z) =
      penrosePeirceEquiv z := by
  change
    InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis.equivFun.symm
          (exterior3SplitOctonionCoordinateEquiv
            (exterior3SplitOctonionCoordinateEquiv.symm (penrosePeirceEquiv z)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end InfoGeometry.Twistor.PenroseExterior3PeirceBridge
