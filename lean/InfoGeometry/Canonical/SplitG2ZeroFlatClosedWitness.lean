import InfoGeometry.Canonical.SplitG2GaugeHodgeCurvatureBridge

namespace InfoGeometry.Canonical

/-!
# Zero flat/closed property

This is a concrete anchor model for the cellular DAG.  It uses identity edge
transport, empty face boundaries, and zero cochains.  It proves that the
packaged flatness and closedness interfaces are inhabitable without claiming a
nontrivial geometric calibration.
-/

noncomputable def zeroSplitG2GaugeConnection
    {K : FiniteOrientedCellComplex} :
    SplitG2GaugeConnection (K.Cell 1) := fun _ => SplitG2Automorphism.id

noncomputable def zeroSplitG2CovariantCochainData
    (K : FiniteOrientedCellComplex) :
    SplitG2CovariantCochainData K where
  connection := zeroSplitG2GaugeConnection
  faceBoundary := fun _ => []
  covariantCoboundary0 := 0
  covariantCoboundary1 := 0
  curvatureAction := 0
  square_eq_curvature := by
    ext x σ b
    rfl

theorem zeroSplitG2CovariantCochainData_flat
    (K : FiniteOrientedCellComplex) :
    (zeroSplitG2CovariantCochainData K).Flat := by
  rfl

def zeroSplitG2DiscreteHodgeCalibration
    (K : FiniteOrientedCellComplex) :
    SplitG2DiscreteHodgeCalibration K where
  star34 := 0
  phi := 0
  d_phi_zero := by
    simp
  d_star_phi_zero := by
    simp

theorem zeroSplitG2DiscreteHodgeCalibration_torsion_free
    (K : FiniteOrientedCellComplex) :
    rationalCoboundary K 3
        (zeroSplitG2DiscreteHodgeCalibration K).phi = 0 ∧
      rationalCoboundary K 4
        (SplitG2DiscreteHodgeCalibration.psi
          (zeroSplitG2DiscreteHodgeCalibration K)) = 0 := by
  exact SplitG2DiscreteHodgeCalibration.torsion_free_pair
    (zeroSplitG2DiscreteHodgeCalibration K)

noncomputable def zeroSplitG2HodgeCovariantCochainData
    (K : FiniteOrientedCellComplex)
    (H : SplitG2HodgeDualData) :
    SplitG2HodgeCovariantCochainData K where
  base := zeroSplitG2CovariantCochainData K
  hodgeData := H
  hodgeCompatible := by
    intro σ φ
    ext v
    rfl

theorem zeroSplitG2HodgeCovariantCochainData_faceHolonomy
    (K : FiniteOrientedCellComplex)
    (H : SplitG2HodgeDualData)
    (σ : K.Cell 2)
    (φ : SplitG2ThreeForms) :
    pullbackForm 4
        ((zeroSplitG2HodgeCovariantCochainData K H).base.faceHolonomy σ).toLinearEquiv
        (H.star34 φ) =
      H.star34
        (pullbackForm 3
          ((zeroSplitG2HodgeCovariantCochainData K H).base.faceHolonomy σ).toLinearEquiv φ) := by
  exact (zeroSplitG2HodgeCovariantCochainData K H).hodgeCompatible σ φ

end InfoGeometry.Canonical
