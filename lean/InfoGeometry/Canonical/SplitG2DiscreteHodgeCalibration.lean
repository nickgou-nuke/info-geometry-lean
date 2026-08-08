import InfoGeometry.Canonical.SplitG2DiscreteCalibrationCohomology

namespace InfoGeometry.Canonical

/-!
# Discrete Hodge-compatible split-`G₂` calibration

This is the first cochain-level torsion-free socket.  The degree `3 → 4`
operator is explicit data on the chosen finite cell complex; it is not inferred
from the pointwise octonion metric.  Closedness is likewise recorded as a
geometric/cellular property, not as a consequence of Moufang identities.
-/

structure SplitG2DiscreteHodgeCalibration (K : FiniteOrientedCellComplex) where
  star34 :
    RationalColorCochain K 3 →ₗ[ℚ] RationalColorCochain K 4
  phi : RationalColorCochain K 3
  d_phi_zero : rationalCoboundary K 3 phi = 0
  d_star_phi_zero :
    rationalCoboundary K 4 (star34 phi) = 0

namespace SplitG2DiscreteHodgeCalibration

def psi {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteHodgeCalibration K) :
    RationalColorCochain K 4 :=
  C.star34 C.phi

theorem psi_eq_star_phi
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteHodgeCalibration K) :
    psi C = C.star34 C.phi := rfl

theorem phi_closed
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteHodgeCalibration K) :
    rationalCoboundary K 3 C.phi = 0 :=
  C.d_phi_zero

theorem psi_closed
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteHodgeCalibration K) :
    rationalCoboundary K 4 (psi C) = 0 := by
  simpa [psi] using C.d_star_phi_zero

theorem torsion_free_pair
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteHodgeCalibration K) :
    rationalCoboundary K 3 C.phi = 0 ∧
      rationalCoboundary K 4 (psi C) = 0 :=
  ⟨C.phi_closed, C.psi_closed⟩

theorem coboundary_sq_on_phi
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteHodgeCalibration K) :
    rationalCoboundary K 4
        (rationalCoboundary K 3 C.phi) = 0 := by
  rw [C.d_phi_zero]
  exact (rationalCoboundary K 4).map_zero

theorem coboundary_sq_on_psi
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteHodgeCalibration K) :
    rationalCoboundary K 5
        (rationalCoboundary K 4 (psi C)) = 0 := by
  rw [C.psi_closed]
  exact (rationalCoboundary K 5).map_zero

end SplitG2DiscreteHodgeCalibration

end InfoGeometry.Canonical
