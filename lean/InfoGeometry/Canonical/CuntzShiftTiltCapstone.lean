import InfoGeometry.Quantum.CuntzShiftTilt
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.CuntzShiftTiltCapstone

open InfoGeometry.Quantum.CuntzShiftTilt

theorem capstone_cuntz_shift_tilt_synthesis
    {R : Type*} [Ring R] [StarRing R]
    (S X Y q : R) (hS : IsCuntzIsometry S)
    (hq_unit : IsUnitaryPhase q) (hq_cent_star : IsCentral (star q)) :
    (CuntzShift S X * CuntzShift S Y = CuntzShift S (X * Y)) ∧
    (IsCuntzIsometry (CuntzTilt S q)) ∧
    (CuntzShift (CuntzTilt S q) X = CuntzShift S X) := by
  exact ⟨shift_multiplicative S X Y hS,
    tilt_is_isometry S q hS hq_unit,
    shift_tilt_invariant S X q hq_unit hq_cent_star⟩

end InfoGeometry.Canonical.CuntzShiftTiltCapstone
