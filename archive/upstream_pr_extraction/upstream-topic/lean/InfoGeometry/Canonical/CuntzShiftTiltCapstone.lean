import InfoGeometry.Quantum.CuntzShiftTilt

namespace InfoGeometry.Canonical.CuntzShiftTiltCapstone

open InfoGeometry.Quantum.CuntzShiftTilt

theorem capstone_cuntz_shift_tilt_synthesis
    {R : Type*} [Ring R] [StarRing R]
    (S X Y q : R) (hS : IsCuntzIsometry S)
    (hq_unit : IsUnitaryPhase q) (hq_cent_star : IsCentral (star q)) :
    (CuntzShift S X * CuntzShift S Y = CuntzShift S (X * Y)) ∧
    (IsCuntzIsometry (CuntzTilt S q)) ∧
    (CuntzShift (CuntzTilt S q) X = CuntzShift S X) :=
  grand_cuntz_shift_tilt_synthesis S X Y q hS hq_unit hq_cent_star

end InfoGeometry.Canonical.CuntzShiftTiltCapstone
