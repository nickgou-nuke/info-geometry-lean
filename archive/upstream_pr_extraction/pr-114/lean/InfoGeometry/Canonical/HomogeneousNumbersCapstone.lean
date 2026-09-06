import InfoGeometry.Projective.HomogeneousNumbers

namespace InfoGeometry.Canonical.HomogeneousNumbersCapstone

open InfoGeometry.Projective.HomogeneousNumbers

theorem capstone_homogeneous_numbers_synthesis (x y c : ℝ) (hy : y ≠ 0) (hc : c ≠ 0) :
    (projScale c (projCoord x y)).1 / (projScale c (projCoord x y)).2 = x / y :=
  grand_homogeneous_numbers_synthesis x y c hy hc

end InfoGeometry.Canonical.HomogeneousNumbersCapstone
