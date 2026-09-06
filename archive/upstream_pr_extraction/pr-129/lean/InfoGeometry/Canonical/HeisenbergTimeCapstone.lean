import InfoGeometry.Spectral.HeisenbergTime

namespace InfoGeometry.Canonical.HeisenbergTimeCapstone

open InfoGeometry.Spectral.HeisenbergTime

theorem capstone_heisenberg_time_synthesis (E : ℝ) :
    heisenbergTime E = Real.log (E / (2 * Real.pi)) :=
  grand_heisenberg_time_synthesis E

end InfoGeometry.Canonical.HeisenbergTimeCapstone
