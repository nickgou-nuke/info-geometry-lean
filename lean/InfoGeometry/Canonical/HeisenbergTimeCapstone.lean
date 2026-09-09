import InfoGeometry.Spectral.HeisenbergTime

namespace InfoGeometry.Canonical.HeisenbergTimeCapstone

open InfoGeometry.Spectral.HeisenbergTime

theorem capstone_heisenberg_time_synthesis (E : ℝ) :
    heisenbergTime E = Real.log (E / (2 * Real.pi)) := by
  exact heisenberg_time_log_scale E

end InfoGeometry.Canonical.HeisenbergTimeCapstone
