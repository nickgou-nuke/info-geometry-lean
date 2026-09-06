import Mathlib.Tactic

namespace Omega.SPG

/-- Paper-facing wrapper identifying the path-integral period module with the Stokes period module.
    prop:app-stokes-period-module-path-integral-reconstruction -/
theorem paper_app_stokes_period_module_path_integral_reconstruction
    {PeriodVector : Type} (pathIntegralPeriodModule stokesPeriodModule : Set PeriodVector)
    (pathIntegral_eq_stokes : pathIntegralPeriodModule = stokesPeriodModule) :
    pathIntegralPeriodModule = stokesPeriodModule := by
  exact pathIntegral_eq_stokes

end Omega.SPG
