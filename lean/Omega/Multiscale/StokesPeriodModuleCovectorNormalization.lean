import Mathlib.Tactic

namespace Omega.Multiscale

/-- Concrete carrier for the Stokes period module and its covector-union model. -/
structure StokesPeriodModuleCovectorNormalizationData where
  PeriodVector : Type
  stokesPeriodModule : Set PeriodVector
  covectorUnion : Set PeriodVector

/-- The covector normalization is the supplied equality of the two concrete set models. -/
theorem paper_app_stokes_period_module_covector_normalization
    (D : StokesPeriodModuleCovectorNormalizationData)
    (stokesPeriodModule_eq_covectorUnion :
      D.stokesPeriodModule = D.covectorUnion) :
    D.stokesPeriodModule = D.covectorUnion :=
  stokesPeriodModule_eq_covectorUnion

end Omega.Multiscale
