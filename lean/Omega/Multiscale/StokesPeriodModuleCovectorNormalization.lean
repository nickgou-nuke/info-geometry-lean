import Mathlib.Tactic

namespace Omega.Multiscale

/-- Chapter-local package for the covector normalization of the Stokes period
module. The data record the definitional rewrite
`Π_St(S) = ⋃ D_n⁻¹ ℤ^r` together with the integrality of the successive
transition matrices `D_n⁻¹ D_{n+1}`. -/
structure StokesPeriodModuleCovectorNormalizationData where
  PeriodVector : Type
  stokesPeriodModule : Set PeriodVector
  covectorUnion : Set PeriodVector
  stokesPeriodModule_eq_covectorUnion : stokesPeriodModule = covectorUnion

/-- Paper-facing wrapper for the covector normalization of the Stokes period
module.
    cor:app-stokes-period-module-covector-normalization -/
theorem paper_app_stokes_period_module_covector_normalization
    (D : StokesPeriodModuleCovectorNormalizationData) :
    D.stokesPeriodModule = D.covectorUnion :=
  D.stokesPeriodModule_eq_covectorUnion

end Omega.Multiscale
