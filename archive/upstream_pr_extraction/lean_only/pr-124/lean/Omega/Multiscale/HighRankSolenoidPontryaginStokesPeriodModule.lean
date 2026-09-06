import Mathlib.Tactic

namespace Omega.Multiscale

/-- Carriers and comparison maps for the high-rank solenoid Pontryagin/Stokes construction. -/
structure HighRankSolenoidPontryaginStokesPeriodModuleData where
  Character : Type
  InverseTowerDual : Type
  StokesPeriodModule : Type
  RankOneCharacter : Type
  toInverseTowerDual : Character → InverseTowerDual
  ofInverseTowerDual : InverseTowerDual → Character
  toStokesPeriodModule : InverseTowerDual → StokesPeriodModule
  ofStokesPeriodModule : StokesPeriodModule → InverseTowerDual
  rankOneInclusion : RankOneCharacter → Character
  rankOnePeriodModule : RankOneCharacter → StokesPeriodModule

/-- Pontryagin duality, Stokes-period rigidity, and rank-one compatibility from explicit laws. -/
theorem paper_app_high_rank_solenoid_pontryagin_stokes_period_module
    (D : HighRankSolenoidPontryaginStokesPeriodModuleData)
    (pontryagin_left_inv :
      Function.LeftInverse D.ofInverseTowerDual D.toInverseTowerDual)
    (pontryagin_right_inv :
      Function.RightInverse D.ofInverseTowerDual D.toInverseTowerDual)
    (stokes_left_inv :
      Function.LeftInverse D.ofStokesPeriodModule D.toStokesPeriodModule)
    (stokes_right_inv :
      Function.RightInverse D.ofStokesPeriodModule D.toStokesPeriodModule)
    (rankOneCompatibility :
      ∀ χ : D.RankOneCharacter,
        D.toStokesPeriodModule (D.toInverseTowerDual (D.rankOneInclusion χ)) =
          D.rankOnePeriodModule χ) :
    Nonempty (D.Character ≃ D.InverseTowerDual) ∧
      Nonempty (D.InverseTowerDual ≃ D.StokesPeriodModule) ∧
        (∀ χ : D.RankOneCharacter,
          D.toStokesPeriodModule (D.toInverseTowerDual (D.rankOneInclusion χ)) =
            D.rankOnePeriodModule χ) := by
  let pontryaginEquiv : D.Character ≃ D.InverseTowerDual :=
    { toFun := D.toInverseTowerDual
      invFun := D.ofInverseTowerDual
      left_inv := pontryagin_left_inv
      right_inv := pontryagin_right_inv }
  let stokesEquiv : D.InverseTowerDual ≃ D.StokesPeriodModule :=
    { toFun := D.toStokesPeriodModule
      invFun := D.ofStokesPeriodModule
      left_inv := stokes_left_inv
      right_inv := stokes_right_inv }
  exact ⟨⟨pontryaginEquiv⟩, ⟨stokesEquiv⟩, rankOneCompatibility⟩

end Omega.Multiscale
