import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Clifford.MonodromyFlowAdapter
import InfoGeometry.Canonical.WedgeBoostModularBridge

/-!
# Hadjiivanov Rindler Modular Bridge

Bridge between the logarithmic-CFT Hadjiivanov monodromy lane and the
Rindler/wedge boost modular lane.

This file does not identify the complex `2 × 2` monodromy matrix with the real
doubled boost operator.  It records the honest shared structure:

- on the LCFT side, one wrap is a phase times a nilpotent parabolic modular flow;
- on the wedge side, modular time is the boost rapidity of the Unruh flow.

The common vocabulary is the modular-flow parameterization, not a literal type
equality of the carriers.
-/

noncomputable section

namespace InfoGeometry.Canonical.HadjiivanovRindlerModularBridge

open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Clifford.MonodromyFlowAdapter
open InfoGeometry.Canonical.WedgeBoostModularBridge
open InfoGeometry.Krein
open InfoGeometry.Dynamics

/-! ## LCFT side: Hadjiivanov monodromy is a modular parabolic flow -/

/-- One Hadjiivanov wrap is the phase-times-parabolic modular flow. -/
theorem hadjiivanovMonodromy_is_modularParabolicFlow (h : ℂ) :
    hadjiivanovMonodromy h =
      lcftPhase h • lcftParabolicFlowStep logShearBase := by
  simpa [lcftParabolicFlowStep] using
    (monodromy_is_parabolic_flow h)

/-- After `n` wraps, the same modular flow parameter accumulates linearly. -/
theorem hadjiivanovMonodromy_pow_is_modularParabolicFlow (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n • lcftParabolicFlowStep ((n : ℂ) * logShearBase) := by
  simpa [lcftParabolicFlowStep] using
    (monodromy_pow_is_compounded_flow h n)

/-!
The scalar parameter bridge is the actual interoperability statement between
the two carrier lanes.  It identifies the LCFT parabolic shear parameter with
the Wick-rotated wedge boost parameter, without identifying the operators.
-/
def lcftParabolicParameterOfModularTime (τmod : ℝ) : ℂ :=
  (τmod : ℂ) * logShearBase

theorem lcftParabolicParameter_eq_wickRotatedWedgeBoost
    (τmod : ℝ) :
    lcftParabolicParameterOfModularTime τmod =
      -Complex.I * (RealTomitaCore.wedgeBoostParameter τmod : ℂ) := by
  simp [lcftParabolicParameterOfModularTime,
    logShearBase, RealTomitaCore.wedgeBoostParameter]
  ring

theorem discrete_lcftParabolicParameter_eq_wickRotatedWedgeBoost
    (n : ℕ) :
    (n : ℂ) * logShearBase =
      -Complex.I *
        (RealTomitaCore.wedgeBoostParameter (n : ℝ) : ℂ) := by
  simpa [lcftParabolicParameterOfModularTime] using
    lcftParabolicParameter_eq_wickRotatedWedgeBoost (τmod := (n : ℝ))

theorem hadjiivanovMonodromy_pow_is_wickRotatedWedgeFlow
    (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        lcftParabolicFlowStep
          (-Complex.I *
            (RealTomitaCore.wedgeBoostParameter (n : ℝ) : ℂ)) := by
  rw [hadjiivanovMonodromy_pow_is_modularParabolicFlow]
  rw [discrete_lcftParabolicParameter_eq_wickRotatedWedgeBoost]

/-! ## Wedge side: modular time is boost rapidity -/

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The wedge side reads the modular flow as the Unruh boost flow. -/
theorem wedgeModularFlow_eq_unruh (τmod : ℝ) :
    unruhFlowOfModularTime (E := E) τmod =
      (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
          • (ContinuousLinearMap.id ℝ (DoubledSpace E))
        + (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
          • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  exact unruhFlowOfModularTime_eq_modular_polynomial (E := E) τmod

/--
Bridge statement: the repo has one modular-flow dictionary, with the LCFT
monodromy on the complex side and the wedge boost on the real doubled side.

This theorem packages the two owner readouts together so downstream code can
cite the modular-flow correspondence from one name.
-/
theorem modularFlow_dictionary
    (h : ℂ) (τmod : ℝ) :
    hadjiivanovMonodromy h =
        lcftPhase h • lcftParabolicFlowStep logShearBase
      ∧
      unruhFlowOfModularTime (E := E) τmod =
        (Real.cosh (RealTomitaCore.wedgeBoostParameter τmod))
          • (ContinuousLinearMap.id ℝ (DoubledSpace E))
        + (Real.sinh (RealTomitaCore.wedgeBoostParameter τmod))
          • InfoGeometry.Dynamics.modularHamiltonian (E := E) := by
  exact ⟨hadjiivanovMonodromy_is_modularParabolicFlow h,
    wedgeModularFlow_eq_unruh (E := E) τmod⟩

end InfoGeometry.Canonical.HadjiivanovRindlerModularBridge
