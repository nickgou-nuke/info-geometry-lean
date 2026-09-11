import InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorLoxodromicModes

/-!
# Rindler/chiral transport into the operator loxodromic readout

The chiral thermal rapidity is the existing real quantity
`inverseTemperature obs * μχ`.  This owner only transports the already proved
Unruh calibration into the existing joint-projector eigenvalue theorem.  It
does not identify wedge, chirality, and Nambu gradings, and it introduces no
new KMS or CAR structure.
-/

namespace InfoGeometry.Canonical.RindlerChiralLoxodromicBridge

open InfoGeometry.Thermodynamics.UnruhTemperature
open InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
open InfoGeometry.Optics.OperatorLoxodromicModes
open InfoGeometry.Optics.SheetWittCircularBasis

theorem rindler_chiral_modeGenerator_mul_jointProjector
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (S : CommutingInvolutions Op) (obs : RindlerObserver)
    (μχ θ : ℝ) (ε σ : Bool) :
    modeGenerator S (inverseTemperature obs * μχ) θ *
        S.jointProjector ε σ =
      algebraMap ℝ Op
          (((2 * Real.pi) / obs.a) * μχ * modeSign ε +
            θ * modeSign σ) * S.jointProjector ε σ := by
  rw [modeGenerator_mul_jointProjector, inverseTemperature_eq]

theorem rindler_equal_energy_occupation_log_ratio
    (obs : RindlerObserver) (E μ μχ : ℝ) :
    Real.log
        (occupationOdds (inverseTemperature obs)
            (effectiveEnergy E μ μχ 1) /
          occupationOdds (inverseTemperature obs)
            (effectiveEnergy E μ μχ (-1))) / 2 =
      ((2 * Real.pi) / obs.a) * μχ := by
  rw [rindler_equal_energy_relative_occupationOdds]
  rw [Real.log_exp]
  ring

/-! The occupation-odds coordinate and the operator projector readout are
identified in one theorem.  No new scalar or commutative operator model is
introduced: the left side is substituted into the native operator action. -/

theorem rindler_equal_energy_occupation_log_ratio_modeGenerator_mul_jointProjector
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (S : CommutingInvolutions Op) (obs : RindlerObserver)
    (E μ μχ θ : ℝ) (ε σ : Bool) :
    modeGenerator S
        (Real.log
            (occupationOdds (inverseTemperature obs)
                (effectiveEnergy E μ μχ 1) /
              occupationOdds (inverseTemperature obs)
                (effectiveEnergy E μ μχ (-1))) / 2) θ *
        S.jointProjector ε σ =
      algebraMap ℝ Op
          (((2 * Real.pi) / obs.a) * μχ * modeSign ε +
            θ * modeSign σ) * S.jointProjector ε σ := by
  rw [rindler_equal_energy_occupation_log_ratio]
  simpa [inverseTemperature_eq] using
    (rindler_chiral_modeGenerator_mul_jointProjector S obs μχ θ ε σ)

end InfoGeometry.Canonical.RindlerChiralLoxodromicBridge
