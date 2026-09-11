import InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor

/-!
# Rindler grand-canonical loxodromic packaging

This owner only packages the already proved Unruh inverse temperature and
chiral thermal rapidity as the hyperbolic parameter of the existing
boost--rotation rotor.  It introduces no new KMS or CAR assertion.
-/

noncomputable section

namespace InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicThermalBridge

open InfoGeometry.Thermodynamics.UnruhTemperature
open InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
open InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor

/-- The Rindler chiral thermal rapidity. -/
def rindlerChiralRapidity (obs : RindlerObserver) (μχ : ℝ) : ℝ :=
  inverseTemperature obs * μχ

theorem rindlerChiralRapidity_eq_acceleration (obs : RindlerObserver) (μχ : ℝ) :
    rindlerChiralRapidity obs μχ = ((2 * Real.pi) / obs.a) * μχ := by
  unfold rindlerChiralRapidity
  rw [inverseTemperature_eq]

theorem rindlerChiralRapidity_eq_thermal_rapidity
    (obs : RindlerObserver) (μχ : ℝ) :
    rindlerChiralRapidity obs μχ =
      Real.log (Real.exp (2 * inverseTemperature obs * μχ)) / 2 := by
  unfold rindlerChiralRapidity
  rw [equal_energy_thermal_rapidity]

/-- The existing loxodromic rotor with its boost parameter fixed by the
Rindler temperature and chiral chemical potential. -/
def rindlerLoxodromicRotor (obs : RindlerObserver) (μχ θ : ℝ) : Operator :=
  loxodromicRotor (rindlerChiralRapidity obs μχ) θ

theorem rindlerLoxodromicRotor_eq_acceleration
    (obs : RindlerObserver) (μχ θ : ℝ) :
    rindlerLoxodromicRotor obs μχ θ =
      loxodromicRotor (((2 * Real.pi) / obs.a) * μχ) θ := by
  unfold rindlerLoxodromicRotor
  rw [rindlerChiralRapidity_eq_acceleration]

theorem rindlerLoxodromicRotor_inverse
    (obs : RindlerObserver) (μχ θ : ℝ) :
    rindlerLoxodromicRotor obs μχ θ *
        loxodromicRotor (-rindlerChiralRapidity obs μχ) (-θ) = 1 := by
  unfold rindlerLoxodromicRotor
  exact loxodromicRotor_mul_neg _ _

theorem rindlerChiralPolarization
    (obs : RindlerObserver) (μχ : ℝ) :
    chiralThermalProbabilityPlus (rindlerChiralRapidity obs μχ) -
        chiralThermalProbabilityMinus (rindlerChiralRapidity obs μχ) =
      Real.tanh (((2 * Real.pi) / obs.a) * μχ) := by
  unfold rindlerChiralRapidity
  exact rindlerChiralThermalProbability_difference obs μχ

theorem chiralThermalProbability_ratio_eq_exp_two (η : ℝ) :
    chiralThermalProbabilityPlus η /
        chiralThermalProbabilityMinus η = Real.exp (2 * η) := by
  unfold chiralThermalProbabilityPlus chiralThermalProbabilityMinus
  have hden : Real.exp η + Real.exp (-η) ≠ 0 :=
    ne_of_gt (chiralThermalWeight_denominator_pos η)
  field_simp [hden, Real.exp_ne_zero]
  rw [← Real.exp_add]
  ring_nf

theorem rindlerChiralThermalProbability_ratio
    (obs : RindlerObserver) (μχ : ℝ) :
    chiralThermalProbabilityPlus (rindlerChiralRapidity obs μχ) /
        chiralThermalProbabilityMinus (rindlerChiralRapidity obs μχ) =
      Real.exp (((4 * Real.pi) / obs.a) * μχ) := by
  rw [chiralThermalProbability_ratio_eq_exp_two,
    rindlerChiralRapidity_eq_acceleration]
  congr 1
  ring_nf

def rindlerLoxodromicMultiplier
    (obs : RindlerObserver) (μχ θ : ℝ) : ℂ :=
  Complex.exp
    (2 * ((rindlerChiralRapidity obs μχ : ℂ) + Complex.I * θ))

theorem rindlerLoxodromicMultiplier_factorization
    (obs : RindlerObserver) (μχ θ : ℝ) :
    rindlerLoxodromicMultiplier obs μχ θ =
      (chiralThermalProbabilityPlus (rindlerChiralRapidity obs μχ) /
          chiralThermalProbabilityMinus (rindlerChiralRapidity obs μχ) : ℂ) *
        Complex.exp (2 * Complex.I * θ) := by
  unfold rindlerLoxodromicMultiplier
  have harg :
      (2 : ℂ) *
          ((rindlerChiralRapidity obs μχ : ℂ) + Complex.I * θ) =
        ((2 * rindlerChiralRapidity obs μχ : ℝ) : ℂ) +
          2 * Complex.I * θ := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  have hratio := congrArg (fun x : ℝ => (x : ℂ))
    (chiralThermalProbability_ratio_eq_exp_two
      (rindlerChiralRapidity obs μχ))
  have hratio' :
      ((chiralThermalProbabilityPlus (rindlerChiralRapidity obs μχ) /
          chiralThermalProbabilityMinus (rindlerChiralRapidity obs μχ) : ℝ) : ℂ) =
        ((Real.exp (2 * rindlerChiralRapidity obs μχ) : ℝ) : ℂ) := by
    exact hratio
  rw [← Complex.ofReal_exp, ← Complex.ofReal_div, hratio']

theorem rindlerLoxodromicMultiplier_acceleration
    (obs : RindlerObserver) (μχ θ : ℝ) :
    rindlerLoxodromicMultiplier obs μχ θ =
      ((Real.exp (((4 * Real.pi) / obs.a) * μχ) : ℝ) : ℂ) *
        Complex.exp (2 * Complex.I * θ) := by
  rw [rindlerLoxodromicMultiplier_factorization,
    ← Complex.ofReal_div, rindlerChiralThermalProbability_ratio]

end InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicThermalBridge

end noncomputable section
