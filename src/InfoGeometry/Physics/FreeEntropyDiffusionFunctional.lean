import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit free-entropy diffusion functional

This file keeps the free-probability layer as explicit scalar definitions and
kernel-checked algebraic readouts.  It does not assert an induced-gravity
theorem.  The metric equation below is only the residual form of the conditional
balance after the geometric action and the effective stress contributions have
already been defined in concrete downstream models.
-/

namespace InfoGeometry.Physics.FreeEntropyDiffusionFunctional

noncomputable section

/-- One-variable free-energy readout: quadratic confinement minus central-charge
weighted free entropy. -/
def freeEntropyEnergy (centralCharge secondMoment freeEntropy : ℝ) : ℝ :=
  (1 / 2) * secondMoment - centralCharge * freeEntropy

/-- First variation of the explicit free-entropy energy readout. -/
def freeEntropyFirstVariation
    (centralCharge dSecondMoment dFreeEntropy : ℝ) : ℝ :=
  (1 / 2) * dSecondMoment - centralCharge * dFreeEntropy

/-- The first-variation formula is the same linear expression with varied inputs. -/
theorem freeEntropyFirstVariation_eq
    (centralCharge dSecondMoment dFreeEntropy : ℝ) :
    freeEntropyFirstVariation centralCharge dSecondMoment dFreeEntropy =
      (1 / 2) * dSecondMoment - centralCharge * dFreeEntropy := by
  rfl

/-- The central charge carried by a net number of chiral Majorana modes. -/
def majoranaCentralCharge (netChiralMajoranas : ℝ) : ℝ :=
  netChiralMajoranas / 2

/-- Sixteen net chiral Majorana modes carry central charge eight. -/
theorem majoranaCentralCharge_sixteen :
    majoranaCentralCharge 16 = 8 := by
  norm_num [majoranaCentralCharge]

/-- Free-entropy energy scaled by the Majorana central charge. -/
def majoranaFreeEntropyEnergy
    (netChiralMajoranas secondMoment freeEntropy : ℝ) : ℝ :=
  freeEntropyEnergy (majoranaCentralCharge netChiralMajoranas) secondMoment freeEntropy

/-- The 16-Majorana specialization is the `c = 8` free-entropy energy. -/
theorem majoranaFreeEntropyEnergy_sixteen
    (secondMoment freeEntropy : ℝ) :
    majoranaFreeEntropyEnergy 16 secondMoment freeEntropy =
      freeEntropyEnergy 8 secondMoment freeEntropy := by
  simp [majoranaFreeEntropyEnergy, majoranaCentralCharge_sixteen]

/-- Free Fisher production readout in the scalar entropy-flow normalization. -/
def freeFisherProduction (beta fisher : ℝ) : ℝ :=
  (1 / 2) * beta * fisher

/-- Nonnegative inverse-temperature and Fisher information give nonnegative production. -/
theorem freeFisherProduction_nonneg
    {beta fisher : ℝ} (hbeta : 0 ≤ beta) (hfisher : 0 ≤ fisher) :
    0 ≤ freeFisherProduction beta fisher := by
  unfold freeFisherProduction
  nlinarith

/-- Scalar reverse free-diffusion drift driven by the conjugate-variable readout. -/
def reverseFreeDrift (beta operatorReadout conjugateVariable : ℝ) : ℝ :=
  -beta * ((1 / 2) * operatorReadout + conjugateVariable)

/-- Expanding the reverse-drift definition. -/
theorem reverseFreeDrift_eq
    (beta operatorReadout conjugateVariable : ℝ) :
    reverseFreeDrift beta operatorReadout conjugateVariable =
      -beta * ((1 / 2) * operatorReadout + conjugateVariable) := by
  rfl

/-- Effective scalar stress is the sum of incidence, anomaly, and free layers. -/
def effectiveStressScalar (incidence anomaly free : ℝ) : ℝ :=
  incidence + anomaly + free

/-- Scalar Einstein-balance residual for the effective stress readout. -/
def einsteinBalanceResidual
    (einsteinTensor newtonG incidence anomaly free : ℝ) : ℝ :=
  einsteinTensor - (8 * Real.pi * newtonG) *
    effectiveStressScalar incidence anomaly free

/-- Zero residual is exactly the scalar effective Einstein balance. -/
theorem einsteinBalanceResidual_eq_zero_iff
    (einsteinTensor newtonG incidence anomaly free : ℝ) :
    einsteinBalanceResidual einsteinTensor newtonG incidence anomaly free = 0 ↔
      einsteinTensor =
        (8 * Real.pi * newtonG) * effectiveStressScalar incidence anomaly free := by
  unfold einsteinBalanceResidual
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Total variation of the geometric, incidence, anomaly, and free layers. -/
def totalVariation
    (geometric incidence anomaly free : ℝ) : ℝ :=
  geometric + incidence + anomaly + free

/-- Stationarity of the total scalar variation is the vanishing of the explicit sum. -/
theorem totalVariation_stationary_iff
    (geometric incidence anomaly free : ℝ) :
    totalVariation geometric incidence anomaly free = 0 ↔
      geometric + incidence + anomaly + free = 0 := by
  rfl

/-- Hawking-type entropy readout from a temperature derivative of boundary free energy. -/
def boundaryEntropyReadout (dFreeEnergy_dTemperature : ℝ) : ℝ :=
  -dFreeEnergy_dTemperature

/-- Expanding the boundary entropy readout. -/
theorem boundaryEntropyReadout_eq
    (dFreeEnergy_dTemperature : ℝ) :
    boundaryEntropyReadout dFreeEnergy_dTemperature =
      -dFreeEnergy_dTemperature := by
  rfl

end

end InfoGeometry.Physics.FreeEntropyDiffusionFunctional
