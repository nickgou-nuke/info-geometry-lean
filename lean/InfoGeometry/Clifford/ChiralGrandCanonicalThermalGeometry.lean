import InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
import InfoGeometry.Thermodynamics.UnruhTemperature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Thermal readouts of the native two-sheet CAR geometry

The CAR algebra and its noncommutative operators are owned by
`ChiralGrandCanonicalOperatorGeometry`.  This file adds only the scalar
readouts of the already proved mode action: Fermi occupation, occupation
odds, and the reciprocal chiral thermal weights.  No thermal deformation of
the CAR product is introduced.
-/

noncomputable section

namespace InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry

open InfoGeometry.Clifford
open InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
open InfoGeometry.Clifford.ChiralLorentzCARLift
open InfoGeometry.Clifford.ChiralLorentzFockQuadratic
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Thermodynamics.UnruhTemperature

/-- Infinitesimal modular transport in the native operator algebra. -/
def modularDerivation (G : Operator) : Operator →ₗ[ℝ] Operator where
  toFun X := algebraCommutator G X
  map_add' := by
    intro X Y
    unfold algebraCommutator
    rw [mul_add, add_mul]
    abel
  map_smul' := by
    intro r X
    unfold algebraCommutator
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]
    rfl

theorem modularDerivation_apply (G X : Operator) :
    modularDerivation G X = algebraCommutator G X := rfl

theorem modularDerivation_mul (G X Y : Operator) :
    modularDerivation G (X * Y) =
      modularDerivation G X * Y + X * modularDerivation G Y := by
  change algebraCommutator G (X * Y) =
    algebraCommutator G X * Y + X * algebraCommutator G Y
  unfold algebraCommutator
  noncomm_ring

def grandCanonicalDerivation
    (H : Operator) (beta μ μχ : ℝ) : Operator →ₗ[ℝ] Operator :=
  modularDerivation (grandCanonicalModularGenerator H beta μ μχ)

def rindlerGrandCanonicalDerivation
    (obs : RindlerObserver) (H : Operator) (μ μχ : ℝ) :
    Operator →ₗ[ℝ] Operator :=
  grandCanonicalDerivation H (inverseTemperature obs) μ μχ

theorem rindlerGrandCanonicalDerivation_beta
    (obs : RindlerObserver) (H : Operator) (μ μχ : ℝ) :
    rindlerGrandCanonicalDerivation obs H μ μχ =
      grandCanonicalDerivation H ((2 * Real.pi) / obs.a) μ μχ := by
  unfold rindlerGrandCanonicalDerivation
  rw [inverseTemperature_eq]

theorem grandCanonicalDerivation_chiralCharge_zero
    (H : Operator) (beta μ μχ : ℝ)
    (hH : algebraCommutator H chiralCharge = 0) :
    grandCanonicalDerivation H beta μ μχ chiralCharge = 0 := by
  unfold grandCanonicalDerivation modularDerivation
  exact grandCanonicalModularGenerator_commutator_chiralCharge
    H beta μ μχ hH

theorem grandCanonicalDerivation_totalNumber_zero
    (H : Operator) (beta μ μχ : ℝ)
    (hH : algebraCommutator H totalNumber = 0) :
    grandCanonicalDerivation H beta μ μχ totalNumber = 0 := by
  unfold grandCanonicalDerivation modularDerivation
  unfold grandCanonicalModularGenerator
  have hG : algebraCommutator
      (grandCanonicalGenerator H μ μχ) totalNumber = 0 :=
    totalNumber_commutator_of_grandCanonicalGenerator H μ μχ hH
  change algebraCommutator
      (beta • grandCanonicalGenerator H μ μχ) totalNumber = 0
  unfold algebraCommutator at hG ⊢
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [← smul_sub, hG, smul_zero]

theorem grandCanonicalModularGenerator_commutator_totalNumber
    (H : Operator) (beta μ μχ : ℝ)
    (hH : algebraCommutator H totalNumber = 0) :
    algebraCommutator
        (grandCanonicalModularGenerator H beta μ μχ) totalNumber = 0 := by
  change grandCanonicalDerivation H beta μ μχ totalNumber = 0
  exact grandCanonicalDerivation_totalNumber_zero H beta μ μχ hH

theorem rindlerGrandCanonicalDerivation_chiralCharge_zero
    (obs : RindlerObserver) (H : Operator) (μ μχ : ℝ)
    (hH : algebraCommutator H chiralCharge = 0) :
    rindlerGrandCanonicalDerivation obs H μ μχ chiralCharge = 0 := by
  unfold rindlerGrandCanonicalDerivation
  exact grandCanonicalDerivation_chiralCharge_zero
    H (inverseTemperature obs) μ μχ hH

theorem rindlerGrandCanonicalDerivation_totalNumber_zero
    (obs : RindlerObserver) (H : Operator) (μ μχ : ℝ)
    (hH : algebraCommutator H totalNumber = 0) :
    rindlerGrandCanonicalDerivation obs H μ μχ totalNumber = 0 := by
  unfold rindlerGrandCanonicalDerivation
  exact grandCanonicalDerivation_totalNumber_zero
    H (inverseTemperature obs) μ μχ hH

theorem grandCanonicalModularGenerator_conserves_number_and_chiral_charge
    (H : Operator) (beta μ μχ : ℝ)
    (hN : algebraCommutator H totalNumber = 0)
    (hχ : algebraCommutator H chiralCharge = 0) :
    algebraCommutator
        (grandCanonicalModularGenerator H beta μ μχ) totalNumber = 0 ∧
      algebraCommutator
        (grandCanonicalModularGenerator H beta μ μχ) chiralCharge = 0 := by
  exact ⟨grandCanonicalModularGenerator_commutator_totalNumber H beta μ μχ hN,
    grandCanonicalModularGenerator_commutator_chiralCharge H beta μ μχ hχ⟩

/-- Effective one-particle energy on sheet `σ`. -/
def effectiveEnergy (E μ μχ σ : ℝ) : ℝ := E - μ - σ * μχ

@[simp] theorem effectiveEnergy_plus (E μ μχ : ℝ) :
    effectiveEnergy E μ μχ 1 = E - μ - μχ := by
  unfold effectiveEnergy
  ring

@[simp] theorem effectiveEnergy_minus (E μ μχ : ℝ) :
    effectiveEnergy E μ μχ (-1) = E - μ + μχ := by
  unfold effectiveEnergy
  ring

/-- The Fermi occupation readout of a native mode energy. -/
def fermiOccupation (β ξ : ℝ) : ℝ :=
  1 / (Real.exp (β * ξ) + 1)

/-- Occupation odds, with no alteration of the underlying CAR algebra. -/
def occupationOdds (β ξ : ℝ) : ℝ :=
  fermiOccupation β ξ / (1 - fermiOccupation β ξ)

lemma exp_add_one_pos (β ξ : ℝ) :
    0 < Real.exp (β * ξ) + 1 := by
  exact add_pos_of_nonneg_of_pos (le_of_lt (Real.exp_pos _)) zero_lt_one

theorem fermiOccupation_add_complement (β ξ : ℝ) :
    fermiOccupation β ξ +
        Real.exp (β * ξ) / (Real.exp (β * ξ) + 1) = 1 := by
  unfold fermiOccupation
  have h := exp_add_one_pos β ξ
  field_simp [ne_of_gt h]
  ring

theorem occupationOdds_eq_exp_neg (β ξ : ℝ) :
    occupationOdds β ξ = Real.exp (-(β * ξ)) := by
  unfold occupationOdds fermiOccupation
  have h : Real.exp (β * ξ) + 1 ≠ 0 :=
    ne_of_gt (exp_add_one_pos β ξ)
  have hcomp : 1 - 1 / (Real.exp (β * ξ) + 1) =
      Real.exp (β * ξ) / (Real.exp (β * ξ) + 1) := by
    field_simp [h]
    ring
  rw [hcomp]
  field_simp [h, Real.exp_ne_zero]
  rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero _)]

theorem occupationOdds_pos (β ξ : ℝ) :
    0 < occupationOdds β ξ := by
  rw [occupationOdds_eq_exp_neg]
  exact Real.exp_pos _

theorem rindlerOccupationOdds_eq
    (obs : RindlerObserver) (E μ μχ σ : ℝ) :
    occupationOdds (inverseTemperature obs)
        (effectiveEnergy E μ μχ σ) =
      Real.exp (-((2 * Real.pi) / obs.a) *
        effectiveEnergy E μ μχ σ) := by
  rw [occupationOdds_eq_exp_neg, inverseTemperature_eq]
  congr 1
  ring

/-- Thermal Bogoliubov amplitude ratio, defined by the native occupation odds. -/
def thermalAmplitudeRatio (β ξ : ℝ) : ℝ :=
  Real.exp (-(β * ξ) / 2)

theorem thermalAmplitudeRatio_pos (β ξ : ℝ) :
    0 < thermalAmplitudeRatio β ξ := by
  unfold thermalAmplitudeRatio
  exact Real.exp_pos _

theorem thermalAmplitudeRatio_sq (β ξ : ℝ) :
    thermalAmplitudeRatio β ξ ^ 2 = occupationOdds β ξ := by
  rw [occupationOdds_eq_exp_neg]
  unfold thermalAmplitudeRatio
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-! The Bogoliubov angle is a readout of the native CAR thermal odds. -/

def thermalBogoliubovAngle (β ξ : ℝ) : ℝ :=
  Real.arctan (thermalAmplitudeRatio β ξ)

theorem tan_thermalBogoliubovAngle (β ξ : ℝ) :
    Real.tan (thermalBogoliubovAngle β ξ) =
      thermalAmplitudeRatio β ξ := by
  unfold thermalBogoliubovAngle
  exact Real.tan_arctan _

theorem thermalBogoliubovAngle_tan_sq (β ξ : ℝ) :
    Real.tan (thermalBogoliubovAngle β ξ) ^ 2 =
      occupationOdds β ξ := by
  rw [tan_thermalBogoliubovAngle, thermalAmplitudeRatio_sq]

theorem relative_occupationOdds
    (β Eplus Eminus μ μχ : ℝ) :
    occupationOdds β (effectiveEnergy Eplus μ μχ 1) /
        occupationOdds β (effectiveEnergy Eminus μ μχ (-1)) =
      Real.exp (-β * (Eplus - Eminus) + 2 * β * μχ) := by
  rw [occupationOdds_eq_exp_neg, occupationOdds_eq_exp_neg]
  rw [← Real.exp_sub]
  congr 1
  simp only [effectiveEnergy_plus, effectiveEnergy_minus]
  ring

theorem equal_energy_relative_occupationOdds
    (β E μ μχ : ℝ) :
    occupationOdds β (effectiveEnergy E μ μχ 1) /
        occupationOdds β (effectiveEnergy E μ μχ (-1)) =
      Real.exp (2 * β * μχ) := by
  rw [relative_occupationOdds]
  ring_nf

/-- Reciprocal operator-valued chiral thermal weight. -/
def chiralThermalWeight (η : ℝ) : SheetOperatorMatrix :=
  Real.exp η • sheetProjectorPlus +
    Real.exp (-η) • sheetProjectorMinus

theorem chiralThermalWeight_mul_projectorPlus (η : ℝ) :
    chiralThermalWeight η * sheetProjectorPlus =
      Real.exp η • sheetProjectorPlus := by
  unfold chiralThermalWeight
  rw [add_mul, smul_mul_assoc, smul_mul_assoc,
    sheetProjectorPlus_sq, sheetProjectors_mul_reverse,
    smul_zero, add_zero]

theorem chiralThermalWeight_mul_projectorMinus (η : ℝ) :
    chiralThermalWeight η * sheetProjectorMinus =
      Real.exp (-η) • sheetProjectorMinus := by
  unfold chiralThermalWeight
  rw [add_mul, smul_mul_assoc, smul_mul_assoc,
    sheetProjectors_mul, sheetProjectorMinus_sq,
    smul_zero, zero_add]

theorem chiralThermalWeight_mul_sheetNumberMatrixPlus (η : ℝ) :
    chiralThermalWeight η * sheetNumberMatrixPlus =
      Real.exp η • sheetNumberMatrixPlus := by
  unfold chiralThermalWeight
  rw [add_mul, smul_mul_assoc, smul_mul_assoc,
    sheetProjectorPlus_mul_sheetNumberMatrixPlus,
    sheetProjectorMinus_mul_sheetNumberMatrixPlus,
    smul_zero, add_zero]

theorem chiralThermalWeight_mul_sheetNumberMatrixMinus (η : ℝ) :
    chiralThermalWeight η * sheetNumberMatrixMinus =
      Real.exp (-η) • sheetNumberMatrixMinus := by
  unfold chiralThermalWeight
  rw [add_mul, smul_mul_assoc, smul_mul_assoc,
    sheetProjectorPlus_mul_sheetNumberMatrixMinus,
    sheetProjectorMinus_mul_sheetNumberMatrixMinus,
    smul_zero, zero_add]

theorem chiralThermalWeight_mul_neg (η : ℝ) :
    chiralThermalWeight η * chiralThermalWeight (-η) =
      1 := by
  unfold chiralThermalWeight
  simp only [neg_neg, add_mul, mul_add, smul_mul_smul,
    sheetProjectorPlus_sq, sheetProjectors_mul,
    sheetProjectors_mul_reverse, sheetProjectorMinus_sq,
    smul_zero, zero_add, add_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  norm_num [sheetProjectors_add]

theorem chiralThermalWeight_neg_mul (η : ℝ) :
    chiralThermalWeight (-η) * chiralThermalWeight η =
      1 := by
  simpa only [neg_neg] using chiralThermalWeight_mul_neg (-η)

/-- Equal bare energies identify the chiral thermal rapidity with `β μχ`. -/
theorem equal_energy_thermal_rapidity (β μχ : ℝ) :
    Real.log (Real.exp (2 * β * μχ)) / 2 = β * μχ := by
  rw [Real.log_exp]
  ring

theorem rindler_equal_energy_thermal_rapidity
    (obs : RindlerObserver) (μχ : ℝ) :
    Real.log (Real.exp (2 * inverseTemperature obs * μχ)) / 2 =
      ((2 * Real.pi) / obs.a) * μχ := by
  rw [equal_energy_thermal_rapidity, inverseTemperature_eq]

/-! ## Normalized chiral thermal polarization readouts -/

def chiralThermalProbabilityPlus (η : ℝ) : ℝ :=
  Real.exp η / (Real.exp η + Real.exp (-η))

def chiralThermalProbabilityMinus (η : ℝ) : ℝ :=
  Real.exp (-η) / (Real.exp η + Real.exp (-η))

lemma chiralThermalWeight_denominator_pos (η : ℝ) :
    0 < Real.exp η + Real.exp (-η) := by
  exact add_pos (Real.exp_pos _) (Real.exp_pos _)

theorem chiralThermalProbability_add (η : ℝ) :
    chiralThermalProbabilityPlus η + chiralThermalProbabilityMinus η = 1 := by
  unfold chiralThermalProbabilityPlus chiralThermalProbabilityMinus
  have h : Real.exp η + Real.exp (-η) ≠ 0 :=
    ne_of_gt (chiralThermalWeight_denominator_pos η)
  field_simp [h]

theorem chiralThermalProbability_difference (η : ℝ) :
    chiralThermalProbabilityPlus η - chiralThermalProbabilityMinus η =
      Real.tanh η := by
  unfold chiralThermalProbabilityPlus chiralThermalProbabilityMinus
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h : Real.exp η + Real.exp (-η) ≠ 0 :=
    ne_of_gt (chiralThermalWeight_denominator_pos η)
  have h2 : (Real.exp η + Real.exp (-η)) / 2 ≠ 0 := by
    positivity
  field_simp [h, h2]

theorem chiralThermalProbabilityPlus_eq_half_add_tanh (η : ℝ) :
    chiralThermalProbabilityPlus η = (1 + Real.tanh η) / 2 := by
  have hsum := chiralThermalProbability_add η
  have hdiff := chiralThermalProbability_difference η
  linarith

theorem chiralThermalProbabilityMinus_eq_half_sub_tanh (η : ℝ) :
    chiralThermalProbabilityMinus η = (1 - Real.tanh η) / 2 := by
  have hsum := chiralThermalProbability_add η
  have hdiff := chiralThermalProbability_difference η
  linarith

theorem chiralThermalProbabilityPlus_nonneg (η : ℝ) :
    0 ≤ chiralThermalProbabilityPlus η := by
  unfold chiralThermalProbabilityPlus
  positivity

theorem chiralThermalProbabilityMinus_nonneg (η : ℝ) :
    0 ≤ chiralThermalProbabilityMinus η := by
  unfold chiralThermalProbabilityMinus
  positivity

theorem rindlerChiralThermalProbability_difference
    (obs : RindlerObserver) (μχ : ℝ) :
    chiralThermalProbabilityPlus (inverseTemperature obs * μχ) -
        chiralThermalProbabilityMinus (inverseTemperature obs * μχ) =
      Real.tanh (((2 * Real.pi) / obs.a) * μχ) := by
  rw [chiralThermalProbability_difference, inverseTemperature_eq]

theorem rindler_equal_energy_relative_occupationOdds
    (obs : RindlerObserver) (E μ μχ : ℝ) :
    occupationOdds (inverseTemperature obs)
        (effectiveEnergy E μ μχ 1) /
        occupationOdds (inverseTemperature obs)
        (effectiveEnergy E μ μχ (-1)) =
      Real.exp (((4 * Real.pi) / obs.a) * μχ) := by
  rw [equal_energy_relative_occupationOdds, inverseTemperature_eq]
  congr 1
  ring

theorem rindler_thermalAmplitudeRatio_sq
    (obs : RindlerObserver) (E μ μχ σ : ℝ) :
    thermalAmplitudeRatio (inverseTemperature obs)
        (effectiveEnergy E μ μχ σ) ^ 2 =
      Real.exp (-((2 * Real.pi) / obs.a) *
        effectiveEnergy E μ μχ σ) := by
  rw [thermalAmplitudeRatio_sq, rindlerOccupationOdds_eq]

/- The scalar effective energies above are readouts of the native CAR
commutators, rather than an independent diagonal model. -/
theorem freeGenerator_annihilation_plus_effectiveEnergy
    (Eplus Eminus μplus μminus : ℝ) :
    algebraCommutator
        (freeGrandCanonicalGenerator Eplus Eminus μplus μminus) (a 0) =
      -(effectiveEnergy Eplus ((μplus + μminus) / 2)
          ((μplus - μminus) / 2) 1 • a 0) := by
  rw [effectiveEnergy_plus]
  convert freeGrandCanonicalGenerator_commutator_annihilation_plus
    Eplus Eminus μplus μminus using 1; ring_nf

theorem freeGenerator_annihilation_minus_effectiveEnergy
    (Eplus Eminus μplus μminus : ℝ) :
    algebraCommutator
        (freeGrandCanonicalGenerator Eplus Eminus μplus μminus) (a 1) =
      -(effectiveEnergy Eminus ((μplus + μminus) / 2)
          ((μplus - μminus) / 2) (-1) • a 1) := by
  rw [effectiveEnergy_minus]
  convert freeGrandCanonicalGenerator_commutator_annihilation_minus
    Eplus Eminus μplus μminus using 1; ring_nf

theorem freeGenerator_creation_plus_effectiveEnergy
    (Eplus Eminus μplus μminus : ℝ) :
    algebraCommutator
        (freeGrandCanonicalGenerator Eplus Eminus μplus μminus) (adag 0) =
      effectiveEnergy Eplus ((μplus + μminus) / 2)
          ((μplus - μminus) / 2) 1 • adag 0 := by
  rw [effectiveEnergy_plus]
  convert freeGrandCanonicalGenerator_commutator_creation_plus
    Eplus Eminus μplus μminus using 1; ring_nf

theorem freeGenerator_creation_minus_effectiveEnergy
    (Eplus Eminus μplus μminus : ℝ) :
    algebraCommutator
        (freeGrandCanonicalGenerator Eplus Eminus μplus μminus) (adag 1) =
      effectiveEnergy Eminus ((μplus + μminus) / 2)
          ((μplus - μminus) / 2) (-1) • adag 1 := by
  rw [effectiveEnergy_minus]
  convert freeGrandCanonicalGenerator_commutator_creation_minus
    Eplus Eminus μplus μminus using 1; ring_nf

end InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
