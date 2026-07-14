import Mathlib
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Thermo.ComplexCircularPolarizationBasis
import InfoGeometry.Thermo.SplitChiralPolarizationBasis
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# InfoGeometry.Arithmetic.ZetaSouriauComplexLift

Formula-as-function complex lift of classical grand-canonical thermodynamics.

This file follows the repository formula/function policy:

* formulas are plain `def`s with explicit arguments;
* theorems call the formula functions directly;
* no sockets, no certificates, no witness fields.

The mathematical move is simple: take the classical real thermodynamic formulas

`q_p = exp(-β(E_p - μ_p))`,
`Z = Σ exp(-β(H - μN))`,
`Φ = log Z`,
`F = -log Z`,
`Ω = -β⁻¹ Φ`,
`D_Φ(x,y) = Φ(x) - Φ(y) - dΦ_y(x - y)`,

and apply the same formulas as analytic functions of a complex Souriau
temperature `s : ℂ`.

The finite partition identities are native theorems. Analytic zeta identities,
functional equations, von Mangoldt series, Lee--Yang/RH statements, and
Hilbert--Pólya claims remain explicit proof obligations outside this file.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.ZetaSouriauComplexLift

open InfoGeometry.Thermo.ComplexCircularPolarizationBasis
open InfoGeometry.Thermo.SplitChiralPolarizationBasis

/-! ## 1. Complex lift of grand-canonical formulas -/

/-- Complex Souriau temperature. In the zeta lane this is the complex `s`. -/
@[rep_depth thermo]
abbrev SouriauTemperature : Type := ℂ

variable {ι : Type*}

/-- Finite fermionic/Fock state over mode labels. -/
@[rep_depth thermo]
abbrev FState (ι : Type*) :=
  InfoGeometry.Arithmetic.PrimonFinite.FState ι

/-- Particle number of a finite Fock state. -/
@[rep_depth thermo]
def particleNumber (S : FState ι) : ℕ :=
  S.card

/-- Classical additive energy formula. -/
@[rep_depth thermo]
def energy (E : ι → ℝ) (S : FState ι) : ℝ :=
  S.sum E

/-- Classical additive chemical-potential formula. -/
@[rep_depth thermo]
def chemicalWork (μ : ι → ℝ) (S : FState ι) : ℝ :=
  S.sum μ

/-- Grand-canonical effective Hamiltonian `K = H - μN`. -/
@[rep_depth thermo]
def hamiltonian (E μ : ι → ℝ) (S : FState ι) : ℝ :=
  energy E S - chemicalWork μ S

/-- Complexified effective Hamiltonian. -/
@[rep_depth thermo]
def hamiltonianC (E μ : ι → ℝ) (S : FState ι) : ℂ :=
  (hamiltonian E μ S : ℂ)

/-- Complex local grand-canonical mode weight `exp(-s(E_p - μ_p))`. -/
@[rep_depth thermo]
def modeWeight
    (s : SouriauTemperature) (E μ : ι → ℝ) (p : ι) : ℂ :=
  Complex.exp (-(s * ((E p - μ p : ℝ) : ℂ)))

lemma modeWeight_ne_zero
    (s : SouriauTemperature) (E μ : ι → ℝ) (p : ι) :
    modeWeight s E μ p ≠ 0 := by
  unfold modeWeight
  exact Complex.exp_ne_zero _

/-- Mode weight factored through the circular polarization basis. -/
@[bridge_target_tag, rep_depth thermo]
theorem modeWeight_eq_circular
    (s : SouriauTemperature) (E μ : ι → ℝ) (p : ι) :
    modeWeight s E μ p =
      circularBoltzmannAmplitude (E p - μ p) s *
        circularBoltzmannPhase (E p - μ p) s := by
  simpa [modeWeight, complexBoltzmannWeight, map_sub, sub_eq_add_neg] using
    complexBoltzmannWeight_eq_circular (E := E p - μ p) s

/-- Circularly polarized local mode weight. -/
@[rep_depth thermo]
def circularModeWeight
    (s : SouriauTemperature) (E μ : ι → ℝ) (p : ι) : ℂ :=
  circularBoltzmannAmplitude (E p - μ p) s *
    circularBoltzmannPhase (E p - μ p) s

/-- Circular mode weight is the same as the original mode weight. -/
@[bridge_target_tag, rep_depth thermo]
theorem circularModeWeight_eq_modeWeight
    (s : SouriauTemperature) (E μ : ι → ℝ) (p : ι) :
    circularModeWeight s E μ p = modeWeight s E μ p := by
  rw [circularModeWeight, modeWeight_eq_circular]

/-- Microstate weight as the product of local mode weights. -/
@[rep_depth thermo]
def microstateWeight [DecidableEq ι]
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) : ℂ :=
  InfoGeometry.Arithmetic.PrimonFinite.weight (modeWeight s E μ) S

/-- Circular microstate weight as the product of circular local weights. -/
@[rep_depth thermo]
def circularMicrostateWeight [DecidableEq ι]
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) : ℂ :=
  InfoGeometry.Arithmetic.PrimonFinite.weight (circularModeWeight s E μ) S

/-- Circular microstate weight equals the original microstate weight. -/
@[bridge_target_tag, rep_depth thermo]
theorem circularMicrostateWeight_eq_microstateWeight [DecidableEq ι]
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) :
    circularMicrostateWeight s E μ S = microstateWeight s E μ S := by
  unfold circularMicrostateWeight microstateWeight
  simp [InfoGeometry.Arithmetic.PrimonFinite.weight,
    circularModeWeight_eq_modeWeight]

lemma microstateWeight_ne_zero [DecidableEq ι]
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) :
    microstateWeight s E μ S ≠ 0 := by
  unfold microstateWeight
  exact InfoGeometry.Arithmetic.PrimonFinite.weight_ne_zero
    (q := modeWeight s E μ) S (fun p _hp => modeWeight_ne_zero s E μ p)

lemma circularMicrostateWeight_ne_zero [DecidableEq ι]
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) :
    circularMicrostateWeight s E μ S ≠ 0 := by
  rw [circularMicrostateWeight_eq_microstateWeight]
  exact microstateWeight_ne_zero s E μ S

/-! ## 2. Split-chiral lift -/

/-- Split-complex rapidity extracted from a complex temperature. -/
@[rep_depth thermo]
def splitTemperature (s : ℂ) : SplitRapidity :=
  ⟨s.re, s.im⟩

/-- Left-moving chiral Boltzmann weight on the split plane. -/
@[rep_depth thermo]
def chiralBoltzmannLeftWeight (E : ℝ) (s : ℂ) : ℝ :=
  splitChiralLeftBoltzmannWeight E (splitTemperature s)

/-- Right-moving chiral Boltzmann weight on the split plane. -/
@[rep_depth thermo]
def chiralBoltzmannRightWeight (E : ℝ) (s : ℂ) : ℝ :=
  splitChiralRightBoltzmannWeight E (splitTemperature s)

/-- Split-chiral Boltzmann weight on the complex temperature plane. -/
@[rep_depth thermo]
def chiralBoltzmannWeight (E : ℝ) (s : ℂ) : ChiralScalar :=
  splitChiralBoltzmannWeight E (splitTemperature s)

/-- The split-chiral Boltzmann weight is the pair of left/right weights. -/
@[bridge_target_tag, rep_depth thermo]
theorem chiralBoltzmannWeight_eq_pair (E : ℝ) (s : ℂ) :
    chiralBoltzmannWeight E s =
      (chiralBoltzmannLeftWeight E s, chiralBoltzmannRightWeight E s) := by
  rfl

/-- Left part of the split-chiral Boltzmann weight. -/
@[bridge_target_tag, rep_depth thermo]
theorem leftPart_chiralBoltzmannWeight (E : ℝ) (s : ℂ) :
    leftPart (chiralBoltzmannWeight E s) = chiralBoltzmannLeftWeight E s := by
  rfl

/-- Right part of the split-chiral Boltzmann weight. -/
@[bridge_target_tag, rep_depth thermo]
theorem rightPart_chiralBoltzmannWeight (E : ℝ) (s : ℂ) :
    rightPart (chiralBoltzmannWeight E s) = chiralBoltzmannRightWeight E s := by
  rfl

/-- Chiral local mode weight. -/
@[rep_depth thermo]
def chiralModeWeight
    (s : SouriauTemperature) (E μ : ι → ℝ) (p : ι) : ChiralScalar :=
  chiralBoltzmannWeight (E p - μ p) s

/-- Chiral microstate weight. -/
@[rep_depth thermo]
def chiralMicrostateWeight [DecidableEq ι]
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) : ChiralScalar :=
  InfoGeometry.Arithmetic.PrimonFinite.weight (chiralModeWeight s E μ) S

/-- Chiral local weight reduces to the split thermodynamic basis. -/
@[bridge_target_tag, rep_depth thermo]
theorem chiralModeWeight_eq_splitChiralBoltzmannWeight
    (s : SouriauTemperature) (E μ : ι → ℝ) (p : ι) :
    chiralModeWeight s E μ p =
      splitChiralBoltzmannWeight (E p - μ p) (splitTemperature s) := by
  rfl

/-- Chiral microstate weight reduces to the split thermodynamic basis. -/
@[bridge_target_tag, rep_depth thermo]
theorem chiralMicrostateWeight_eq_split [DecidableEq ι]
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) :
    chiralMicrostateWeight s E μ S =
      InfoGeometry.Arithmetic.PrimonFinite.weight
        (fun p => splitChiralBoltzmannWeight (E p - μ p) (splitTemperature s)) S := by
  rfl

section FiniteModes

variable [DecidableEq ι]

/-- Finite fermionic grand-canonical partition. -/
@[rep_depth thermo]
def fermionPartition
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ) : ℂ :=
  InfoGeometry.Arithmetic.PrimonFinite.ZF modes (modeWeight s E μ)

/-- Finite signed/Möbius supertrace. -/
@[rep_depth thermo]
def signedPartition
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ) : ℂ :=
  InfoGeometry.Arithmetic.PrimonFinite.STrF modes (modeWeight s E μ)

/-- Finite bosonic grand-canonical partition as reciprocal Euler factors. -/
@[rep_depth thermo]
def bosonPartition
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ) : ℂ :=
  InfoGeometry.Arithmetic.PrimonFinite.ZB modes (modeWeight s E μ)

/-- Fermionic finite partition product formula. -/
@[bridge_target_tag, rep_depth thermo]
theorem fermionPartition_eq_prod
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ) :
    fermionPartition modes s E μ =
      modes.prod (fun p => 1 + modeWeight s E μ p) := by
  simpa [fermionPartition] using
    (InfoGeometry.Arithmetic.PrimonFinite.ZF_eq_prod
      (modes := modes) (q := modeWeight s E μ))

/-- Fermionic finite partition written in circular polarization coordinates. -/
@[bridge_target_tag, rep_depth thermo]
theorem fermionPartition_eq_circularProd
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ) :
    fermionPartition modes s E μ =
      modes.prod (fun p =>
        1 + circularModeWeight s E μ p) := by
  rw [fermionPartition_eq_prod]
  congr with p
  rw [circularModeWeight_eq_modeWeight]

/-- Signed/Möbius finite partition product formula. -/
@[bridge_target_tag, rep_depth thermo]
theorem signedPartition_eq_prod
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ) :
    signedPartition modes s E μ =
      modes.prod (fun p => 1 - modeWeight s E μ p) := by
  simpa [signedPartition] using
    (InfoGeometry.Arithmetic.PrimonFinite.STrF_eq_prod
      (modes := modes) (q := modeWeight s E μ))

/-- Signed/Möbius finite partition written in circular polarization coordinates. -/
@[bridge_target_tag, rep_depth thermo]
theorem signedPartition_eq_circularProd
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ) :
    signedPartition modes s E μ =
      modes.prod (fun p =>
        1 - circularModeWeight s E μ p) := by
  rw [signedPartition_eq_prod]
  congr with p
  rw [circularModeWeight_eq_modeWeight]

/-- Bosonic finite partition product formula. -/
@[bridge_target_tag, rep_depth thermo]
theorem bosonPartition_eq_prod_inv
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ) :
    bosonPartition modes s E μ =
      modes.prod (fun p => (1 - modeWeight s E μ p)⁻¹) := by
  rfl

omit [DecidableEq ι] in
lemma bosonPartition_ne_zero
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ)
    (h : ∀ p ∈ modes, (1 - modeWeight s E μ p) ≠ 0) :
    bosonPartition modes s E μ ≠ 0 := by
  exact InfoGeometry.Arithmetic.PrimonFinite.ZB_ne_zero
    (modes := modes) (q := modeWeight s E μ) h

/-- Bosonic finite partition written in circular polarization coordinates. -/
@[bridge_target_tag, rep_depth thermo]
theorem bosonPartition_eq_circularProd_inv
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ) :
    bosonPartition modes s E μ =
      modes.prod (fun p => (1 - circularModeWeight s E μ p)⁻¹) := by
  rw [bosonPartition_eq_prod_inv]
  congr with p
  rw [circularModeWeight_eq_modeWeight]

/-- Finite boson/signed-fermion cancellation. -/
@[bridge_target_tag, rep_depth thermo]
theorem boson_mul_signedPartition_eq_one
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ)
    (h : ∀ p ∈ modes, (1 - modeWeight s E μ p) ≠ 0) :
    bosonPartition modes s E μ * signedPartition modes s E μ = 1 := by
  rw [bosonPartition_eq_prod_inv, signedPartition_eq_prod]
  rw [← Finset.prod_mul_distrib]
  exact
    InfoGeometry.Arithmetic.PrimonFinite.local_susy_cancellation
      (modes := modes) (q := modeWeight s E μ) h

/-- Normalized finite fermionic density. -/
@[rep_depth thermo]
def density
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ)
    (S : FState ι) : ℂ :=
  microstateWeight s E μ S * (fermionPartition modes s E μ)⁻¹

/-- Normalized finite fermionic density written in circular coordinates. -/
@[rep_depth thermo]
def circularDensity
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ)
    (S : FState ι) : ℂ :=
  circularMicrostateWeight s E μ S *
    (fermionPartition modes s E μ)⁻¹

/-- Circular density equals the original density. -/
@[bridge_target_tag, rep_depth thermo]
theorem circularDensity_eq_density [DecidableEq ι]
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ)
    (S : FState ι) :
    circularDensity modes s E μ S = density modes s E μ S := by
  unfold circularDensity density
  rw [circularMicrostateWeight_eq_microstateWeight]

/-- The finite normalized fermionic density sums to one when `Z_F ≠ 0`. -/
@[bridge_target_tag, rep_depth thermo]
theorem density_sum_eq_one
    (modes : Finset ι) (s : SouriauTemperature) (E μ : ι → ℝ)
    (hZ : fermionPartition modes s E μ ≠ 0) :
    modes.powerset.sum (density modes s E μ) = 1 := by
  calc
    modes.powerset.sum (density modes s E μ) =
        modes.powerset.sum
          (fun S =>
            InfoGeometry.Arithmetic.PrimonFinite.weight (modeWeight s E μ) S *
              (fermionPartition modes s E μ)⁻¹) := by
          simp [density, microstateWeight]
    _ =
        modes.powerset.sum
          (InfoGeometry.Arithmetic.PrimonFinite.weight (modeWeight s E μ)) *
          (fermionPartition modes s E μ)⁻¹ := by
          rw [← Finset.sum_mul]
    _ = 1 := by
          rw [show modes.powerset.sum
              (InfoGeometry.Arithmetic.PrimonFinite.weight (modeWeight s E μ)) =
              fermionPartition modes s E μ by rfl]
          exact mul_inv_cancel₀ hZ

end FiniteModes


/-! ## 2. Massieu, free energy, and grand potential as functions -/

/-- Massieu--Planck potential `Φ = log Z`. -/
@[rep_depth thermo]
def massieu (Z : ℂ) : ℂ :=
  Complex.log Z

/-- Circular amplitude coordinate of a complex readout. -/
@[rep_depth thermo]
def circularAmplitudeCoord (z : ℂ) : ℂ :=
  InfoGeometry.Thermo.ComplexCircularPolarizationBasis.circleAmplitudeCoord z

/-- Circular phase coordinate of a complex readout. -/
@[rep_depth thermo]
def circularPhaseCoord (z : ℂ) : ℂ :=
  InfoGeometry.Thermo.ComplexCircularPolarizationBasis.circlePhaseCoord z

/-- Circular split of the Massieu readout. -/
@[rep_depth thermo]
def circularMassieuPlus (Z : ℂ) : ℂ :=
  circularAmplitudeCoord (massieu Z)

/-- Circular split of the Massieu phase readout. -/
@[rep_depth thermo]
def circularMassieuMinus (Z : ℂ) : ℂ :=
  circularPhaseCoord (massieu Z)

/-- The Massieu readout reconstructs from its circular split. -/
@[bridge_target_tag, rep_depth thermo]
theorem massieu_circular_reconstruct (Z : ℂ) :
    massieu Z = circularMassieuPlus Z + circularMassieuMinus Z := by
  unfold circularMassieuPlus circularMassieuMinus circularAmplitudeCoord
    circularPhaseCoord
  simpa using
    InfoGeometry.Thermo.ComplexCircularPolarizationBasis.circle_reconstruct
      (massieu Z)

/-- Free energy / barrier potential `F = -log Z`. -/
@[rep_depth thermo]
def freeEnergy (Z : ℂ) : ℂ :=
  -massieu Z

/-- Circular amplitude coordinate of the free energy readout. -/
@[rep_depth thermo]
def circularFreeEnergyPlus (Z : ℂ) : ℂ :=
  circularAmplitudeCoord (freeEnergy Z)

/-- Circular phase coordinate of the free energy readout. -/
@[rep_depth thermo]
def circularFreeEnergyMinus (Z : ℂ) : ℂ :=
  circularPhaseCoord (freeEnergy Z)

/-- The free-energy readout reconstructs from its circular split. -/
@[bridge_target_tag, rep_depth thermo]
theorem freeEnergy_circular_reconstruct (Z : ℂ) :
    freeEnergy Z =
      circularFreeEnergyPlus Z + circularFreeEnergyMinus Z := by
  unfold circularFreeEnergyPlus circularFreeEnergyMinus circularAmplitudeCoord
    circularPhaseCoord
  simpa using
    InfoGeometry.Thermo.ComplexCircularPolarizationBasis.circle_reconstruct
      (freeEnergy Z)

/-- Grand potential `Ω = -s⁻¹ Φ`. -/
@[rep_depth thermo]
def grandPotential (s Z : ℂ) : ℂ :=
  -s⁻¹ * massieu Z

/-- Circular amplitude coordinate of the grand potential readout. -/
@[rep_depth thermo]
def circularGrandPotentialPlus (s Z : ℂ) : ℂ :=
  circularAmplitudeCoord (grandPotential s Z)

/-- Circular phase coordinate of the grand potential readout. -/
@[rep_depth thermo]
def circularGrandPotentialMinus (s Z : ℂ) : ℂ :=
  circularPhaseCoord (grandPotential s Z)

/-- The grand-potential readout reconstructs from its circular split. -/
@[bridge_target_tag, rep_depth thermo]
theorem grandPotential_circular_reconstruct (s Z : ℂ) :
    grandPotential s Z =
      circularGrandPotentialPlus s Z + circularGrandPotentialMinus s Z := by
  unfold circularGrandPotentialPlus circularGrandPotentialMinus
    circularAmplitudeCoord circularPhaseCoord
  simpa using
    InfoGeometry.Thermo.ComplexCircularPolarizationBasis.circle_reconstruct
      (grandPotential s Z)

/-- Direct formula for a partition function `Z : ℂ → ℂ`. -/
@[rep_depth thermo]
def massieuOf (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  massieu (Z s)

/-- Direct formula for `-log Z(s)`. -/
@[rep_depth thermo]
def freeEnergyOf (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  freeEnergy (Z s)

/-- Direct formula for `Ω(s) = -s⁻¹ log Z(s)`. -/
@[rep_depth thermo]
def grandPotentialOf (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  grandPotential s (Z s)

/-- Completed-zeta Massieu/barrier formula `Φ(s) = -log ξ(s)`. -/
@[rep_depth thermo]
def completedMassieu (xi : ℂ → ℂ) (s : ℂ) : ℂ :=
  -Complex.log (xi s)

/-- Log-derivative force formula `-Z'(s)/Z(s)`. -/
@[rep_depth thermo]
def logDerivativeForce (Z dZ : ℂ → ℂ) (s : ℂ) : ℂ :=
  -(dZ s) / (Z s)

/-- Von-Mangoldt force formula when `Z = ζ`. -/
@[rep_depth thermo]
def vonMangoldtForce (zeta dzeta : ℂ → ℂ) (s : ℂ) : ℂ :=
  logDerivativeForce zeta dzeta s

/-- Grand-potential formula unfolds to its Massieu expression. -/
@[bridge_target_tag, rep_depth thermo]
theorem grandPotential_eq_neg_inv_mul_massieu (s Z : ℂ) :
    grandPotential s Z = -s⁻¹ * massieu Z := by
  rfl

/-- `massieuOf` is the Massieu function applied to `Z`. -/
@[bridge_target_tag, rep_depth thermo]
theorem massieuOf_eq (Z : ℂ → ℂ) (s : ℂ) :
    massieuOf Z s = massieu (Z s) := by
  rfl

/-- `freeEnergyOf` is the free-energy function applied to `Z`. -/
@[bridge_target_tag, rep_depth thermo]
theorem freeEnergyOf_eq (Z : ℂ → ℂ) (s : ℂ) :
    freeEnergyOf Z s = freeEnergy (Z s) := by
  rfl

/-- `grandPotentialOf` is the grand-potential function applied to `Z`. -/
@[bridge_target_tag, rep_depth thermo]
theorem grandPotentialOf_eq (Z : ℂ → ℂ) (s : ℂ) :
    grandPotentialOf Z s = grandPotential s (Z s) := by
  rfl

/-- Completed Massieu is definitionally the negative logarithm of `xi`. -/
@[bridge_target_tag, rep_depth thermo]
theorem completedMassieu_eq (xi : ℂ → ℂ) (s : ℂ) :
    completedMassieu xi s = -Complex.log (xi s) := by
  rfl


/-! ## 3. Complex KMS periodicity as a formula theorem -/

section ComplexKMS

variable [DecidableEq ι]

/-- Complex kernel on the finite Fock carrier. -/
@[rep_depth thermo]
abbrev Kernel :=
  FState ι → FState ι → ℂ

/-- Complex grand-canonical thermal weight `exp(-sK(S))`. -/
@[rep_depth thermo]
def thermalWeight
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) : ℂ :=
  Complex.exp (-(s * hamiltonianC E μ S))

omit [DecidableEq ι] in
lemma thermalWeight_ne_zero
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) :
    thermalWeight s E μ S ≠ 0 := by
  unfold thermalWeight
  exact Complex.exp_ne_zero _

/-- Circular split of the complex thermal weight. -/
@[rep_depth thermo]
def circularThermalWeightPlus
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) : ℂ :=
  circularAmplitudeCoord (thermalWeight s E μ S)

/-- Circular phase split of the complex thermal weight. -/
@[rep_depth thermo]
def circularThermalWeightMinus
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) : ℂ :=
  circularPhaseCoord (thermalWeight s E μ S)

/-- The thermal weight reconstructs from its circular split. -/
@[bridge_target_tag, rep_depth thermo]
theorem thermalWeight_circular_reconstruct
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) :
    thermalWeight s E μ S =
      circularThermalWeightPlus s E μ S +
        circularThermalWeightMinus s E μ S := by
  unfold circularThermalWeightPlus circularThermalWeightMinus
    circularAmplitudeCoord circularPhaseCoord
  simpa using
    InfoGeometry.Thermo.ComplexCircularPolarizationBasis.circle_reconstruct
      (thermalWeight s E μ S)

/-- Complex thermal-vacuum half-density `exp(-(s/2)K(S))`. -/
@[rep_depth thermo]
def thermalVacuumAmplitude
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) : ℂ :=
  Complex.exp (-(s / 2 * hamiltonianC E μ S))

omit [DecidableEq ι] in
lemma thermalVacuumAmplitude_ne_zero
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) :
    thermalVacuumAmplitude s E μ S ≠ 0 := by
  unfold thermalVacuumAmplitude
  exact Complex.exp_ne_zero _

/-- Circular split of the thermal-vacuum amplitude. -/
@[rep_depth thermo]
def circularThermalVacuumPlus
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) : ℂ :=
  circularAmplitudeCoord (thermalVacuumAmplitude s E μ S)

/-- Circular phase split of the thermal-vacuum amplitude. -/
@[rep_depth thermo]
def circularThermalVacuumMinus
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) : ℂ :=
  circularPhaseCoord (thermalVacuumAmplitude s E μ S)

/-- The thermal-vacuum amplitude reconstructs from its circular split. -/
@[bridge_target_tag, rep_depth thermo]
theorem thermalVacuumAmplitude_circular_reconstruct
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) :
    thermalVacuumAmplitude s E μ S =
      circularThermalVacuumPlus s E μ S +
        circularThermalVacuumMinus s E μ S := by
  unfold circularThermalVacuumPlus circularThermalVacuumMinus
    circularAmplitudeCoord circularPhaseCoord
  simpa using
    InfoGeometry.Thermo.ComplexCircularPolarizationBasis.circle_reconstruct
      (thermalVacuumAmplitude s E μ S)

/-- Thermal-vacuum amplitude squares to the thermal weight. -/
@[bridge_target_tag, rep_depth thermo]
theorem thermalVacuumAmplitude_mul_self_eq_weight
    (s : SouriauTemperature) (E μ : ι → ℝ) (S : FState ι) :
    thermalVacuumAmplitude s E μ S *
      thermalVacuumAmplitude s E μ S =
    thermalWeight s E μ S := by
  unfold thermalVacuumAmplitude thermalWeight
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Complex imaginary-time modular/KMS shift of a finite kernel. -/
@[rep_depth thermo]
def kmsShift
    (s : SouriauTemperature) (E μ : ι → ℝ)
    (A : Kernel (ι := ι)) : Kernel (ι := ι) :=
  fun S T =>
    Complex.exp (-(s * (hamiltonianC E μ S - hamiltonianC E μ T))) *
      A S T

/--
Finite complex KMS boundary condition:

`ρ(S) A(S,T) = ρ(T) σ_s(A)(S,T)`.
-/
@[bridge_target_tag, rep_depth thermo]
theorem kms_periodicity
    (s : SouriauTemperature) (E μ : ι → ℝ)
    (A : Kernel (ι := ι)) (S T : FState ι) :
    thermalWeight s E μ S * A S T =
      thermalWeight s E μ T * kmsShift s E μ A S T := by
  unfold thermalWeight kmsShift
  have hExp :
      Complex.exp (-(s * hamiltonianC E μ S)) =
        Complex.exp (-(s * hamiltonianC E μ T)) *
          Complex.exp (-(s * (hamiltonianC E μ S - hamiltonianC E μ T))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hExp]
  ring

end ComplexKMS


/-! ## 4. Bregman functions on the complex plane -/

/--
Complex-valued Bregman formula.

This is algebraic. It is not an ordered divergence unless a real readout or
positivity structure is supplied.
-/
@[rep_depth thermo]
def bregman
    (Phi gradPhi : ℂ → ℂ) (x y : ℂ) : ℂ :=
  Phi x - Phi y - gradPhi y * (x - y)

/-- Diagonal vanishing of the complex Bregman formula. -/
@[bridge_target_tag, simp, rep_depth thermo]
theorem bregman_self_eq_zero
    (Phi gradPhi : ℂ → ℂ) (x : ℂ) :
    bregman Phi gradPhi x x = 0 := by
  unfold bregman
  ring

/--
Real-valued Bregman formula on the complex temperature plane.

`firstOrderAt y dy` is the derivative/readout at `y` applied to displacement
`dy`.
-/
@[rep_depth thermo]
def realBregman
    (A : ℂ → ℝ) (firstOrderAt : ℂ → ℂ → ℝ)
    (x y : ℂ) : ℝ :=
  A x - A y - firstOrderAt y (x - y)

/-- Regularized real Bregman formula on the complex temperature plane. -/
@[rep_depth thermo]
def regularizedBregman
    (A : ℂ → ℝ) (firstOrderAt : ℂ → ℂ → ℝ)
    (ε : ℝ) (x y : ℂ) : ℝ :=
  realBregman A firstOrderAt x y + ε * ‖x - y‖ ^ 2

/-- Regularized Bregman nonnegativity from base nonnegativity and `ε ≥ 0`. -/
@[bridge_target_tag, rep_depth thermo]
theorem regularizedBregman_nonneg
    (A : ℂ → ℝ) (firstOrderAt : ℂ → ℂ → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (x y : ℂ)
    (hB : 0 ≤ realBregman A firstOrderAt x y) :
    0 ≤ regularizedBregman A firstOrderAt ε x y := by
  unfold regularizedBregman
  have hdist : 0 ≤ ‖x - y‖ ^ 2 := sq_nonneg _
  exact add_nonneg hB (mul_nonneg hε hdist)


/-! ## 5. Functional equation and zeta-plane symmetry as direct formulas -/

/-- Critical line predicate. -/
@[rep_depth thermo]
def CriticalLine (s : ℂ) : Prop :=
  s.re = (1 / 2 : ℝ)

/-- Functional-equation reflection. -/
@[rep_depth thermo]
def functionalReflection (s : ℂ) : ℂ :=
  1 - s

/-- Conjugation reflection. -/
@[rep_depth thermo]
def conjugationReflection (s : ℂ) : ℂ :=
  star s

/-- Antiunitary fixed-line reflection. -/
@[rep_depth thermo]
def antiunitaryReflection (s : ℂ) : ℂ :=
  1 - star s

/-- The functional reflection is an involution. -/
@[bridge_target_tag, simp, rep_depth thermo]
theorem functionalReflection_involutive (s : ℂ) :
    functionalReflection (functionalReflection s) = s := by
  simp [functionalReflection]

/-- The conjugation reflection is an involution. -/
@[bridge_target_tag, simp, rep_depth thermo]
theorem conjugationReflection_involutive (s : ℂ) :
    conjugationReflection (conjugationReflection s) = s := by
  simp [conjugationReflection]

/-- The antiunitary reflection is an involution. -/
@[bridge_target_tag, simp, rep_depth thermo]
theorem antiunitaryReflection_involutive (s : ℂ) :
    antiunitaryReflection (antiunitaryReflection s) = s := by
  simp [antiunitaryReflection]

/-- The antiunitary fixed locus is the critical line. -/
@[bridge_target_tag, rep_depth thermo]
theorem fixed_antiunitaryReflection_iff_criticalLine (s : ℂ) :
    s = antiunitaryReflection s ↔ CriticalLine s := by
  constructor
  · intro h
    have h_re : s.re = (antiunitaryReflection s).re := by
      exact congrArg Complex.re h
    have h_eq : s.re = 1 - s.re := by
      simpa [antiunitaryReflection] using h_re
    unfold CriticalLine
    nlinarith
  · intro hs
    apply Complex.ext
    · have h_re : (1 - s.re : ℝ) = s.re := by
        rw [hs]
        norm_num
      simpa [antiunitaryReflection] using h_re.symm
    · simp [antiunitaryReflection]

/-- Points on the critical line are fixed by the antiunitary reflection. -/
@[bridge_target_tag, rep_depth thermo]
theorem antiunitaryReflection_eq_self_of_criticalLine
    {s : ℂ} (hs : CriticalLine s) :
    antiunitaryReflection s = s := by
  exact (fixed_antiunitaryReflection_iff_criticalLine s).2 hs |>.symm


/-! ## 6. Prime specialization -/

namespace PrimeSpecialization

open InfoGeometry.Arithmetic.PrimeBitWittenIndex (PrimeRegister)

/-- Prime energy `E_p = log p`. -/
@[rep_depth thermo]
def primeEnergy (p : ℕ) : ℝ :=
  Real.log p

/-- Zero chemical potential. -/
@[rep_depth thermo]
def zeroChemicalPotential (_p : ℕ) : ℝ :=
  0

/-- Complex prime mode weight `exp(-s log p)`. -/
@[rep_depth thermo]
def primeModeWeight (s : ℂ) (p : ℕ) : ℂ :=
  modeWeight s primeEnergy zeroChemicalPotential p

lemma primeModeWeight_ne_zero (s : ℂ) (p : ℕ) :
    primeModeWeight s p ≠ 0 := by
  exact modeWeight_ne_zero s primeEnergy zeroChemicalPotential p

/-- Finite prime bosonic partition. -/
@[rep_depth thermo]
def finitePrimeBosonPartition (P : PrimeRegister) (s : ℂ) : ℂ :=
  bosonPartition P.primes s primeEnergy zeroChemicalPotential

/-- Finite prime signed/Möbius partition. -/
@[rep_depth thermo]
def finitePrimeSignedPartition (P : PrimeRegister) (s : ℂ) : ℂ :=
  signedPartition P.primes s primeEnergy zeroChemicalPotential

/-- Product formula for finite prime bosonic partition. -/
@[bridge_target_tag, rep_depth thermo]
theorem finitePrimeBosonPartition_eq_prod
    (P : PrimeRegister) (s : ℂ) :
    finitePrimeBosonPartition P s =
      P.primes.prod (fun p => (1 - primeModeWeight s p)⁻¹) := by
  rfl

lemma finitePrimeBosonPartition_ne_zero
    (P : PrimeRegister) (s : ℂ)
    (h : ∀ p ∈ P.primes, (1 - primeModeWeight s p) ≠ 0) :
    finitePrimeBosonPartition P s ≠ 0 := by
  exact bosonPartition_ne_zero
    (modes := P.primes) (s := s) (E := primeEnergy) (μ := zeroChemicalPotential) h

/-- Product formula for finite prime signed/Möbius partition. -/
@[bridge_target_tag, rep_depth thermo]
theorem finitePrimeSignedPartition_eq_prod
    (P : PrimeRegister) (s : ℂ) :
    finitePrimeSignedPartition P s =
      P.primes.prod (fun p => 1 - primeModeWeight s p) := by
  exact
    signedPartition_eq_prod
      P.primes s primeEnergy zeroChemicalPotential

/-- Finite prime Massieu--Planck potential. -/
@[rep_depth thermo]
def finitePrimeMassieu (P : PrimeRegister) (s : ℂ) : ℂ :=
  massieu (finitePrimeBosonPartition P s)

/-- Finite prime free energy. -/
@[rep_depth thermo]
def finitePrimeFreeEnergy (P : PrimeRegister) (s : ℂ) : ℂ :=
  freeEnergy (finitePrimeBosonPartition P s)

/-- Finite prime grand potential. -/
@[rep_depth thermo]
def finitePrimeGrandPotential (P : PrimeRegister) (s : ℂ) : ℂ :=
  grandPotential s (finitePrimeBosonPartition P s)

/-- Grand potential formula for the finite prime partition. -/
@[bridge_target_tag, rep_depth thermo]
theorem finitePrimeGrandPotential_eq
    (P : PrimeRegister) (s : ℂ) :
    finitePrimeGrandPotential P s =
      -s⁻¹ * finitePrimeMassieu P s := by
  rfl

end PrimeSpecialization

end InfoGeometry.Arithmetic.ZetaSouriauComplexLift
