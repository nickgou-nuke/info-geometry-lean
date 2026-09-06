import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
import InfoGeometry.Potential.Thermo
import InfoGeometry.Thermodynamics.SouriauTemperature
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge

Bridge packet for the finite prime grand-canonical ensemble with a Souriau
temperature coordinate and a scalar Massieu/Legendre readout.

This file does not assert a new analytic theory for the zeta symmetry group.
It packages the already-owned finite prime ensemble together with the existing
Massieu / Legendre / Bregman thermodynamic layer so that:

* the inverse-temperature readout can be tied to a Souriau temperature;
* the free-energy and entropy identities are exported from the generic
  Legendre model;
* the temperature-regularized Fenchel/Bregman gap is available as a finite
  Hamiltonian defect readout.

No infinite limit, analytic continuation, or RH claim is made here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge

open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
open InfoGeometry.LogPotential
open InfoGeometry.LogPotential.LegendreModel
open InfoGeometry.Thermodynamics

/-! ## 1. Bridge packet -/

/--
Prime grand-canonical Massieu bridge.

`beta` is the real inverse-temperature readout.  The Souriau temperature is
kept separately as a complex coordinate so that the real part can be matched
to the thermodynamic inverse temperature by proof.

`massieuModel` stores the scalar Legendre / Massieu datum for the β-potential
at the chosen chemical potential.
-/
@[rep_depth transport]
structure Bridge where
  P : PrimeRegister
  energyWeight : ℕ → ℝ
  temperature : SouriauTemperature
  chemicalPotential : ℝ
  massieuModel : LegendreModel
  massieu_eq_packet :
    ∀ θ : ℝ, massieuModel.massieu θ = InfoGeometry.GrandCanonical.potentialGC (primeGrandCanonicalParams P energyWeight) θ chemicalPotential
  dualCoord_eq_meanShift :
    ∀ θ : ℝ, massieuModel.dualCoord θ = InfoGeometry.GrandCanonical.meanShift (primeGrandCanonicalParams P energyWeight) θ chemicalPotential

namespace Bridge

variable (B : Bridge)

/-! The inverse-temperature coordinate is derived from the Souriau datum. -/
def beta : ℝ := B.temperature.s.re

/-! ## 2. Bridge readouts -/

/-- The Souriau inverse-temperature readout. -/
@[rep_depth transport]
theorem beta_eq_realPart_of_bridge :
    B.beta = B.temperature.s.re :=
  rfl

/-- The Massieu readout matches the prime grand-canonical potential. -/
@[rep_depth thermo]
theorem massieu_eq_potential (θ : ℝ) :
    B.massieuModel.massieu θ = InfoGeometry.GrandCanonical.potentialGC (primeGrandCanonicalParams B.P B.energyWeight) θ B.chemicalPotential :=
  B.massieu_eq_packet θ

/--
The bridge Massieu readout is the logarithm of the explicit finite Euler
product owned by the prime grand-canonical ensemble.
-/
@[rep_depth thermo]
theorem massieu_eq_log_finiteEulerProduct (θ : ℝ) :
    B.massieuModel.massieu θ =
      Real.log (finiteEulerProduct B.P B.energyWeight θ B.chemicalPotential) := by
  rw [B.massieu_eq_potential θ]
  exact potential_eq_log_finiteEulerProduct
    B.P B.energyWeight θ B.chemicalPotential

/-- The finite bridge Massieu potential is the sum of local log factors. -/
@[rep_depth thermo]
theorem massieu_eq_sum_local_log_finiteEulerProduct (θ : ℝ) :
    B.massieuModel.massieu θ =
      ∑ p ∈ InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister.primes B.P,
        Real.log (1 + Real.exp (-θ * (B.energyWeight p - B.chemicalPotential))) := by
  rw [B.massieu_eq_potential θ]
  exact potential_eq_sum_local_log_finiteEulerProduct
    B.P B.energyWeight θ B.chemicalPotential

/-- The dual coordinate is the mean-shift readout. -/
@[rep_depth thermo]
theorem dualCoord_eq_meanShift_of_bridge (θ : ℝ) :
    B.massieuModel.dualCoord θ = InfoGeometry.GrandCanonical.meanShift (primeGrandCanonicalParams B.P B.energyWeight) θ B.chemicalPotential :=
  B.dualCoord_eq_meanShift θ

/-- The canonical free energy is the scaled negative Massieu potential. -/
@[rep_depth thermo]
theorem canonicalFreeEnergy_eq_beta_scaled_massieu (ε θ : ℝ) :
    B.massieuModel.canonicalFreeEnergy ε θ =
      -ε * InfoGeometry.GrandCanonical.potentialGC (primeGrandCanonicalParams B.P B.energyWeight) θ B.chemicalPotential := by
  calc
    B.massieuModel.canonicalFreeEnergy ε θ = -ε * B.massieuModel.massieu θ := by
      exact B.massieuModel.canonicalFreeEnergy_def ε θ
    _ = -ε * InfoGeometry.GrandCanonical.potentialGC (primeGrandCanonicalParams B.P B.energyWeight) θ B.chemicalPotential := by
      rw [B.massieu_eq_potential θ]

/-- The canonical entropy is the negative entropy readout on the contact model. -/
@[rep_depth thermo]
theorem canonicalEntropy_eq_neg_entropy (θ : ℝ) :
    B.massieuModel.canonicalEntropy θ = -B.massieuModel.entropy θ :=
  B.massieuModel.canonicalEntropy_eq_neg_entropy θ

/-- Contact balance in the Massieu model. -/
@[rep_depth thermo]
theorem contact_balance (θ : ℝ) :
    B.massieuModel.massieu θ + B.massieuModel.φ (B.massieuModel.dualCoord θ)
      = θ * B.massieuModel.dualCoord θ :=
  B.massieuModel.contact_balance θ

/-! ## 3. Temperature-regularized Fenchel/Bregman Hamiltonian -/

/--
Temperature-regularized Hamiltonian defect.

This is the finite β-scaled Fenchel gap used as the Bregman-style regularizer.
It is the thermodynamic defect readout, not a claim about a genuine
infinite-dimensional Hamiltonian.
-/
@[rep_depth thermo]
def temperatureRegularizedHamiltonian
    (ε θ η : ℝ) : ℝ :=
  B.massieuModel.scaledFenchelGap ε θ η

/-- The temperature-regularized Hamiltonian defect is nonnegative. -/
@[rep_depth thermo]
theorem temperatureRegularizedHamiltonian_nonneg
    (ε θ η : ℝ) (hε : 0 ≤ ε) :
    0 ≤ B.temperatureRegularizedHamiltonian ε θ η := by
  unfold temperatureRegularizedHamiltonian
  exact B.massieuModel.scaledFenchelGap_nonneg ε θ η hε

/-- The temperature-regularized Hamiltonian defect vanishes on the contact locus. -/
@[rep_depth thermo]
theorem temperatureRegularizedHamiltonian_eq_zero_at_contact
    (ε θ : ℝ) :
    B.temperatureRegularizedHamiltonian ε θ (B.massieuModel.dualCoord θ) = 0 := by
  unfold temperatureRegularizedHamiltonian
  exact B.massieuModel.scaledFenchelGap_eq_zero_at_contact ε θ

/-- The Fenchel gap is nonnegative at arbitrary coordinates. -/
@[rep_depth thermo]
theorem fenchelGap_nonneg (θ η : ℝ) :
    0 ≤ B.massieuModel.fenchelGap θ η :=
  B.massieuModel.fenchelGap_nonneg θ η

/-- The Fenchel gap vanishes at Legendre contact. -/
@[rep_depth thermo]
theorem fenchelGap_eq_zero_at_contact (θ : ℝ) :
    B.massieuModel.fenchelGap θ (B.massieuModel.dualCoord θ) = 0 :=
  B.massieuModel.fenchelGap_eq_zero_at_contact θ

end Bridge

end InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge
