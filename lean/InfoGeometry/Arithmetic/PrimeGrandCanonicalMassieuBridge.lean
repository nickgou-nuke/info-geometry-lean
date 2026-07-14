import Mathlib
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
  packet : PrimeGrandCanonicalPacket
  temperature : SouriauTemperature
  beta : ℝ
  beta_eq_realPart_proof : beta = temperature.s.re
  chemicalPotential : ℝ
  massieuModel : LegendreModel
  massieu_eq_packet_proof :
    ∀ θ : ℝ, massieuModel.massieu θ = packet.potential θ chemicalPotential
  dualCoord_eq_meanShift_proof :
    ∀ θ : ℝ, massieuModel.dualCoord θ = packet.meanShift θ chemicalPotential

namespace Bridge

variable (B : Bridge)

/-! ## 2. Bridge readouts -/

/-- The Souriau inverse-temperature readout. -/
@[rep_depth transport]
theorem beta_eq_realPart_of_bridge :
    B.beta = B.temperature.s.re :=
  B.beta_eq_realPart_proof

/-- The Massieu readout matches the prime grand-canonical potential. -/
@[rep_depth thermo]
theorem massieu_eq_potential (θ : ℝ) :
    B.massieuModel.massieu θ = B.packet.potential θ B.chemicalPotential :=
  B.massieu_eq_packet_proof θ

/-- The dual coordinate is the mean-shift readout. -/
@[rep_depth thermo]
theorem dualCoord_eq_meanShift_of_bridge (θ : ℝ) :
    B.massieuModel.dualCoord θ = B.packet.meanShift θ B.chemicalPotential :=
  B.dualCoord_eq_meanShift_proof θ

/-- The canonical free energy is the scaled negative Massieu potential. -/
@[rep_depth thermo]
theorem canonicalFreeEnergy_eq_beta_scaled_massieu (ε θ : ℝ) :
    B.massieuModel.canonicalFreeEnergy ε θ =
      -ε * B.packet.potential θ B.chemicalPotential := by
  calc
    B.massieuModel.canonicalFreeEnergy ε θ = -ε * B.massieuModel.massieu θ := by
      exact B.massieuModel.canonicalFreeEnergy_def ε θ
    _ = -ε * B.packet.potential θ B.chemicalPotential := by
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
