import Mathlib
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
import InfoGeometry.Potential.Thermo
import InfoGeometry.Thermodynamics.SouriauTemperature
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.BridgeTarget

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
structure PrimeGrandCanonicalMassieuBridge where
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

namespace PrimeGrandCanonicalMassieuBridge

variable (B : PrimeGrandCanonicalMassieuBridge)

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

/-! ## 4. Prime-ensemble theorem wrappers -/

/-- The finite partition function is positive. -/
@[rep_depth thermo]
theorem partition_pos (β μ : ℝ) :
    0 < B.packet.partition β μ :=
  B.packet.partition_pos β μ

/-- The Gibbs weights normalize to one. -/
@[rep_depth thermo]
theorem gibbsWeight_sum_one (β μ : ℝ) :
    ∑ S, B.packet.gibbsWeight β μ S = 1 :=
  B.packet.gibbsWeight_sum_one β μ

/-- β-derivative of the potential. -/
@[rep_depth thermo]
theorem potential_deriv_beta_eq_neg_meanShift (β μ : ℝ) :
    deriv (fun t => B.packet.potential t μ) β = -B.packet.meanShift β μ :=
  B.packet.potential_deriv_beta_eq_neg_meanShift β μ

/-- μ-derivative of the potential. -/
@[rep_depth thermo]
theorem potential_deriv_mu_eq_beta_meanNumber (β μ : ℝ) :
    deriv (fun t => B.packet.potential β t) μ = β * B.packet.meanNumber β μ :=
  B.packet.potential_deriv_mu_eq_beta_meanNumber β μ

/-- β response equals negative mean shift. -/
@[rep_depth thermo]
theorem betaResponse_eq_neg_meanShift (β μ : ℝ) :
    B.packet.betaResponse β μ = -B.packet.meanShift β μ :=
  B.packet.betaResponse_eq_neg_meanShift β μ

/-- μ response equals β times the mean number. -/
@[rep_depth thermo]
theorem muResponse_eq_beta_meanNumber (β μ : ℝ) :
    B.packet.muResponse β μ = β * B.packet.meanNumber β μ :=
  B.packet.muResponse_eq_beta_meanNumber β μ

/-- The ββ Hessian is the shift variance. -/
@[rep_depth thermo]
theorem betaHessian_eq_varianceShift (β μ : ℝ) :
    B.packet.betaHessian β μ =
      InfoGeometry.GrandCanonical.varianceShift B.packet.params β μ :=
  B.packet.betaHessian_eq_varianceShift β μ

/-- The μμ Hessian is the β²-scaled number variance. -/
@[rep_depth thermo]
theorem muHessian_eq_beta_sq_varianceNumber (β μ : ℝ) :
    B.packet.muHessian β μ =
      (β ^ (2 : ℕ)) * InfoGeometry.GrandCanonical.varianceNumber B.packet.params β μ :=
  B.packet.muHessian_eq_beta_sq_varianceNumber β μ

/-- Mixed Hessian symmetry on the finite grand-canonical surface. -/
@[rep_depth thermo]
theorem betaMuHessian_eq_muBetaHessian (β μ : ℝ) :
    B.packet.betaMuHessian β μ = B.packet.muBetaHessian β μ :=
  B.packet.betaMuHessian_eq_muBetaHessian β μ

/-- The response matrix is symmetric. -/
@[rep_depth thermo]
theorem responseMatrix_symmetric (β μ : ℝ) :
    InfoGeometry.GrandCanonical.ResponseMatrix2.Symmetric
      (B.packet.responseMatrix β μ) :=
  B.packet.responseMatrix_symmetric β μ

/-- The response matrix is positive semidefinite when the diagonal minors are. -/
@[rep_depth thermo]
theorem responseMatrix_positiveSemidefinite (β μ : ℝ)
    (hββ : 0 ≤ B.packet.betaHessian β μ)
    (hμμ : 0 ≤ B.packet.muHessian β μ)
    (hdet : 0 ≤ (B.packet.responseMatrix β μ).det) :
    InfoGeometry.GrandCanonical.ResponseMatrix2.PositiveSemidefinite
      (B.packet.responseMatrix β μ) :=
  B.packet.responseMatrix_positiveSemidefinite β μ hββ hμμ hdet

/-- The spinodal locus is the vanishing of the 2D response determinant. -/
@[rep_depth thermo]
theorem spinodal2D_iff_det_eq_zero (β μ : ℝ) :
    B.packet.spinodal2D β μ ↔ (B.packet.responseMatrix β μ).det = 0 :=
  B.packet.spinodal2D_iff_det_eq_zero β μ

/-! ## 5. Owner target -/

/--
Owner target for the finite prime grand-canonical Massieu/Souriau bridge.

This closes the bridge-level identifications:
* Souriau temperature and inverse temperature;
* partition normalization and first derivatives;
* finite Legendre/Bregman regularization on the contact locus.
-/
@[owner_target_tag]
def PrimeGrandCanonicalMassieuOwnerTarget : Prop :=
    ∀ (B : PrimeGrandCanonicalMassieuBridge),
    B.beta = B.temperature.s.re ∧
      0 < B.packet.partition B.beta B.chemicalPotential ∧
      (∑ S, B.packet.gibbsWeight B.beta B.chemicalPotential S = 1) ∧
      (deriv (fun t => B.packet.potential t B.chemicalPotential) B.beta =
        -B.packet.meanShift B.beta B.chemicalPotential) ∧
      (deriv (fun t => B.packet.potential B.beta t) B.chemicalPotential =
        B.beta * B.packet.meanNumber B.beta B.chemicalPotential) ∧
      B.temperatureRegularizedHamiltonian 1 B.beta
        (B.massieuModel.dualCoord B.beta) = 0

/-- The finite prime grand-canonical Massieu owner target is proved. -/
theorem primeGrandCanonicalMassieuOwnerTarget :
    PrimeGrandCanonicalMassieuOwnerTarget := by
  intro B
  exact
    ⟨ B.beta_eq_realPart_of_bridge,
      B.partition_pos B.beta B.chemicalPotential,
      B.gibbsWeight_sum_one B.beta B.chemicalPotential,
      B.potential_deriv_beta_eq_neg_meanShift B.beta B.chemicalPotential,
      B.potential_deriv_mu_eq_beta_meanNumber B.beta B.chemicalPotential,
      B.temperatureRegularizedHamiltonian_eq_zero_at_contact 1 B.beta ⟩

end PrimeGrandCanonicalMassieuBridge

end InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge
