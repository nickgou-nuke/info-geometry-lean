import Mathlib
import InfoGeometry.GrandCanonical.ResponseMatrix
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

Finite grand-canonical ensemble on the prime-occupation state space.

This module specializes the existing finite grand-canonical core to a finite
prime cutoff:

* states are square-free prime subsets, represented as elements of
  `P.primes.powerset`;
* energy is a prime-weight sum over occupied primes;
* number is the occupied-mode cardinality;
* partition, Gibbs weights, potential, and response theorems come from the
  generic grand-canonical model.

The file remains finite and theorem-safe.  It does not claim any infinite
limit, thermodynamic completion, or RH statement.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-! ## 1. Finite prime grand-canonical carrier -/

/--
Finite prime-occupation states.

The carrier is the powerset subtype, so Lean sees it as a finite type directly.
-/
@[rep_depth thermo]
abbrev PrimeState (P : PrimeRegister) :=
  {S : Finset ℕ // S ∈ P.primes.powerset}

instance (P : PrimeRegister) : Fintype (PrimeState P) := by
  infer_instance

instance (P : PrimeRegister) : Nonempty (PrimeState P) := by
  refine ⟨⟨∅, ?_⟩⟩
  simp

/-- The occupied prime set of a state. -/
@[rep_depth thermo]
def occupied {P : PrimeRegister} (S : PrimeState P) : Finset ℕ :=
  S.1

/-- Prime-weighted energy observable on a state. -/
@[rep_depth thermo]
def stateEnergy {P : PrimeRegister}
    (lam : ℕ → ℝ) (S : PrimeState P) : ℝ :=
  Finset.sum S.1 (fun p => lam p)

/-- Occupation-number observable on a state. -/
@[rep_depth thermo]
def stateNumber {P : PrimeRegister} (S : PrimeState P) : ℝ :=
  S.1.card

/-! ## 2. Bundled finite grand-canonical packet -/

/--
Finite grand-canonical packet on a prime register.

`energyWeight` is the prime-axis energy coefficient, typically `log p`.
-/
@[rep_depth thermo]
structure PrimeGrandCanonicalPacket where
  P : PrimeRegister
  energyWeight : ℕ → ℝ

namespace PrimeGrandCanonicalPacket

/-- The state carrier for the packet. -/
@[rep_depth thermo]
abbrev State (B : PrimeGrandCanonicalPacket) := PrimeState B.P

/-- The grand-canonical two-parameter data associated to the packet. -/
@[rep_depth thermo]
def params (B : PrimeGrandCanonicalPacket) :
    InfoGeometry.GrandCanonical.GrandCanonicalTwoParam (State B) where
  energy := stateEnergy B.energyWeight
  number := stateNumber

/-- Canonical `β`-partition function. -/
@[rep_depth thermo]
def partition (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.partitionGC (B.params) β μ

/-- Log-partition potential. -/
@[rep_depth thermo]
def potential (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.potentialGC (B.params) β μ

/-- Gibbs weight of a state. -/
@[rep_depth thermo]
def gibbsWeight (B : PrimeGrandCanonicalPacket) (β μ : ℝ) (S : State B) : ℝ :=
  InfoGeometry.GrandCanonical.gibbsWeightGC (B.params) β μ S

/-- Mean shifted observable `E - μN`. -/
@[rep_depth thermo]
def meanShift (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanShift (B.params) β μ

/-- Mean particle number. -/
@[rep_depth thermo]
def meanNumber (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanNumber (B.params) β μ

/-- First β-response of the potential. -/
@[rep_depth thermo]
def betaResponse (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaResponse (B.params) β μ

/-- First μ-response of the potential. -/
@[rep_depth thermo]
def muResponse (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muResponse (B.params) β μ

/-- Second β-derivative of the potential. -/
@[rep_depth thermo]
def betaHessian (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaHessian (B.params) β μ

/-- Second μ-derivative of the potential. -/
@[rep_depth thermo]
def muHessian (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muHessian (B.params) β μ

/-- Mixed derivative `∂_μ ∂_β`. -/
@[rep_depth thermo]
def betaMuHessian (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaMuHessian (B.params) β μ

/-- Mixed derivative `∂_β ∂_μ`. -/
@[rep_depth thermo]
def muBetaHessian (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muBetaHessian (B.params) β μ

/-- Thermodynamic response matrix. -/
@[rep_depth thermo]
def responseMatrix (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.ResponseMatrix2 :=
  InfoGeometry.GrandCanonical.responseMatrix (B.params) β μ

/-- Spinodal condition in the grand-canonical packet. -/
@[rep_depth thermo]
def spinodal2D (B : PrimeGrandCanonicalPacket) (β μ : ℝ) : Prop :=
  InfoGeometry.GrandCanonical.Spinodal2D (B.params) β μ

@[simp, rep_depth thermo]
theorem params_energy (B : PrimeGrandCanonicalPacket) (S : State B) :
    (B.params).energy S = stateEnergy B.energyWeight S := by
  rfl

@[simp, rep_depth thermo]
theorem params_number (B : PrimeGrandCanonicalPacket) (S : State B) :
    (B.params).number S = stateNumber S := by
  rfl

@[simp, rep_depth thermo]
theorem partition_eq (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.partition β μ = InfoGeometry.GrandCanonical.partitionGC B.params β μ := by
  rfl

@[simp, rep_depth thermo]
theorem potential_eq (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.potential β μ = InfoGeometry.GrandCanonical.potentialGC B.params β μ := by
  rfl

@[simp, rep_depth thermo]
theorem gibbsWeight_eq (B : PrimeGrandCanonicalPacket) (β μ : ℝ) (S : State B) :
    B.gibbsWeight β μ S = InfoGeometry.GrandCanonical.gibbsWeightGC B.params β μ S := by
  rfl

/-! ## 3. Prime-specialized theorem wrappers -/

theorem partition_pos (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    0 < B.partition β μ := by
  simpa [PrimeGrandCanonicalPacket.partition] using
    InfoGeometry.GrandCanonical.partitionGC_pos B.params β μ

theorem gibbsWeight_sum_one (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    ∑ S, B.gibbsWeight β μ S = 1 := by
  simpa [PrimeGrandCanonicalPacket.gibbsWeight] using
    InfoGeometry.GrandCanonical.gibbsWeightGC_sum_one B.params β μ

theorem potential_deriv_beta_eq_neg_meanShift (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    deriv (fun t => B.potential t μ) β = -B.meanShift β μ := by
  simpa [PrimeGrandCanonicalPacket.potential, PrimeGrandCanonicalPacket.meanShift] using
    InfoGeometry.GrandCanonical.potentialGC_deriv_beta_eq_neg_meanShift B.params β μ

theorem potential_deriv_mu_eq_beta_meanNumber (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    deriv (fun t => B.potential β t) μ = β * B.meanNumber β μ := by
  simpa [PrimeGrandCanonicalPacket.potential, PrimeGrandCanonicalPacket.meanNumber] using
    InfoGeometry.GrandCanonical.potentialGC_deriv_mu_eq_beta_meanNumber B.params β μ

theorem betaResponse_eq_neg_meanShift (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.betaResponse β μ = -B.meanShift β μ := by
  simpa [PrimeGrandCanonicalPacket.betaResponse, PrimeGrandCanonicalPacket.meanShift] using
    InfoGeometry.GrandCanonical.betaResponse_eq_neg_meanShift B.params β μ

theorem muResponse_eq_beta_meanNumber (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.muResponse β μ = β * B.meanNumber β μ := by
  simpa [PrimeGrandCanonicalPacket.muResponse, PrimeGrandCanonicalPacket.meanNumber] using
    InfoGeometry.GrandCanonical.muResponse_eq_beta_meanNumber B.params β μ

theorem betaHessian_eq_varianceShift (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.betaHessian β μ =
      InfoGeometry.GrandCanonical.varianceShift B.params β μ := by
  simpa [PrimeGrandCanonicalPacket.betaHessian] using
    InfoGeometry.GrandCanonical.potentialGC_hessian_beta_beta B.params β μ

theorem muHessian_eq_beta_sq_varianceNumber (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.muHessian β μ =
      (β ^ (2 : ℕ)) * InfoGeometry.GrandCanonical.varianceNumber B.params β μ := by
  simpa [PrimeGrandCanonicalPacket.muHessian] using
    InfoGeometry.GrandCanonical.potentialGC_hessian_mu_mu B.params β μ

theorem betaMuHessian_eq_meanNumber_sub_beta_mul_covariance
    (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.betaMuHessian β μ =
      InfoGeometry.GrandCanonical.meanNumber B.params β μ
        - β * InfoGeometry.GrandCanonical.covarianceShiftNumber B.params β μ := by
  simpa [PrimeGrandCanonicalPacket.betaMuHessian] using
    InfoGeometry.GrandCanonical.potentialGC_hessian_beta_mu B.params β μ

theorem muBetaHessian_eq_meanNumber_sub_beta_mul_covariance
    (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.muBetaHessian β μ =
      InfoGeometry.GrandCanonical.meanNumber B.params β μ
        - β * InfoGeometry.GrandCanonical.covarianceShiftNumber B.params β μ := by
  simpa [PrimeGrandCanonicalPacket.muBetaHessian] using
    InfoGeometry.GrandCanonical.potentialGC_hessian_mu_beta B.params β μ

theorem betaMuHessian_eq_muBetaHessian (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.betaMuHessian β μ = B.muBetaHessian β μ := by
  rw [betaMuHessian_eq_meanNumber_sub_beta_mul_covariance,
    muBetaHessian_eq_meanNumber_sub_beta_mul_covariance]

theorem responseMatrix_symmetric (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.ResponseMatrix2.Symmetric (B.responseMatrix β μ) := by
  simpa [PrimeGrandCanonicalPacket.responseMatrix] using
    InfoGeometry.GrandCanonical.responseMatrix_symmetric B.params β μ
      (betaMuHessian_eq_muBetaHessian B β μ)

theorem responseMatrix_positiveSemidefinite (B : PrimeGrandCanonicalPacket) (β μ : ℝ)
    (hββ : 0 ≤ B.betaHessian β μ)
    (hμμ : 0 ≤ B.muHessian β μ)
    (hdet : 0 ≤ (B.responseMatrix β μ).det) :
    InfoGeometry.GrandCanonical.ResponseMatrix2.PositiveSemidefinite
      (B.responseMatrix β μ) := by
  simpa [PrimeGrandCanonicalPacket.responseMatrix] using
    InfoGeometry.GrandCanonical.responseMatrix_positiveSemidefinite B.params β μ hββ hμμ hdet

theorem spinodal2D_iff_det_eq_zero (B : PrimeGrandCanonicalPacket) (β μ : ℝ) :
    B.spinodal2D β μ ↔ (B.responseMatrix β μ).det = 0 := by
  simpa [PrimeGrandCanonicalPacket.spinodal2D, PrimeGrandCanonicalPacket.responseMatrix] using
    InfoGeometry.GrandCanonical.spinodal2D_iff_det_eq_zero B.params β μ

/-! ## 4. Log-energy specialization -/

/-- The logarithmic prime-energy specialization `lam p = log p`. -/
@[rep_depth thermo]
def logPrimeEnergyWeight : ℕ → ℝ :=
  fun p => Real.log p

/-- The log-energy prime grand-canonical packet. -/
@[rep_depth thermo]
def logPrimePacket (P : PrimeRegister) : PrimeGrandCanonicalPacket where
  P := P
  energyWeight := logPrimeEnergyWeight

end PrimeGrandCanonicalPacket

end InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
