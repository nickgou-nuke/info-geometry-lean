import Mathlib.Tactic
import InfoGeometry.Core.GrandCanonical
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Topology.CantorDiracOperator

/-!
# InfoGeometry.Topology.CantorDiracGrandCanonical

Finite grand-canonical ensemble attached to the Cantor Dirac thermal scale.

This file keeps the Gibbs Hamiltonian on the even thermal side of the Cantor
Dirac story.  The odd Dirac operator is not used as the Gibbs Hamiltonian.
Instead, the finite binary-cylinder occupancy model is equipped with an even
thermal energy readout derived from the Cantor Dirac scale.

Theorems here are the finite grand-canonical wrappers:

* partition positivity;
* Gibbs normalization;
* `β` and `μ` derivative readbacks for the log-partition potential;
* Hessian / response readbacks;
* mixed-response symmetry.

No infinite limit, no analytic continuation, and no RH claim is made.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Topology.CantorDiracGrandCanonical

open InfoGeometry.Topology.CantorDiracOperator

/-! ## 1. Finite Cantor occupancy carrier -/

/-- Binary words at a finite Cantor level. -/
abbrev CantorState (n : ℕ) := BinaryWord n

instance (n : ℕ) : Fintype (CantorState n) := by
  dsimp [CantorState]
  infer_instance

instance (n : ℕ) : Nonempty (CantorState n) := by
  dsimp [CantorState]
  infer_instance

/-- Occupation number of a finite Cantor binary word. -/
@[rep_depth thermo]
def occupancy {n : ℕ} (w : CantorState n) : ℝ :=
  ∑ i : Fin n, if w i then 1 else 0

@[simp, rep_depth thermo]
theorem occupancy_zero {n : ℕ} (w : CantorState n) :
    occupancy w = ∑ i : Fin n, if w i then 1 else 0 := by
  rfl

/-! ## 2. Finite Cantor grand-canonical packet -/

/--
Finite grand-canonical packet on the Cantor cylinder carrier.

`scale` is the even thermal Hamiltonian scale induced by the Cantor Dirac
block at the chosen cutoff.  The energy observable is the scaled occupancy.
-/
@[rep_depth thermo]
structure CantorGrandCanonicalPacket where
  cutoff : ℕ
  scale : CantorDiracScale

namespace CantorGrandCanonicalPacket

/-- Finite Cantor state carrier for the packet. -/
@[rep_depth thermo]
abbrev State (B : CantorGrandCanonicalPacket) := CantorState B.cutoff

/-- The two-parameter grand-canonical data associated to the Cantor packet. -/
@[rep_depth thermo]
def params (B : CantorGrandCanonicalPacket) :
    InfoGeometry.GrandCanonical.GrandCanonicalTwoParam (State B) where
  energy := fun w => B.scale B.cutoff * occupancy w
  number := occupancy

/-- Canonical `β, μ` partition function. -/
@[rep_depth thermo]
def partition (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.partitionGC (params B) β μ

/-- Log-partition potential. -/
@[rep_depth thermo]
def potential (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.potentialGC (params B) β μ

/-- Gibbs weight of a Cantor state. -/
@[rep_depth thermo]
def gibbsWeight (B : CantorGrandCanonicalPacket) (β μ : ℝ) (w : State B) : ℝ :=
  InfoGeometry.GrandCanonical.gibbsWeightGC (params B) β μ w

/-- Mean shifted observable `E - μN`. -/
@[rep_depth thermo]
def meanShift (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanShift (params B) β μ

/-- Mean particle number. -/
@[rep_depth thermo]
def meanNumber (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanNumber (params B) β μ

/-- First `β`-response of the potential. -/
@[rep_depth thermo]
def betaResponse (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaResponse (params B) β μ

/-- First `μ`-response of the potential. -/
@[rep_depth thermo]
def muResponse (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muResponse (params B) β μ

/-- Second `β`-derivative of the potential. -/
@[rep_depth thermo]
def betaHessian (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaHessian (params B) β μ

/-- Second `μ`-derivative of the potential. -/
@[rep_depth thermo]
def muHessian (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muHessian (params B) β μ

/-- Mixed derivative `∂_μ ∂_β`. -/
@[rep_depth thermo]
def betaMuHessian (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaMuHessian (params B) β μ

/-- Mixed derivative `∂_β ∂_μ`. -/
@[rep_depth thermo]
def muBetaHessian (B : CantorGrandCanonicalPacket) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muBetaHessian (params B) β μ

/-- Thermodynamic response matrix. -/
@[rep_depth thermo]
def responseMatrix (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.ResponseMatrix2 :=
  InfoGeometry.GrandCanonical.responseMatrix (params B) β μ

/-- Spinodal condition in the Cantor grand-canonical packet. -/
@[rep_depth thermo]
def spinodal2D (B : CantorGrandCanonicalPacket) (β μ : ℝ) : Prop :=
  InfoGeometry.GrandCanonical.Spinodal2D (params B) β μ

@[simp, rep_depth thermo]
theorem params_energy (B : CantorGrandCanonicalPacket) (w : State B) :
    (params B).energy w = B.scale B.cutoff * occupancy w := by
  rfl

@[simp, rep_depth thermo]
theorem params_number (B : CantorGrandCanonicalPacket) (w : State B) :
    (params B).number w = occupancy w := by
  rfl

@[simp, rep_depth thermo]
theorem partition_eq (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    partition B β μ = InfoGeometry.GrandCanonical.partitionGC (params B) β μ := by
  rfl

@[simp, rep_depth thermo]
theorem potential_eq (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    potential B β μ = InfoGeometry.GrandCanonical.potentialGC (params B) β μ := by
  rfl

@[simp, rep_depth thermo]
theorem gibbsWeight_eq (B : CantorGrandCanonicalPacket) (β μ : ℝ) (w : State B) :
    gibbsWeight B β μ w = InfoGeometry.GrandCanonical.gibbsWeightGC (params B) β μ w := by
  rfl

/-! ## 3. Grand-canonical theorem wrappers -/

theorem partition_pos (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    0 < partition B β μ := by
  simpa [CantorGrandCanonicalPacket.partition] using
    InfoGeometry.GrandCanonical.partitionGC_pos (params B) β μ

theorem gibbsWeight_sum_one (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    ∑ w, gibbsWeight B β μ w = 1 := by
  simpa [CantorGrandCanonicalPacket.gibbsWeight] using
    InfoGeometry.GrandCanonical.gibbsWeightGC_sum_one (params B) β μ

theorem gibbsWeight_nonneg (B : CantorGrandCanonicalPacket) (β μ : ℝ) (w : State B) :
    0 ≤ gibbsWeight B β μ w := by
  simpa [CantorGrandCanonicalPacket.gibbsWeight] using
    InfoGeometry.GrandCanonical.gibbsWeightGC_nonneg (params B) β μ w

theorem gibbsWeight_le_one (B : CantorGrandCanonicalPacket) (β μ : ℝ) (w : State B) :
    gibbsWeight B β μ w ≤ 1 := by
  simpa [CantorGrandCanonicalPacket.gibbsWeight] using
    InfoGeometry.GrandCanonical.gibbsWeightGC_le_one (params B) β μ w

theorem potential_deriv_beta_eq_neg_meanShift (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    deriv (fun t => potential B t μ) β = -meanShift B β μ := by
  simpa [CantorGrandCanonicalPacket.potential, CantorGrandCanonicalPacket.meanShift] using
    InfoGeometry.GrandCanonical.potentialGC_deriv_beta_eq_neg_meanShift (params B) β μ

theorem potential_deriv_mu_eq_beta_meanNumber (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    deriv (fun t => potential B β t) μ = β * meanNumber B β μ := by
  simpa [CantorGrandCanonicalPacket.potential, CantorGrandCanonicalPacket.meanNumber] using
    InfoGeometry.GrandCanonical.potentialGC_deriv_mu_eq_beta_meanNumber (params B) β μ

theorem betaResponse_eq_neg_meanShift (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    betaResponse B β μ = -meanShift B β μ := by
  simpa [CantorGrandCanonicalPacket.betaResponse, CantorGrandCanonicalPacket.meanShift] using
    InfoGeometry.GrandCanonical.betaResponse_eq_neg_meanShift (params B) β μ

theorem muResponse_eq_beta_meanNumber (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    muResponse B β μ = β * meanNumber B β μ := by
  simpa [CantorGrandCanonicalPacket.muResponse, CantorGrandCanonicalPacket.meanNumber] using
    InfoGeometry.GrandCanonical.muResponse_eq_beta_meanNumber (params B) β μ

theorem betaHessian_eq_varianceShift (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    betaHessian B β μ = InfoGeometry.GrandCanonical.varianceShift (params B) β μ := by
  simpa [CantorGrandCanonicalPacket.betaHessian] using
    InfoGeometry.GrandCanonical.potentialGC_hessian_beta_beta (params B) β μ

theorem muHessian_eq_beta_sq_varianceNumber (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    muHessian B β μ =
      (β ^ (2 : ℕ)) * InfoGeometry.GrandCanonical.varianceNumber (params B) β μ := by
  simpa [CantorGrandCanonicalPacket.muHessian] using
    InfoGeometry.GrandCanonical.potentialGC_hessian_mu_mu (params B) β μ

theorem betaMuHessian_eq_meanNumber_sub_beta_mul_covariance
    (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    betaMuHessian B β μ =
      InfoGeometry.GrandCanonical.meanNumber (params B) β μ
        - β * InfoGeometry.GrandCanonical.covarianceShiftNumber (params B) β μ := by
  simpa [CantorGrandCanonicalPacket.betaMuHessian] using
    InfoGeometry.GrandCanonical.potentialGC_hessian_beta_mu (params B) β μ

theorem muBetaHessian_eq_meanNumber_sub_beta_mul_covariance
    (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    muBetaHessian B β μ =
      InfoGeometry.GrandCanonical.meanNumber (params B) β μ
        - β * InfoGeometry.GrandCanonical.covarianceShiftNumber (params B) β μ := by
  simpa [CantorGrandCanonicalPacket.muBetaHessian] using
    InfoGeometry.GrandCanonical.potentialGC_hessian_mu_beta (params B) β μ

theorem betaMuHessian_eq_muBetaHessian (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    betaMuHessian B β μ = muBetaHessian B β μ := by
  rw [betaMuHessian_eq_meanNumber_sub_beta_mul_covariance,
    muBetaHessian_eq_meanNumber_sub_beta_mul_covariance]

theorem responseMatrix_symmetric (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.ResponseMatrix2.Symmetric (responseMatrix B β μ) := by
  simpa [CantorGrandCanonicalPacket.responseMatrix] using
    InfoGeometry.GrandCanonical.responseMatrix_symmetric_of_hessian (params B) β μ

theorem responseMatrix_positiveSemidefinite (B : CantorGrandCanonicalPacket) (β μ : ℝ)
    (hββ : 0 ≤ betaHessian B β μ)
    (hμμ : 0 ≤ muHessian B β μ)
    (hdet : 0 ≤ (responseMatrix B β μ).det) :
    InfoGeometry.GrandCanonical.ResponseMatrix2.PositiveSemidefinite (responseMatrix B β μ) := by
  simpa [CantorGrandCanonicalPacket.responseMatrix] using
    InfoGeometry.GrandCanonical.responseMatrix_positiveSemidefinite (params B) β μ hββ hμμ hdet

theorem spinodal2D_iff_det_eq_zero (B : CantorGrandCanonicalPacket) (β μ : ℝ) :
    spinodal2D B β μ ↔ (responseMatrix B β μ).det = 0 := by
  simpa [CantorGrandCanonicalPacket.spinodal2D, CantorGrandCanonicalPacket.responseMatrix] using
    InfoGeometry.GrandCanonical.spinodal2D_iff_det_eq_zero (params B) β μ

end CantorGrandCanonicalPacket

end InfoGeometry.Topology.CantorDiracGrandCanonical
