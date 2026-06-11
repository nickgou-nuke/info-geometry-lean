import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.ConcreteHilbertCommutation
import InfoGeometry.Canonical.CayleyBregmanBridge
import InfoGeometry.Canonical.SouriauBostConnesClosureProofs
import InfoGeometry.Canonical.PrimeCantorThermoYangBaxterBridge
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Canonical.DiracSea
import InfoGeometry.Quantum.FibonacciFusionCategory

/-!
# InfoGeometry.Canonical.SouriauBostConnesTransition

Verified finite/local matrix for the proposed Souriau--Bost--Connes transition
lane.

This module is deliberately not an analytic zero-temperature convergence
theorem.  It records the owner-backed pieces that already compile:

* finite Boolean prime Weyl denominator identity;
* finite reciprocal primon-product/evaluated-denominator identity;
* algebraic tensor-factor separation for base/fiber operators;
* Cayley critical-line/unit-circle readout through the prime Lee--Yang owner;
* conditional RH readout through the existing witness-gated owner;
* finite Yang--Baxter matrix readout;
* finite Fibonacci golden-ratio and phase readouts;
* combinatorial Dirac-sea interface nilpotence.

The analytic Bost--Connes partition function, zero-temperature limit,
Fibonacci categorical pentagon/hexagon coherence, and full boundary
crystallisation statement remain explicit closure debt below.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Canonical.SouriauBostConnesTransition

open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeCantorThermoYangBaxterBridge
open InfoGeometry.Canonical.PrimeLeeYangRHBridge
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Canonical.DiracSea
open FibonacciFusion

/-! ## Transition data carriers -/

/-- Finite prime-cutoff bulk state. -/
@[rep_depth thermo, capstone]
structure BulkState where
  /-- Finite prime cutoff. -/
  primes : Finset ℕ
  /-- Primality certificates for every prime in the cutoff. -/
  prime_mem : ∀ p ∈ primes, Nat.Prime p
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Non-degenerate temperature. -/
  beta_pos : 0 < beta

/-- Boundary state carrier used by the finite/local capstone matrix. -/
@[rep_depth thermo, capstone]
structure CrystallisedState where
  /-- Cantor boundary label as an infinite binary word. -/
  boundaryWord : ℕ → Fin 2
  /-- Fibonacci fusion label attached to the boundary site. -/
  label : FibObject
  /-- Combinatorial Dirac-sea vacuum profile. -/
  diracSeaVacuumState : DiracSeaBoundary := diracSeaVacuum

/-- Pack a finite bulk state together with a chosen finite/local boundary readout. -/
@[rep_depth thermo, capstone]
structure BCTransitionData where
  bulk : BulkState
  irReadout : CrystallisedState

/-- Formal root lattice associated to a finite bulk state. -/
@[rep_depth thermo, capstone]
def BulkState.rootLattice (bulk : BulkState) : FormalPrimeRootLattice where
  primes := bulk.primes
  prime_mem := bulk.prime_mem

/-- Thermal formal root variable used by the finite denominator readout. -/
@[rep_depth thermo, capstone]
def BulkState.thermalRootVariable (bulk : BulkState) (p : ℕ) : ℝ :=
  -bulk.beta * Real.log (p : ℝ)

/-- The canonical all-zero boundary readout with unit Fibonacci label. -/
@[rep_depth thermo, capstone]
def canonicalCrystallisedReadout : CrystallisedState where
  boundaryWord := fun _ : ℕ => 0
  label := FibObject.unit
  diracSeaVacuumState := diracSeaVacuum

/-- Construct the finite/local transition data packet from a finite bulk state. -/
@[rep_depth thermo, capstone]
def transitionDataOfBulk (bulk : BulkState) : BCTransitionData where
  bulk := bulk
  irReadout := canonicalCrystallisedReadout

/-! ## Owner-backed finite/local readouts -/

/-- Finite Boolean prime Weyl denominator identity for the bulk cutoff. -/
@[rep_depth thermo, capstone]
theorem finite_weylDenominator_eq_alternatingSum
    (bulk : BulkState) :
    weylDenominatorProduct bulk.rootLattice bulk.thermalRootVariable =
      weylAlternatingSum bulk.rootLattice bulk.thermalRootVariable :=
  finite_prime_weyl_denominator bulk.rootLattice bulk.thermalRootVariable

/--
The finite inverse Euler-product partition readout is the reciprocal of the
evaluated finite Weyl denominator.  This is still only the finite cutoff
statement, not the analytic Bost--Connes zeta partition theorem.
-/
@[rep_depth thermo, capstone]
theorem finite_primonPartition_eq_inverse_evaluatedWeylDenominator
    (bulk : BulkState) :
    finitePrimonPartition bulk.rootLattice bulk.beta =
      (evaluatedWeylDenominator bulk.rootLattice bulk.beta)⁻¹ :=
  finitePrimonPartition_eq_evaluatedWeylDenominator_inv bulk.rootLattice bulk.beta

/-- Same finite partition readout in conventional `p^{-β}` variables. -/
@[rep_depth thermo, capstone]
theorem finite_primonPartition_eq_rpowProduct
    (bulk : BulkState) :
    finitePrimonPartition bulk.rootLattice bulk.beta =
      ∏ p ∈ bulk.primes, (1 - (p : ℝ) ^ (-bulk.beta))⁻¹ :=
  finitePrimonPartition_eq_rpowProduct bulk.rootLattice bulk.beta

/-- Remaining analytic debt after the finite reciprocal product has been proved. -/
@[rep_depth thermo, capstone]
def inverseEulerProductIdentificationDebt : String :=
  "Finite reciprocal product proved; extend it to the analytic inverse Euler-product partition theorem."

/-- Remaining analytic Bost--Connes owner debt after the finite cutoff identity. -/
@[rep_depth thermo, capstone]
def analyticBostConnesPartitionDebt : String :=
  "Extend the finite reciprocal primon product to the analytic Bost-Connes partition theorem."

/-- Remaining Hilbert-space completion debt after algebraic tensor separation. -/
@[rep_depth thermo, capstone]
def hilbertCompletionTensorSeparationDebt : String :=
  "Lift the algebraic/PiLp Cuntz tensor separation to bounded operators on the Hilbert completion."

/--
Algebraic tensor-factor separation for the Cuntz-base/fiber split.

This closes the purely algebraic identity
`(S ⊗ id) (id ⊗ K) = (id ⊗ K) (S ⊗ id)`.  The bounded Hilbert-completion
version remains in `ConcreteHilbertCommutation` as explicit closure debt.
-/
@[rep_depth thermo, capstone]
theorem algebraic_tensor_factor_separation
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (S : V →ₗ[ℝ] V) (K : W →ₗ[ℝ] W) :
    (TensorProduct.map S (LinearMap.id : W →ₗ[ℝ] W)).comp
        (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) K) =
      (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) K).comp
        (TensorProduct.map S (LinearMap.id : W →ₗ[ℝ] W)) :=
  ConcreteHilbertCommutation.tensorFactorSeparation S K

/--
The real thermal-ray Cayley compactification reaches the boundary point `1` as
`β -> +∞`.  This is the scalar compactification coordinate only; it does not
identify the zero-temperature state accumulation set.
-/
@[rep_depth thermo, capstone]
theorem thermal_cayley_tendsto_boundary_one :
    Filter.Tendsto Cayley.thermalCayley Filter.atTop (𝓝 1) :=
  Cayley.thermalCayley_tendsto_atTop_one

/-- Remaining zero-temperature state-space debt after the real Cayley coordinate limit. -/
@[rep_depth thermo, capstone]
def zeroTemperatureCantorAccumulationDebt : String :=
  "Upgrade the finite zero-temperature boundary package to an analytic Cantor accumulation theorem."

/-- The concrete canonical V4-sewn Pauli boundary state has zero chiral index. -/
@[rep_depth thermo, capstone]
theorem concrete_canonical_sewn_boundary_anomaly_free :
    SouriauBostConnesClosureProofs.sewnChiralIndex
        SouriauBostConnesClosureProofs.canonicalSewnBoundaryState = 0 :=
  SouriauBostConnesClosureProofs.canonical_sewn_boundary_chiral_index_vanishes

/-- Remaining categorical boundary-functor debt after the finite label readout. -/
@[rep_depth thermo, capstone]
def cuntzFibonacciBoundaryFunctorDebt : String :=
  "Construct the Cuntz-to-Fibonacci boundary functor, not just a finite label readout."

/-- Remaining categorical owner debt for Fibonacci coherence. -/
@[rep_depth thermo, capstone]
def categoricalFibonacciCoherenceDebt : String :=
  "Prove categorical Fibonacci pentagon and hexagon coherence in the categorical owner file."

/-- Remaining full boundary anomaly debt after the concrete finite Pauli state. -/
@[rep_depth thermo, capstone]
def fullCantorBoundaryAnomalyLiftDebt : String :=
  "Lift the concrete finite V4-sewn Pauli boundary state to the full Cantor/Hilbert boundary state."

/-- Remaining quarantine debt for legacy anomaly surfaces. -/
@[rep_depth thermo, capstone]
def legacyKleinBottleQuarantineDebt : String :=
  "Retire or quarantine legacy axiom-based KleinBottleSewing surfaces in favor of concrete closure owners."

/-- Cayley compactification sends the critical line exactly to the unit circle. -/
@[rep_depth thermo, capstone]
theorem cayley_criticalLine_iff_unitCircle
    (s : ℂ) :
    OnCriticalLine s ↔ OnLeeYangCircle (cayleyToFugacity s) :=
  criticalLine_iff_cayleyCircle s

/-- Riemann reflection reads back as inversion in Cayley fugacity coordinates. -/
@[rep_depth thermo, capstone]
theorem cayley_reflection_eq_fugacity_inversion
    (s : ℂ) :
    cayleyToFugacity (1 - s) = (cayleyToFugacity s)⁻¹ :=
  riemannReflection_eq_fugacityInversion s

/-- The RH route remains conditional on the supplied prime Lee--Yang witnesses. -/
@[rep_depth thermo, capstone]
theorem conditional_RH_from_supplied_primeLeeYang
    (Ξ : CompletedXiZeroPredicate)
    (C : CayleyCriticalLineWitness)
    (A : LeeYangPrimeApproximation Ξ) :
    RiemannHypothesis Ξ :=
  conditional_RH_from_primeLeeYang Ξ C A

/-- A finite boundary readout exists for every finite bulk state. -/
@[rep_depth thermo, capstone]
theorem crystallised_readout_exists
    (_bulk : BulkState) :
    ∃ γ : CrystallisedState,
      γ.boundaryWord = (fun _ : ℕ => 0) ∧
        γ.label = FibObject.unit ∧
          γ.diracSeaVacuumState = diracSeaVacuum := by
  refine ⟨canonicalCrystallisedReadout, ?_, ?_, ?_⟩ <;> rfl

/--
Finite/local zero-temperature boundary package.

This packages the two finite owner facts already proved in this module:
the thermal Cayley coordinate reaches the boundary point `1`, and the
canonical Cantor/Fibonacci boundary readout exists for every finite bulk
state.

This is still not the analytic Cantor accumulation theorem.
-/
@[rep_depth thermo, capstone]
theorem finite_zeroTemperature_boundary_package
    (bulk : BulkState) :
    Filter.Tendsto Cayley.thermalCayley Filter.atTop (𝓝 1) ∧
      ∃ γ : CrystallisedState,
        γ.boundaryWord = (fun _ : ℕ => 0) ∧
          γ.label = FibObject.unit ∧
            γ.diracSeaVacuumState = diracSeaVacuum := by
  exact ⟨thermal_cayley_tendsto_boundary_one, crystallised_readout_exists bulk⟩

/-- Finite Yang--Baxter parameter identities from the exact matrix owner. -/
@[rep_depth thermo, capstone]
theorem yangBaxter_boundary_parameters :
    YangBaxterProof.q ^ 5 = -1 ∧
      YangBaxterProof.τ ^ 2 + YangBaxterProof.τ = 1 :=
  ⟨YangBaxterProof.q_pow_five, YangBaxterProof.tau_sq_add_tau⟩

/-- Finite Fibonacci golden-ratio identities from the finite matrix readout. -/
@[rep_depth thermo, capstone]
theorem fibonacci_golden_ratio_identities :
    0 < phi ∧ 1 < phi ∧ 0 < phiInv ∧
      phi ^ 2 = phi + 1 ∧ phiInv ^ 2 + phiInv = 1 :=
  ⟨phi_pos, phi_gt_one, phiInv_pos, phi_sq, phiInv_sq_add_phiInv⟩

/-- Finite Fibonacci braid phases are unitary and have the expected product. -/
@[rep_depth thermo, capstone]
theorem rmatrix_unitarity :
    ‖R1_phase‖ = 1 ∧
      ‖Rtau_phase‖ = 1 ∧
        R1_phase * Rtau_phase = Complex.exp (Complex.I * (2 * Real.pi / 5)) := by
  rcases R_phases_unitary with ⟨hR1, hRτ⟩
  exact ⟨hR1, hRτ, R_product⟩

/-- Combinatorial Dirac-sea vacuum and interface-step nilpotence. -/
@[rep_depth thermo, capstone]
theorem diracSea_half_filled :
    diracSeaVacuum = (fun n : ℤ => n < 0) ∧
      (∀ w : DiracSeaBoundary, Option.bind (diracSeaStep w) diracSeaStep = none) := by
  exact ⟨rfl, diracSeaStep_square_zero⟩

/-! ## Verified capstone matrix -/

/--
Verified finite/local matrix of the transition lane.

This is a record of the owner-backed facts that are actually proved.  Analytic
convergence and categorical coherence claims are intentionally excluded.
-/
@[rep_depth thermo, capstone]
structure VerifiedTransitionMatrix (bulk : BulkState) where
  denominator_identity :
    weylDenominatorProduct bulk.rootLattice bulk.thermalRootVariable =
      weylAlternatingSum bulk.rootLattice bulk.thermalRootVariable
  reciprocal_partition_identity :
    finitePrimonPartition bulk.rootLattice bulk.beta =
      (evaluatedWeylDenominator bulk.rootLattice bulk.beta)⁻¹
  thermal_cayley_boundary_limit :
    Filter.Tendsto Cayley.thermalCayley Filter.atTop (𝓝 1)
  canonical_sewn_boundary_anomaly_free :
    SouriauBostConnesClosureProofs.sewnChiralIndex
        SouriauBostConnesClosureProofs.canonicalSewnBoundaryState = 0
  yang_baxter_parameters :
    YangBaxterProof.q ^ 5 = -1 ∧
      YangBaxterProof.τ ^ 2 + YangBaxterProof.τ = 1
  fibonacci_identities :
    0 < phi ∧ 1 < phi ∧ 0 < phiInv ∧
      phi ^ 2 = phi + 1 ∧ phiInv ^ 2 + phiInv = 1
  rmatrix_phases :
    ‖R1_phase‖ = 1 ∧
      ‖Rtau_phase‖ = 1 ∧
        R1_phase * Rtau_phase = Complex.exp (Complex.I * (2 * Real.pi / 5))
  dirac_sea_readout :
    diracSeaVacuum = (fun n : ℤ => n < 0) ∧
      (∀ w : DiracSeaBoundary, Option.bind (diracSeaStep w) diracSeaStep = none)

/-- Construct the verified finite/local matrix from the existing owner theorems. -/
@[rep_depth thermo, capstone]
def verifiedTransitionMatrix (bulk : BulkState) : VerifiedTransitionMatrix bulk where
  denominator_identity := finite_weylDenominator_eq_alternatingSum bulk
  reciprocal_partition_identity :=
    finite_primonPartition_eq_inverse_evaluatedWeylDenominator bulk
  thermal_cayley_boundary_limit := thermal_cayley_tendsto_boundary_one
  canonical_sewn_boundary_anomaly_free := concrete_canonical_sewn_boundary_anomaly_free
  yang_baxter_parameters := yangBaxter_boundary_parameters
  fibonacci_identities := fibonacci_golden_ratio_identities
  rmatrix_phases := rmatrix_unitarity
  dirac_sea_readout := diracSea_half_filled

/-- Public package constructor for the finite/local transition readout. -/
@[rep_depth thermo, capstone]
def souriau_bost_connes_transition_Package
    (P : Finset ℕ) (primesP : ∀ p ∈ P, Nat.Prime p) (β : ℝ) (hβpos : 0 < β) :
    BCTransitionData :=
  transitionDataOfBulk
    { primes := P
      prime_mem := primesP
      beta := β
      beta_pos := hβpos }

/-- The public package preserves the supplied finite cutoff and temperature. -/
@[rep_depth thermo, capstone]
theorem souriau_bost_connes_transition_Package_bulk
    (P : Finset ℕ) (primesP : ∀ p ∈ P, Nat.Prime p) (β : ℝ) (hβpos : 0 < β) :
    (souriau_bost_connes_transition_Package P primesP β hβpos).bulk.primes = P ∧
      (souriau_bost_connes_transition_Package P primesP β hβpos).bulk.beta = β :=
  ⟨rfl, rfl⟩

/--
The public package has a verified finite/local transition matrix.

This is the theorem-safe capstone exported by this file.
-/
@[rep_depth thermo, capstone]
theorem souriau_bost_connes_transition_verified
    (P : Finset ℕ) (primesP : ∀ p ∈ P, Nat.Prime p) (β : ℝ) (hβpos : 0 < β) :
    Nonempty
      (VerifiedTransitionMatrix
        (souriau_bost_connes_transition_Package P primesP β hβpos).bulk) :=
  ⟨verifiedTransitionMatrix _⟩

/-! ## Explicit closure debt -/

/-- Open closure debt for the analytic/categorical transition theorem. -/
@[rep_depth thermo, capstone]
def openClosureDebt : List String :=
  [ "Construct the analytic Bost-Connes partition function in the repository owner lane."
  , inverseEulerProductIdentificationDebt
  , analyticBostConnesPartitionDebt
  , hilbertCompletionTensorSeparationDebt
  , zeroTemperatureCantorAccumulationDebt
  , cuntzFibonacciBoundaryFunctorDebt
  , categoricalFibonacciCoherenceDebt
  , fullCantorBoundaryAnomalyLiftDebt
  , legacyKleinBottleQuarantineDebt
  ]

/-- The capstone still has explicit open debt; it is not an analytic closure theorem. -/
@[rep_depth thermo, capstone]
theorem openClosureDebt_ne_nil :
    openClosureDebt ≠ [] := by
  decide

end InfoGeometry.Canonical.SouriauBostConnesTransition
