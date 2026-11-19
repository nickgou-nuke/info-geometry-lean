/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConcreteHilbertCommutation
import InfoGeometry.Canonical.CayleyBregmanBridge
import InfoGeometry.Canonical.SouriauBostConnesClosureProofs
import InfoGeometry.Canonical.PrimeCantorThermoYangBaxterBridge
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Canonical.DiracSea
import InfoGeometry.Quantum.FibonacciFusionCategory
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.BostConnes.BostConnesThermofield
import InfoGeometry.Canonical.ConcreteHilbertCuntzO2
import InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
import InfoGeometry.Categorical.FibonacciMonoidalBraidedInstance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Meta

/-!
# InfoGeometry.Canonical.SouriauBostConnesTransition

Owner-backed Souriau--Bost--Connes transition bridge and closure debts (`D1`–`D7`).

This module combines finite/local matrix readouts with completed analytic,
infinite-dimensional Hilbert-space, and monoidal-categorical theorem owners:

* finite Boolean prime Weyl denominator, reciprocal primon-product, Yang--Baxter,
  Fibonacci, and Dirac-sea readouts, plus conditional RH readout via Prime Lee--Yang;
* Cayley critical-line / thermal boundary compactification (`thermalCayleyBoundaryArchetype`);
* analytic zeta non-vanishing on `Re(s) > 1`, Euler product, zero-temperature Cantor
  crystallization (`d1`–`d3`), and Souriau Fisher metric blow-up / excited-tail collapse (`d4`);
* completed `H_lp` Hilbert Cuntz `O₂` isometries, non-commutativity, and phase-axis
  commutation (`d5`, `completedHilbertCuntzClockCommutationArchetype`);
* explicit semisimple braided monoidal Fibonacci category (`d6`);
* infinite-dimensional `H_lp` modular swap / fundamental symmetry `Cl(1,1)` algebra,
  non-commuting Cuntz `O₂` sewing invariance, non-zero sewn Cantor vacuum state, and
  boundary chiral anomaly cancellation (`d7InfiniteHilbertSewnAnomalyCancellationArchetype`).

Remaining open frontier outside this surface: unconditional RH (RH remains strictly
conditional on supplied Lee--Yang hypotheses) and full $C^*$-algebraic Bost--Connes
$\mathrm{KMS}_\beta \simeq \widehat{\mathbb{Z}}^\times$ idele-class state-simplex classification;
infinite-dimensional anomaly cancellation applies to `J_lp`-fixed vectors and `J_lp`-paired
summable operator families (not arbitrary trace-class operator ideals without pairing).
-/

noncomputable section

open scoped Topology
open scoped ArithmeticFunction.Moebius
open scoped LSeries.notation

namespace InfoGeometry.Canonical.SouriauBostConnesTransition

open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeCantorThermoYangBaxterBridge
open InfoGeometry.Canonical.PrimeLeeYangRHBridge
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Canonical.DiracSea
open FibonacciFusion
open InfoGeometry.Meta
open InfoGeometry.MetaCompiler

/-! ## Transition data carriers -/

/-- Finite prime-cutoff bulk state. -/
@[rep_depth thermo]
structure BulkState where
  /-- Finite prime cutoff. -/
  primes : Finset ℕ
  /-- Primality proof for every prime in the cutoff. -/
  prime_mem : ∀ p ∈ primes, Nat.Prime p
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Non-degenerate temperature. -/
  beta_pos : 0 < beta

/-- Boundary state carrier used by the finite/local capstone matrix. -/
@[rep_depth thermo]
structure CrystallisedState where
  /-- Cantor boundary label as an infinite binary word. -/
  boundaryWord : ℕ → Fin 2
  /-- Fibonacci fusion label attached to the boundary site. -/
  label : FibObject

namespace CrystallisedState

/-- The finite/local boundary carrier uses the canonical Dirac-sea vacuum. -/
def diracSeaVacuumState (_γ : CrystallisedState) : DiracSeaBoundary :=
  diracSeaVacuum

@[simp] theorem diracSeaVacuumState_eq (γ : CrystallisedState) :
    γ.diracSeaVacuumState = diracSeaVacuum := rfl

end CrystallisedState

/-- Pack a finite bulk state together with a chosen finite/local boundary readout. -/
@[rep_depth thermo]
structure BCTransitionData where
  bulk : BulkState
  irReadout : CrystallisedState

instance : Inhabited BulkState where
  default := {
    primes := ∅
    prime_mem := fun _ hp => by simp at hp
    beta := 1
    beta_pos := by norm_num
  }

instance : Inhabited CrystallisedState where
  default := {
    boundaryWord := fun _ => 0
    label := FibObject.unit
  }

instance : Inhabited BCTransitionData where
  default := {
    bulk := default
    irReadout := default
  }

/-- Formal root lattice associated to a finite bulk state. -/
@[rep_depth thermo]
def BulkState.rootLattice (bulk : BulkState) : FormalPrimeRootLattice where
  primes := bulk.primes
  prime_mem := bulk.prime_mem

/-- Thermal formal root variable used by the finite denominator readout. -/
@[rep_depth thermo]
def BulkState.thermalRootVariable (bulk : BulkState) (p : ℕ) : ℝ :=
  -bulk.beta * Real.log (p : ℝ)

/-- The canonical all-zero boundary readout with unit Fibonacci label. -/
@[rep_depth thermo]
def canonicalCrystallisedReadout : CrystallisedState where
  boundaryWord := fun _ : ℕ => 0
  label := FibObject.unit

/-- Construct the finite/local transition data packet from a finite bulk state. -/
@[rep_depth thermo]
def transitionDataOfBulk (bulk : BulkState) : BCTransitionData where
  bulk := bulk
  irReadout := canonicalCrystallisedReadout

/-! ## Bost--Connes Dirichlet Series and Thermofield Intertwining -/

/-- Real-valued Bost--Connes Dirichlet series / partition function $Z(β) = \sum_{n=1}^\infty n^{-β}$
for inverse temperature $β > 1$. -/
@[rep_depth thermo]
noncomputable def dirichletSeriesBC (β : ℝ) (_hβ : 1 < β) : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-β)

/-- The Dirichlet series $Z(β)$ converges and has sum `dirichletSeriesBC β hβ`. -/
@[rep_depth thermo, capstone]
theorem dirichletSeriesBC_hasSum (β : ℝ) (hβ : 1 < β) :
    HasSum (fun n : ℕ => (n : ℝ) ^ (-β)) (dirichletSeriesBC β hβ) := by
  have h_exp : -β < -1 := by linarith
  exact (Real.summable_nat_rpow.mpr h_exp).hasSum

/-- Completely multiplicative homomorphism on ℕ for real power n ↦ n^(-β). -/
@[rep_depth thermo]
noncomputable def dirichletSummandRealHom {β : ℝ} (hβ : β ≠ 0) : ℕ →*₀ ℝ where
  toFun n := (n : ℝ) ^ (-β)
  map_zero' := by
    have hneg : -β ≠ 0 := neg_ne_zero.mpr hβ
    simp only [Nat.cast_zero]
    exact Real.zero_rpow hneg
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- The Dirichlet summand is completely multiplicative. -/
@[rep_depth thermo, capstone]
theorem dirichletSeriesBC_sum_multiplicative (β : ℝ) (hβ : β ≠ 0) (m n : ℕ) :
    dirichletSummandRealHom hβ (m * n) =
      dirichletSummandRealHom hβ m * dirichletSummandRealHom hβ n :=
  (dirichletSummandRealHom hβ).map_mul m n

open Nat EulerProduct

/-- Euler product partial product convergence to the Bost--Connes partition function. -/
@[rep_depth thermo, capstone]
theorem dirichletSeriesBC_euler_product (β : ℝ) (hβ : 1 < β) :
    Filter.Tendsto (fun n : ℕ => ∏ p ∈ primesBelow n, (1 - (p : ℝ) ^ (-β))⁻¹)
      Filter.atTop (𝓝 (dirichletSeriesBC β hβ)) := by
  have hβ_ne : β ≠ 0 := by linarith
  have h_summable : Summable (fun n : ℕ => ‖dirichletSummandRealHom hβ_ne n‖) := by
    have h_exp : -β < -1 := by linarith
    have h_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-β)) := Real.summable_nat_rpow.mpr h_exp
    refine h_rpow.congr (fun n => ?_)
    dsimp [dirichletSummandRealHom]
    exact (Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)).symm
  exact eulerProduct_completely_multiplicative h_summable

/-- Unconditional Euler product convergence over the directed net of finite subsets of $\mathbb{N}$:
$\lim_{P \to \infty} \prod_{p \in P,\, p\text{ prime}} (1 - p^{-\beta})^{-1} = Z(\beta)$ for $\beta > 1$. -/
@[rep_depth thermo, capstone]
theorem dirichletSeriesBC_finset_euler_product (β : ℝ) (hβ : 1 < β) :
    Filter.Tendsto
      (fun (P : Finset ℕ) => ∏ p ∈ P.filter Nat.Prime, (1 - (p : ℝ) ^ (-β))⁻¹)
      Filter.atTop
      (𝓝 (dirichletSeriesBC β hβ)) := by
  have hβ_ne : β ≠ 0 := by linarith [hβ]
  let f : ℕ →*₀ ℝ := dirichletSummandRealHom hβ_ne
  have hsum : Summable (fun n : ℕ => ‖f n‖) := by
    have h_exp : -β < -1 := by linarith [hβ]
    have h_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-β)) := Real.summable_nat_rpow.mpr h_exp
    refine h_rpow.congr (fun n => ?_)
    dsimp [f, dirichletSummandRealHom]
    exact (Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)).symm
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n :=
    fun {_ _} _ => f.map_mul _ _
  have h_hasProd :
      HasProd ({p | Nat.Prime p}.mulIndicator fun p => (1 - f p)⁻¹) (∑' n, f n) := by
    have h_ind := EulerProduct.eulerProduct_hasProd_mulIndicator f.map_one hmul hsum f.map_zero
    have h_eq : ({p | Nat.Prime p}.mulIndicator fun p => (1 - f p)⁻¹) =
        ({p | Nat.Prime p}.mulIndicator fun p => ∑' e : ℕ, f (p ^ e)) :=
      Set.mulIndicator_congr (fun p hp =>
        EulerProduct.one_sub_inv_eq_geometric_of_summable_norm hp hsum)
    simpa only [h_eq] using h_ind
  have h_tendsto : Filter.Tendsto
      (fun (P : Finset ℕ) => ∏ p ∈ P, {p | Nat.Prime p}.mulIndicator (fun p => (1 - f p)⁻¹) p)
      Filter.atTop (𝓝 (dirichletSeriesBC β hβ)) := by
    change Filter.Tendsto
      (fun (P : Finset ℕ) => ∏ p ∈ P, {p | Nat.Prime p}.mulIndicator (fun p => (1 - f p)⁻¹) p)
      Filter.atTop (𝓝 (∑' n : ℕ, f n))
    simpa only [HasProd, SummationFilter.unconditional_filter] using h_hasProd
  refine h_tendsto.congr (fun P => ?_)
  have h_prod : ∏ p ∈ P, {p | Nat.Prime p}.mulIndicator (fun p => (1 - f p)⁻¹) p =
      ∏ p ∈ P.filter Nat.Prime, (1 - f p)⁻¹ :=
    Finset.prod_mulIndicator_eq_prod_filter P (fun _ => fun p => (1 - f p)⁻¹)
      (fun _ => {p | Nat.Prime p}) id
  simpa [f, dirichletSummandRealHom] using h_prod

/-- Positivity of the Bost--Connes partition function $Z(β) > 0$ for $\beta > 1$. -/
@[rep_depth thermo, capstone]
theorem dirichletSeriesBC_pos (β : ℝ) (hβ : 1 < β) :
    0 < dirichletSeriesBC β hβ := by
  have hs : HasSum (fun n : ℕ => (n : ℝ) ^ (-β)) (dirichletSeriesBC β hβ) :=
    dirichletSeriesBC_hasSum β hβ
  have h_one : (1 : ℝ) ≤ dirichletSeriesBC β hβ := by
    have hterm : (fun n : ℕ => (n : ℝ) ^ (-β)) 1 = 1 := by simp
    have hnonneg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-β) := fun n =>
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h_sub : HasSum (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 1 1
    refine hasSum_le ?_ h_sub hs
    intro n
    by_cases hn : n = 1
    · subst hn; simp
    · simp [hn, hnonneg n]
  linarith

/-- Commutation of the Liouville chiral grading with the Bost--Connes modular flow,
reused from `BostConnesThermofield`. -/
@[rep_depth thermo, capstone]
theorem bostConnes_liouville_commutes_modular_flow (n : ℕ) (t : ℝ) :
    (InfoGeometry.BostConnes.liouvilleParity n : ℂ) * BostConnesThermofield.modular_phase t n =
      BostConnesThermofield.modular_phase t n * (InfoGeometry.BostConnes.liouvilleParity n : ℂ) :=
  BostConnesThermofield.liouville_commutes_modular_flow n t

/-- Thermal anomaly protection across all time parameters $t$ and sectors $n$,
reused from `BostConnesThermofield`. -/
@[rep_depth thermo, capstone]
theorem bostConnes_thermal_anomaly_protection :
    ∀ t : ℝ, ∀ n : ℕ,
      (InfoGeometry.BostConnes.liouvilleParity n : ℂ) * BostConnesThermofield.modular_phase t n =
        BostConnesThermofield.modular_phase t n * (InfoGeometry.BostConnes.liouvilleParity n : ℂ) :=
  BostConnesThermofield.thermal_anomaly_protection

/-- Reciprocal-zeta identity for the Bost--Connes Möbius L-series (Witten index),
reused from `BostConnesThermofield`. -/
@[rep_depth thermo, capstone]
theorem bostConnes_witten_index_eq_reciprocal_zeta (β : ℝ) (hβ : 1 < β) :
    L ↗ArithmeticFunction.moebius (β : ℂ) = (riemannZeta (β : ℂ))⁻¹ :=
  BostConnesThermofield.witten_index_eq_reciprocal_zeta β hβ

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

/--
Algebraic tensor-factor separation for the Cuntz-base/fiber split.

This closes the purely algebraic identity
`(S ⊗ id) (id ⊗ K) = (id ⊗ K) (S ⊗ id)`.  The bounded Hilbert-completion
commutation theorem is owned by `ConcreteHilbertCommutation.S_left_commutes_K_lp`.
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

/-- The concrete canonical V4-sewn Pauli boundary state has zero chiral index. -/
@[rep_depth thermo, capstone]
theorem concrete_canonical_sewn_boundary_anomaly_free :
    SouriauBostConnesClosureProofs.sewnChiralIndex
        SouriauBostConnesClosureProofs.canonicalSewnBoundaryState = 0 :=
  SouriauBostConnesClosureProofs.canonical_sewn_boundary_chiral_index_vanishes

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

/-- The RH route remains conditional on the supplied prime Lee--Yang hypotheses. -/
@[rep_depth thermo, capstone]
theorem conditional_RH_from_supplied_primeLeeYang
    {n : ℕ}
    (W : InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain.PrimeFerromagneticChain.LeeYangStabilityWitness (n := n))
    (hLeeYang : ∀ z : ℂ, W.partitionPolynomial.IsRoot z → OnLeeYangCircle z)
    {z : ℂ}
    (hz : W.partitionPolynomial.IsRoot z)
    (hpole : z.re ≠ -1) :
    OnCriticalLine (cayleyToTemperature z) :=
  partitionRoot_mapsToCriticalLine W.partitionPolynomial hLeeYang hz hpole

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
@[rep_depth thermo]
def VerifiedTransitionMatrix (bulk : BulkState) : Prop :=
  weylDenominatorProduct bulk.rootLattice bulk.thermalRootVariable =
      weylAlternatingSum bulk.rootLattice bulk.thermalRootVariable ∧
    finitePrimonPartition bulk.rootLattice bulk.beta =
      (evaluatedWeylDenominator bulk.rootLattice bulk.beta)⁻¹ ∧
    Filter.Tendsto Cayley.thermalCayley Filter.atTop (𝓝 1) ∧
    SouriauBostConnesClosureProofs.sewnChiralIndex
        SouriauBostConnesClosureProofs.canonicalSewnBoundaryState = 0 ∧
    YangBaxterProof.q ^ 5 = -1 ∧
      YangBaxterProof.τ ^ 2 + YangBaxterProof.τ = 1 ∧
    0 < phi ∧ 1 < phi ∧ 0 < phiInv ∧
      phi ^ 2 = phi + 1 ∧ phiInv ^ 2 + phiInv = 1 ∧
    ‖R1_phase‖ = 1 ∧
      ‖Rtau_phase‖ = 1 ∧
        R1_phase * Rtau_phase = Complex.exp (Complex.I * (2 * Real.pi / 5)) ∧
    diracSeaVacuum = (fun n : ℤ => n < 0) ∧
      (∀ w : DiracSeaBoundary, Option.bind (diracSeaStep w) diracSeaStep = none)

/-- Construct the verified finite/local matrix from the existing owner theorems. -/
@[rep_depth thermo, capstone]
theorem verifiedTransitionMatrix (bulk : BulkState) : VerifiedTransitionMatrix bulk := by
  refine ⟨finite_weylDenominator_eq_alternatingSum bulk, ?_⟩
  refine ⟨finite_primonPartition_eq_inverse_evaluatedWeylDenominator bulk, ?_⟩
  refine ⟨thermal_cayley_tendsto_boundary_one, ?_⟩
  refine ⟨concrete_canonical_sewn_boundary_anomaly_free, ?_⟩
  refine ⟨yangBaxter_boundary_parameters.1, yangBaxter_boundary_parameters.2, ?_⟩
  refine ⟨fibonacci_golden_ratio_identities.1, ?_⟩
  refine ⟨fibonacci_golden_ratio_identities.2.1, ?_⟩
  refine ⟨fibonacci_golden_ratio_identities.2.2.1, ?_⟩
  refine ⟨fibonacci_golden_ratio_identities.2.2.2.1, ?_⟩
  refine ⟨fibonacci_golden_ratio_identities.2.2.2.2, ?_⟩
  refine ⟨rmatrix_unitarity.1, rmatrix_unitarity.2.1, rmatrix_unitarity.2.2, ?_⟩
  exact diracSea_half_filled

/-- Public package constructor for the finite/local transition readout. -/
@[rep_depth thermo]
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
    VerifiedTransitionMatrix
      (souriau_bost_connes_transition_Package P primesP β hβpos).bulk :=
  verifiedTransitionMatrix _

/-! ## Proved Typed Archetypes -/

/-- Proved TypedArchetype for Dirichlet series convergence. -/
def dirichletSeriesConvergenceArchetype : TypedArchetype { β : ℝ // 1 < β } .proved where
  name     := `dirichletSeriesConvergenceArchetype
  phase    := 3
  claim    := fun ⟨β, hβ⟩ => HasSum (fun n : ℕ => (n : ℝ) ^ (-β)) (dirichletSeriesBC β hβ)
  evidence := fun ⟨β, hβ⟩ => dirichletSeriesBC_hasSum β hβ

#register_archetype dirichletSeriesConvergenceArchetype
#audit_archetype dirichletSeriesConvergenceArchetype

/-- Proved TypedArchetype for Bost-Connes Liouville modular flow commutation. -/
def bostConnesModularCommutationArchetype : TypedArchetype (ℕ × ℝ) .proved where
  name     := `bostConnesModularCommutationArchetype
  phase    := 3
  claim    := fun ⟨n, t⟩ =>
    (InfoGeometry.BostConnes.liouvilleParity n : ℂ) * BostConnesThermofield.modular_phase t n =
      BostConnesThermofield.modular_phase t n * (InfoGeometry.BostConnes.liouvilleParity n : ℂ)
  evidence := fun ⟨n, t⟩ => bostConnes_liouville_commutes_modular_flow n t

#register_archetype bostConnesModularCommutationArchetype
#audit_archetype bostConnesModularCommutationArchetype

/-- Proved TypedArchetype for Bost-Connes Witten index reciprocal zeta identity. -/
def bostConnesWittenIndexArchetype : TypedArchetype { β : ℝ // 1 < β } .proved where
  name     := `bostConnesWittenIndexArchetype
  phase    := 3
  claim    := fun ⟨β, _hβ⟩ => L ↗ArithmeticFunction.moebius (β : ℂ) = (riemannZeta (β : ℂ))⁻¹
  evidence := fun ⟨β, hβ⟩ => bostConnes_witten_index_eq_reciprocal_zeta β hβ

#register_archetype bostConnesWittenIndexArchetype
#audit_archetype bostConnesWittenIndexArchetype

/-- Proved TypedArchetype for thermal Cayley compactification boundary limit. -/
def thermalCayleyBoundaryArchetype : TypedArchetype Unit .proved where
  name     := `thermalCayleyBoundaryArchetype
  phase    := 3
  claim    := fun _ => Filter.Tendsto Cayley.thermalCayley Filter.atTop (𝓝 1)
  evidence := fun _ => thermal_cayley_tendsto_boundary_one

#register_archetype thermalCayleyBoundaryArchetype
#audit_archetype thermalCayleyBoundaryArchetype

/-- Proved TypedArchetype for finite prime Weyl denominator alternating sum identity. -/
def finiteWeylDenominatorArchetype : TypedArchetype BulkState .proved where
  name     := `finiteWeylDenominatorArchetype
  phase    := 3
  claim    := fun bulk =>
    weylDenominatorProduct bulk.rootLattice bulk.thermalRootVariable =
      weylAlternatingSum bulk.rootLattice bulk.thermalRootVariable
  evidence := fun bulk => finite_weylDenominator_eq_alternatingSum bulk

#register_archetype finiteWeylDenominatorArchetype
#audit_archetype finiteWeylDenominatorArchetype

/-- Proved TypedArchetype for the verified finite/local transition matrix. -/
def verifiedTransitionMatrixArchetype : TypedArchetype BulkState .proved where
  name     := `verifiedTransitionMatrixArchetype
  phase    := 3
  claim    := fun bulk => VerifiedTransitionMatrix bulk
  evidence := fun bulk => verifiedTransitionMatrix bulk

#register_archetype verifiedTransitionMatrixArchetype
#audit_archetype verifiedTransitionMatrixArchetype

/-! ## Completed Hilbert Cuntz--Clock Commutation & Bost--Connes Closure Debts (D1–D7) -/

/-- Proved TypedArchetype for the completed `lp` Hilbert Cuntz branch isometry and
phase-axis (`K^2 = -I`) commutation proved in `ConcreteHilbertCommutation`. -/
def completedHilbertCuntzClockCommutationArchetype : TypedArchetype Unit .proved where
  name     := `completedHilbertCuntzClockCommutationArchetype
  phase    := 3
  claim    := fun _ =>
    Isometry (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)) ∧
    (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)).comp
        (ConcreteHilbertCommutation.K_lp_clm (E := ℝ)) =
      (ConcreteHilbertCommutation.K_lp_clm (E := ℝ)).comp
        (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)) ∧
    (ConcreteHilbertCommutation.K_lp_clm (E := ℝ)).comp
        (ConcreteHilbertCommutation.K_lp_clm (E := ℝ)) =
      -(ContinuousLinearMap.id ℝ (ConcreteHilbertCommutation.H_lp ℝ))
  evidence := fun _ =>
    ⟨ConcreteHilbertCommutation.S_left_lp_clm_isometry (E := ℝ),
     ConcreteHilbertCommutation.S_left_lp_clm_commutes_K_lp_clm (E := ℝ),
     ConcreteHilbertCommutation.K_lp_clm_comp_self (E := ℝ)⟩

#register_archetype completedHilbertCuntzClockCommutationArchetype
#audit_archetype completedHilbertCuntzClockCommutationArchetype

/-- Proved TypedArchetype (Debt D1): analytic completion and non-vanishing of the
Riemann zeta function (`riemannZeta` is complex-differentiable away from `s = 1` and
non-vanishing on `Re(s) > 1`). -/
def d1AnalyticZetaCompletionCandidate : TypedArchetype ℂ .proved where
  name     := `d1AnalyticZetaCompletionCandidate
  phase    := 3
  claim    := fun s =>
    (1 < s.re → riemannZeta s ≠ 0) ∧
    (s ≠ 1 → DifferentiableAt ℂ riemannZeta s)
  evidence := fun _ => ⟨fun hs => riemannZeta_ne_zero_of_one_lt_re hs, fun hs => differentiableAt_riemannZeta hs⟩

#register_archetype d1AnalyticZetaCompletionCandidate
#audit_archetype d1AnalyticZetaCompletionCandidate

/-- Proved TypedArchetype (Debt D2): Unconditional infinite Euler product convergence
$\prod_{p \in P,\, p\text{ prime}} (1 - p^{-\beta})^{-1} \to Z(\beta)$ along `Finset ℕ`
for $\beta > 1$. -/
def d2EulerProductConvergenceCandidate : TypedArchetype { β : ℝ // 1 < β } .proved where
  name     := `d2EulerProductConvergenceCandidate
  phase    := 3
  claim    := fun ⟨β, hβ⟩ =>
    Filter.Tendsto
      (fun (P : Finset ℕ) => ∏ p ∈ P.filter Nat.Prime, (1 - (p : ℝ) ^ (-β))⁻¹)
      Filter.atTop
      (𝓝 (dirichletSeriesBC β hβ))
  evidence := fun ⟨β, hβ⟩ => dirichletSeriesBC_finset_euler_product β hβ

#register_archetype d2EulerProductConvergenceCandidate
#audit_archetype d2EulerProductConvergenceCandidate

lemma summable_nat_add_two_rpow_neg {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-β)) := by
  have h_exp : -β < -1 := by linarith [hβ]
  have h_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-β)) := Real.summable_nat_rpow.mpr h_exp
  exact (summable_nat_add_iff 2).mpr h_rpow

lemma summable_nat_add_one_rpow_neg {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-β)) := by
  have h_exp : -β < -1 := by linarith [hβ]
  have h_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-β)) := Real.summable_nat_rpow.mpr h_exp
  exact (summable_nat_add_iff 1).mpr h_rpow

lemma tendsto_pow_two_neg_beta :
    Filter.Tendsto (fun β : ℝ => (2 : ℝ) ^ (-β)) Filter.atTop (𝓝 0) := by
  have h_eq : (fun β : ℝ => (2 : ℝ) ^ (-β)) = (fun β : ℝ => ((2 : ℝ)⁻¹) ^ β) := by
    funext β
    exact (Real.rpow_neg zero_le_two β).trans (Real.inv_rpow zero_le_two β).symm
  rw [h_eq]
  exact tendsto_rpow_atTop_of_base_lt_one (2⁻¹) (by norm_num) (by norm_num)

lemma tendsto_zero_temperature_excited_tail :
    Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β)) Filter.atTop (𝓝 0) := by
  let C := ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ)
  have h_sum2 : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    summable_nat_add_two_rpow_neg (by norm_num)
  have h_upper : Filter.Tendsto (fun β : ℝ => (2 : ℝ) ^ (- (β - 2)) * C) Filter.atTop (𝓝 0) := by
    have h_rw : (fun β : ℝ => (2 : ℝ) ^ (- (β - 2)) * C) = (fun β : ℝ => (2 : ℝ) ^ (-β) * (4 * C)) := by
      funext β
      have h_split := Real.rpow_add zero_lt_two (-β) 2
      have h_eq : -β + 2 = - (β - 2) := by ring
      have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
      rw [← h_eq, h_split, h4]
      ring
    rw [h_rw]
    have h_lim := tendsto_pow_two_neg_beta.mul_const (4 * C)
    simpa using h_lim
  have h_le : ∀ᶠ β : ℝ in Filter.atTop,
      0 ≤ ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β) ∧
      ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β) ≤ (2 : ℝ) ^ (- (β - 2)) * C := by
    filter_upwards [Filter.eventually_ge_atTop 2] with β hβ
    have hβ_gt1 : 1 < β := by linarith
    have h_sumβ : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-β)) :=
      summable_nat_add_two_rpow_neg hβ_gt1
    refine ⟨tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _), ?_⟩
    have h_term_le : ∀ n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β) ≤ (2 : ℝ) ^ (- (β - 2)) * ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) := by
      intro n
      have hx_pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
      have h_add := Real.rpow_add hx_pos (- (β - 2)) (-2)
      have h_exp_eq : - (β - 2) + -2 = -β := by ring
      rw [h_exp_eq] at h_add
      rw [h_add]
      have h_rpow_le : ((n + 2 : ℕ) : ℝ) ^ (- (β - 2)) ≤ (2 : ℝ) ^ (- (β - 2)) := by
        apply Real.rpow_le_rpow_of_nonpos zero_lt_two
        · exact Nat.cast_le.mpr (Nat.le_add_left 2 n)
        · linarith
      exact mul_le_mul_of_nonneg_right h_rpow_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h_tsum_le := hasSum_le h_term_le h_sumβ.hasSum (h_sum2.mul_left _).hasSum
    rw [tsum_mul_left] at h_tsum_le
    exact h_tsum_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    (h_le.mono fun β h => h.1) (h_le.mono fun β h => h.2)

lemma tendsto_zero_temperature_full_partition :
    Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-β)) Filter.atTop (𝓝 1) := by
  have h_tail := tendsto_zero_temperature_excited_tail
  have h_add : Filter.Tendsto (fun β : ℝ => 1 + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β)) Filter.atTop (𝓝 1) := by
    have h1 := h_tail.const_add 1
    simpa using h1
  refine h_add.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with β hβ
  have hs : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-β)) := summable_nat_add_one_rpow_neg hβ
  have h_split := hs.tsum_eq_zero_add
  have h0 : ((0 + 1 : ℕ) : ℝ) ^ (-β) = 1 := by simp
  have hstep : (fun n : ℕ => (((n + 1) + 1 : ℕ) : ℝ) ^ (-β)) = (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-β)) := rfl
  rw [h_split, h0, hstep]

/-- Proved TypedArchetype (Debt D3): Analytic zero-temperature KMS boundary crystallization
$\lim_{\beta \to \infty} Z_{\ge 1}(\beta) = 1$ with excited-sector tail extinction
$\lim_{\beta \to \infty} \sum_{n \ge 2} n^{-\beta} = 0$. -/
def d3ZeroTempCantorCrystallizationCandidate : TypedArchetype Unit .proved where
  name     := `d3ZeroTempCantorCrystallizationCandidate
  phase    := 3
  claim    := fun _ =>
    Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-β)) Filter.atTop (𝓝 1) ∧
    Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-β)) Filter.atTop (𝓝 0)
  evidence := fun _ => ⟨tendsto_zero_temperature_full_partition, tendsto_zero_temperature_excited_tail⟩

#register_archetype d3ZeroTempCantorCrystallizationCandidate
#audit_archetype d3ZeroTempCantorCrystallizationCandidate

lemma summable_log_sq_rpow_neg {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)) := by
  let ε : ℝ := (β - 1) / 4
  have hε : 0 < ε := by
    change 0 < (β - 1) / 4
    linarith [hβ]
  have h_exp : 2 * ε - β < -1 := by
    change 2 * ((β - 1) / 4) - β < -1
    linarith [hβ]
  have h_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (2 * ε - β)) := Real.summable_nat_rpow.mpr h_exp
  have h_mul : Summable (fun n : ℕ => (1 / ε ^ 2) * (n : ℝ) ^ (2 * ε - β)) := h_rpow.mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h_mul
  by_cases hn : n = 0
  · subst hn; simp; positivity
  · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hlog := Real.log_natCast_le_rpow_div n hε
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have hsq : (Real.log (n : ℝ)) ^ 2 ≤ ((n : ℝ) ^ ε / ε) ^ 2 := by
      nlinarith [hlog_nonneg, hlog]
    have hdiv : ((n : ℝ) ^ ε / ε) ^ 2 = (1 / ε ^ 2) * ((n : ℝ) ^ ε) ^ 2 := by
      rw [div_pow]
      ring
    have hpow2 : ((n : ℝ) ^ ε) ^ 2 = (n : ℝ) ^ (2 * ε) := by
      rw [← Real.rpow_natCast, Nat.cast_two, ← Real.rpow_mul (le_of_lt hn_pos)]
      ring_nf
    have hmul_rpow : (n : ℝ) ^ (2 * ε) * (n : ℝ) ^ (-β) = (n : ℝ) ^ (2 * ε - β) := by
      have hr := Real.rpow_add hn_pos (2 * ε) (-β)
      have heq : 2 * ε + -β = 2 * ε - β := by ring
      rw [heq] at hr
      exact hr.symm
    calc (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)
      _ ≤ ((n : ℝ) ^ ε / ε) ^ 2 * (n : ℝ) ^ (-β) := mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (1 / ε ^ 2) * ((n : ℝ) ^ ε) ^ 2 * (n : ℝ) ^ (-β) := by rw [hdiv]
      _ = (1 / ε ^ 2) * (((n : ℝ) ^ ε) ^ 2 * (n : ℝ) ^ (-β)) := by ring
      _ = (1 / ε ^ 2) * ((n : ℝ) ^ (2 * ε) * (n : ℝ) ^ (-β)) := by rw [hpow2]
      _ = (1 / ε ^ 2) * (n : ℝ) ^ (2 * ε - β) := by rw [hmul_rpow]

lemma tendsto_souriau_fisher_collapse :
    Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)) Filter.atTop (𝓝 0) := by
  let C := ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ)
  have h_sum2 : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    summable_nat_add_two_rpow_neg (by norm_num)
  have h_upper : Filter.Tendsto (fun β : ℝ => (2 : ℝ) ^ (- (β - 4)) * C) Filter.atTop (𝓝 0) := by
    have h_rw : (fun β : ℝ => (2 : ℝ) ^ (- (β - 4)) * C) = (fun β : ℝ => (2 : ℝ) ^ (-β) * (16 * C)) := by
      funext β
      have h_split := Real.rpow_add zero_lt_two (-β) 4
      have h_eq : -β + 4 = - (β - 4) := by ring
      have h16 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
      rw [← h_eq, h_split, h16]
      ring
    rw [h_rw]
    have h_lim := tendsto_pow_two_neg_beta.mul_const (16 * C)
    simpa using h_lim
  have h_shift_eq : ∀ β : ℝ, 1 < β →
      (∑' n : ℕ, (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)) =
      ∑' n : ℕ, (Real.log ((n + 2 : ℕ) : ℝ)) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-β) := by
    intro β hβ
    let g : ℕ → ℝ := fun n => (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)
    have hg : Summable g := summable_log_sq_rpow_neg hβ
    have h0 : g 0 = 0 := by simp [g]
    have h1 : g 1 = 0 := by simp [g]
    have hg_shift : Summable (fun n => g (n + 1)) := (summable_nat_add_iff 1).mpr hg
    have h_shift1 : (∑' n, g n) = ∑' n, g (n + 1) := by rw [hg.tsum_eq_zero_add, h0, zero_add]
    have h_shift2 : (∑' n, g (n + 1)) = ∑' n, g (n + 2) := by
      have hs := hg_shift.tsum_eq_zero_add
      have hg2 : (fun n => g (n + 1 + 1)) = (fun n => g (n + 2)) := rfl
      rw [hs, h1, zero_add, hg2]
    rw [h_shift1, h_shift2]
  have h_tail_lim : Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, (Real.log ((n + 2 : ℕ) : ℝ)) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-β)) Filter.atTop (𝓝 0) := by
    have h_le : ∀ᶠ β : ℝ in Filter.atTop,
        0 ≤ ∑' n : ℕ, (Real.log ((n + 2 : ℕ) : ℝ)) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-β) ∧
        ∑' n : ℕ, (Real.log ((n + 2 : ℕ) : ℝ)) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-β) ≤ (2 : ℝ) ^ (- (β - 4)) * C := by
      filter_upwards [Filter.eventually_ge_atTop 4] with β hβ
      have hβ_gt1 : 1 < β := by linarith
      have h_sum_full : Summable (fun n : ℕ => (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)) :=
        summable_log_sq_rpow_neg hβ_gt1
      have h_sumβ : Summable (fun n : ℕ => (Real.log ((n + 2 : ℕ) : ℝ)) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-β)) := by
        exact (summable_nat_add_iff 2).mpr h_sum_full
      refine ⟨tsum_nonneg (fun n => by positivity), ?_⟩
      have h_term_le : ∀ n : ℕ,
          (Real.log ((n + 2 : ℕ) : ℝ)) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-β) ≤
          (2 : ℝ) ^ (- (β - 4)) * ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) := by
        intro n
        have hx_pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
        have hlog_le : Real.log ((n + 2 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Real.log_le_self (by positivity)
        have hlog_nonneg : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
        have hlog_sq : (Real.log ((n + 2 : ℕ) : ℝ)) ^ 2 ≤ ((n + 2 : ℕ) : ℝ) ^ 2 := by
          nlinarith [hlog_nonneg, hlog_le]
        have h_add := Real.rpow_add hx_pos (- (β - 4)) (-4)
        have h_exp_eq : - (β - 4) + -4 = -β := by ring
        rw [h_exp_eq] at h_add
        have h_rpow_le : ((n + 2 : ℕ) : ℝ) ^ (- (β - 4)) ≤ (2 : ℝ) ^ (- (β - 4)) := by
          apply Real.rpow_le_rpow_of_nonpos zero_lt_two
          · exact Nat.cast_le.mpr (Nat.le_add_left 2 n)
          · linarith
        have h_two_four : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) * ((n + 2 : ℕ) : ℝ) ^ (-4 : ℝ) = ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) := by
          have hr := Real.rpow_add hx_pos 2 (-4)
          have heq : (2 : ℝ) + -4 = -2 := by norm_num
          rw [heq] at hr
          exact hr.symm
        have h_step1 : ((n + 2 : ℕ) : ℝ) ^ (-β) ≤ (2 : ℝ) ^ (- (β - 4)) * ((n + 2 : ℕ) : ℝ) ^ (-4 : ℝ) := by
          rw [h_add]
          exact mul_le_mul_of_nonneg_right h_rpow_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        have h_step2 : (Real.log ((n + 2 : ℕ) : ℝ)) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-β) ≤
            ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) * ((2 : ℝ) ^ (- (β - 4)) * ((n + 2 : ℕ) : ℝ) ^ (-4 : ℝ)) := by
          rw [show ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) = ((n + 2 : ℕ) : ℝ) ^ 2 by simp]
          exact mul_le_mul hlog_sq h_step1 (by positivity) (by positivity)
        calc (Real.log ((n + 2 : ℕ) : ℝ)) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-β)
          _ ≤ ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) * ((2 : ℝ) ^ (- (β - 4)) * ((n + 2 : ℕ) : ℝ) ^ (-4 : ℝ)) := h_step2
          _ = (2 : ℝ) ^ (- (β - 4)) * (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) * ((n + 2 : ℕ) : ℝ) ^ (-4 : ℝ)) := by ring
          _ = (2 : ℝ) ^ (- (β - 4)) * ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) := by rw [h_two_four]
      have h_tsum_le := hasSum_le h_term_le h_sumβ.hasSum (h_sum2.mul_left _).hasSum
      rw [tsum_mul_left] at h_tsum_le
      exact h_tsum_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
      (h_le.mono fun β h => h.1) (h_le.mono fun β h => h.2)
  refine h_tail_lim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with β hβ
  exact (h_shift_eq β hβ).symm

lemma tendsto_souriau_fisher_blowup :
    Filter.Tendsto (fun β : ℝ => ∑' n : ℕ, (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β))
      (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  let c : ℝ := (Real.log 2) ^ 2 / 4
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := by dsimp [c]; positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (M / c))
  have hk1 : 1 ≤ k := by
    have : 1 < (k : ℝ) := (le_max_left 1 (M / c)).trans_lt hk
    exact_mod_cast le_of_lt this
  have hkM : M ≤ (k : ℝ) ^ 2 * c := by
    have h_div : M / c < (k : ℝ) := (le_max_right 1 (M / c)).trans_lt hk
    have h_lin : M < (k : ℝ) * c := by
      have := (div_lt_iff₀ hc_pos).mp h_div
      linarith
    have hk_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ (k : ℝ) by exact_mod_cast hk1]
    nlinarith
  let delta_val : ℝ := 1 / (k + 1 : ℝ)
  have h_delta_pos : 0 < delta_val := by dsimp [delta_val]; positivity
  have h_mem : Set.Ioo 1 (1 + delta_val) ∈ nhdsWithin 1 (Set.Ioi 1) := Ioo_mem_nhdsGT (by linarith)
  filter_upwards [h_mem] with β hβ
  have hβ1 : 1 < β := hβ.1
  have hβδ : β < 1 + delta_val := hβ.2
  have h_summable : Summable (fun n : ℕ => (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)) :=
    summable_log_sq_rpow_neg hβ1
  let S_k : Finset ℕ := Finset.Ico (2 ^ k) (2 ^ (k + 1))
  have h_le_tsum : (∑ n ∈ S_k, (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β)) ≤
      ∑' n : ℕ, (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β) :=
    sum_le_hasSum S_k (fun _ _ => by positivity) h_summable.hasSum
  have h_term_ge : ∀ n ∈ S_k, (k : ℝ) ^ 2 * (Real.log 2) ^ 2 * (2 : ℝ) ^ (- (k + 2 : ℝ)) ≤
      (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn2k : 2 ^ k ≤ n := hn.1
    have hnk1 : n < 2 ^ (k + 1) := hn.2
    have h2k_pos : 0 < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlog_le : Real.log ((2 ^ k : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log h2k_pos
      exact_mod_cast hn2k
    have h2k_cast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by simp
    have hlog_2k : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
      rw [h2k_cast, Real.log_pow]
    rw [hlog_2k] at hlog_le
    have hlog_sq : ((k : ℝ) * Real.log 2) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
      have : 0 ≤ (k : ℝ) * Real.log 2 := by positivity
      nlinarith [hlog_le]
    have hlog_sq_eq : ((k : ℝ) * Real.log 2) ^ 2 = (k : ℝ) ^ 2 * (Real.log 2) ^ 2 := mul_pow (k : ℝ) (Real.log 2) 2
    rw [hlog_sq_eq] at hlog_sq
    have hn_le_pow : (n : ℝ) ≤ (2 : ℝ) ^ (k + 1 : ℝ) := by
      have h1 : (n : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast le_of_lt hnk1
      have h2 : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1 : ℝ) := by
        push_cast
        rw [← Real.rpow_natCast]
        push_cast; rfl
      rwa [h2] at h1
    have hrpow1 : ((2 : ℝ) ^ (k + 1 : ℝ)) ^ (-β) ≤ (n : ℝ) ^ (-β) := by
      apply Real.rpow_le_rpow_of_nonpos hn_pos hn_le_pow (by linarith)
    have hrpow_eq : ((2 : ℝ) ^ (k + 1 : ℝ)) ^ (-β) = (2 : ℝ) ^ (- ((k + 1 : ℝ) * β)) := by
      have hr := Real.rpow_mul zero_le_two (k + 1 : ℝ) (-β)
      have heq : (k + 1 : ℝ) * -β = - ((k + 1 : ℝ) * β) := by ring
      rw [heq] at hr
      exact hr.symm
    have hrpow2 : (2 : ℝ) ^ (- (k + 2 : ℝ)) ≤ (2 : ℝ) ^ (- ((k + 1 : ℝ) * β)) := by
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      have hδ_eq : (k + 1 : ℝ) * (1 + delta_val) = (k + 1 : ℝ) + 1 := by
        dsimp [delta_val]
        have : (k + 1 : ℝ) * (1 / (k + 1 : ℝ)) = 1 := mul_one_div_cancel (by positivity)
        linarith
      have : (k + 1 : ℝ) * β < (k + 1 : ℝ) + 1 := by
        have h_mul := mul_lt_mul_of_pos_left hβδ (show 0 < (k + 1 : ℝ) by positivity)
        rwa [hδ_eq] at h_mul
      linarith
    have hrpow_bound : (2 : ℝ) ^ (- (k + 2 : ℝ)) ≤ (n : ℝ) ^ (-β) := by
      rw [← hrpow_eq] at hrpow2
      exact hrpow2.trans hrpow1
    exact mul_le_mul hlog_sq hrpow_bound (by positivity) (by positivity)
  have h_card : S_k.card = 2 ^ k := by
    dsimp [S_k]
    rw [Nat.card_Ico]
    have : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    omega
  have h_sum_lower : (k : ℝ) ^ 2 * c ≤ ∑ n ∈ S_k, (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β) := by
    have h_sum_const := Finset.sum_le_sum h_term_ge
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum_const
    have h_card_cast : (S_k.card : ℝ) = (2 : ℝ) ^ (k : ℝ) := by
      rw [h_card]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast]
    rw [h_card_cast] at h_sum_const
    have h_prod : (2 : ℝ) ^ (k : ℝ) * ((k : ℝ) ^ 2 * (Real.log 2) ^ 2 * (2 : ℝ) ^ (- (k + 2 : ℝ))) =
        (k : ℝ) ^ 2 * c := by
      have h2 : (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (- (k + 2 : ℝ)) = 1 / 4 := by
        have hr := Real.rpow_add zero_lt_two (k : ℝ) (- (k + 2 : ℝ))
        have heq : (k : ℝ) + - (k + 2 : ℝ) = -2 := by ring
        rw [heq] at hr
        have h4 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by norm_num
        rw [h4] at hr
        exact hr.symm
      calc (2 : ℝ) ^ (k : ℝ) * ((k : ℝ) ^ 2 * (Real.log 2) ^ 2 * (2 : ℝ) ^ (- (k + 2 : ℝ)))
        _ = (k : ℝ) ^ 2 * (Real.log 2) ^ 2 * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (- (k + 2 : ℝ))) := by ring
        _ = (k : ℝ) ^ 2 * (Real.log 2) ^ 2 * (1 / 4) := by rw [h2]
        _ = (k : ℝ) ^ 2 * c := by dsimp [c]; ring
    rwa [h_prod] at h_sum_const
  linarith

/-- Proved TypedArchetype (Debt D4): Analytic Souriau--Fisher log-energy variance metric
$g_{\mathrm{SB}}(\beta) = \sum_{n \ge 1} (\log n)^2 n^{-\beta}$ blowing up as $\beta \to 1^+$
and collapsing at zero temperature $\beta \to \infty$. -/
def d4SouriauFisherMetricCollapseCandidate : TypedArchetype Unit .proved where
  name     := `d4SouriauFisherMetricCollapseCandidate
  phase    := 3
  claim    := fun _ =>
    Filter.Tendsto
      (fun β : ℝ => ∑' n : ℕ, (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β))
      (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop ∧
    Filter.Tendsto
      (fun β : ℝ => ∑' n : ℕ, (Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (-β))
      Filter.atTop (𝓝 0)
  evidence := fun _ => ⟨tendsto_souriau_fisher_blowup, tendsto_souriau_fisher_collapse⟩

#register_archetype d4SouriauFisherMetricCollapseCandidate
#audit_archetype d4SouriauFisherMetricCollapseCandidate

/-- Proved TypedArchetype (Debt D5): Completed two-branch Hilbert Cuntz $O_2$ isometric decomposition
on `H_lp ℝ` (constructing `S_right` commuting with `K_lp_clm` and splitting `H_lp ℝ` into
orthogonal complementary isometric ranges alongside `S_left_lp_clm`). -/
def d5CompletedCuntzBoundaryFunctorCandidate : TypedArchetype Unit .proved where
  name     := `d5CompletedCuntzBoundaryFunctorCandidate
  phase    := 3
  claim    := fun _ =>
    ∃ (S_right : ConcreteHilbertCommutation.H_lp ℝ →L[ℝ] ConcreteHilbertCommutation.H_lp ℝ),
      Isometry S_right ∧
      S_right.comp (ConcreteHilbertCommutation.K_lp_clm (E := ℝ)) =
        (ConcreteHilbertCommutation.K_lp_clm (E := ℝ)).comp S_right ∧
      (∀ φ₁ φ₂ : ConcreteHilbertCommutation.H_lp ℝ,
        (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)) φ₁ = S_right φ₂ →
          φ₁ = 0 ∧ φ₂ = 0) ∧
      (∀ ψ : ConcreteHilbertCommutation.H_lp ℝ,
        ∃ φ₁ φ₂ : ConcreteHilbertCommutation.H_lp ℝ,
          ψ = (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)) φ₁ + S_right φ₂)
  evidence := fun _ =>
    ⟨ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ),
     ConcreteHilbertCuntzO2.S_right_lp_clm_isometry (E := ℝ),
     ConcreteHilbertCuntzO2.S_right_lp_clm_commutes_K_lp_clm (E := ℝ),
     ConcreteHilbertCuntzO2.S_left_right_lp_clm_disjoint (E := ℝ),
     ConcreteHilbertCuntzO2.cuntz_o2_lp_decomposition (E := ℝ)⟩

#register_archetype d5CompletedCuntzBoundaryFunctorCandidate
#audit_archetype d5CompletedCuntzBoundaryFunctorCandidate

section BraidedClaim
open CategoryTheory CategoryTheory.MonoidalCategory

private def FibonacciBraidedClaimPred
    [CategoryTheory.Category.{0} (FibObject → ℕ)]
    [MonoidalCategory (FibObject → ℕ)]
    [BraidedCategory (FibObject → ℕ)] : Prop :=
  let oneVec : FibObject → ℕ := fun x => match x with | FibObject.unit => 1 | FibObject.tau => 0
  let tauVec : FibObject → ℕ := fun x => match x with | FibObject.unit => 0 | FibObject.tau => 1
  (𝟙_ (FibObject → ℕ) = oneVec) ∧
  (∀ X Y : FibObject → ℕ,
    (X ⊗ Y) FibObject.unit = X FibObject.unit * Y FibObject.unit + X FibObject.tau * Y FibObject.tau ∧
    (X ⊗ Y) FibObject.tau =
      X FibObject.unit * Y FibObject.tau + X FibObject.tau * Y FibObject.unit +
        X FibObject.tau * Y FibObject.tau) ∧
  Nonempty ((oneVec ⟶ oneVec) ≃ ℂ) ∧
  Nonempty ((tauVec ⟶ tauVec) ≃ ℂ) ∧
  Nonempty (Unique (oneVec ⟶ tauVec)) ∧
  Nonempty ((oneVec ⟶ (tauVec ⊗ tauVec)) ≃ ℂ) ∧
  Nonempty ((tauVec ⟶ (tauVec ⊗ tauVec)) ≃ ℂ) ∧
  ((BraidedCategory.braiding tauVec tauVec).hom ≫
    (BraidedCategory.braiding tauVec tauVec).hom ≠ 𝟙 (tauVec ⊗ tauVec))

end BraidedClaim

/-- Proved TypedArchetype (Debt D6): Full Mathlib `BraidedCategory` instance on Fibonacci multiplicity
vectors `FibObject → ℕ` realizing the Fibonacci fusion ring, Schur simplicity on `{1, τ}`,
and non-symmetric braiding (`c_{τ,τ}^2 ≠ id`) with pentagon and hexagon coherence. -/
def d6BraidedAnyonCategoryCoherenceCandidate : TypedArchetype Unit .proved where
  name     := `d6BraidedAnyonCategoryCoherenceCandidate
  phase    := 3
  claim    := fun _ =>
    ∃ (instCat : CategoryTheory.Category.{0} (FibObject → ℕ))
      (instMon : @CategoryTheory.MonoidalCategory.{0, 0} (FibObject → ℕ) instCat)
      (instBraid : @CategoryTheory.BraidedCategory.{0, 0} (FibObject → ℕ) instCat instMon),
      @FibonacciBraidedClaimPred instCat instMon instBraid
  evidence := fun _ =>
    ⟨InfoGeometry.Categorical.FibonacciMonoidalBraidedInstance.fibVecCategory,
     InfoGeometry.Categorical.FibonacciMonoidalBraidedInstance.fibVecMonoidalCategory,
     InfoGeometry.Categorical.FibonacciMonoidalBraidedInstance.fibVecBraidedCategory,
     InfoGeometry.Categorical.FibonacciMonoidalBraidedInstance.fibonacci_braided_category_package⟩

#register_archetype d6BraidedAnyonCategoryCoherenceCandidate
#audit_archetype d6BraidedAnyonCategoryCoherenceCandidate

/-- Proved TypedArchetype (Debt D7): Infinite-dimensional `H_lp` Hilbert-space sewn
boundary anomaly cancellation, `Cl(1,1)` involutions (`J_lp`, `ε_lp`), non-commuting
Cuntz `O₂` sewing invariance, non-zero sewn Cantor vacuum state, and `tsum` chiral
index vanishing from `ConcreteHilbertSewnAnomaly`. -/
def d7InfiniteHilbertSewnAnomalyCancellationArchetype : TypedArchetype Unit .proved where
  name     := `d7InfiniteHilbertSewnAnomalyCancellationArchetype
  phase    := 3
  claim    := fun _ =>
    Isometry (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)) ∧
    Isometry (ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)) ∧
    (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
        (ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)) =
      -((ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)).comp
        (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) ∧
    (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)).comp
        (ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ)) ≠
      (ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ)).comp
        (ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)) ∧
    (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
        ((ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ)).comp
          (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) =
      ConcreteHilbertCommutation.S_left_lp_clm (E := ℝ) ∧
    (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
        ((ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ)).comp
          (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) =
      ConcreteHilbertCuntzO2.S_right_lp_clm (E := ℝ) ∧
    ConcreteHilbertSewnAnomaly.canonicalCantorSewnState ≠ 0 ∧
    ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)
        ConcreteHilbertSewnAnomaly.canonicalCantorSewnState =
      ConcreteHilbertSewnAnomaly.canonicalCantorSewnState ∧
    (∀ (B : ConcreteHilbertCommutation.H_lp ℝ →L[ℝ] ConcreteHilbertCommutation.H_lp ℝ),
      (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
          (B.comp (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) = B →
      ∀ (ψ : ConcreteHilbertCommutation.H_lp ℝ),
        ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ) ψ = ψ →
        inner ℝ ψ (((ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)).comp B) ψ) = 0) ∧
    (∀ {ι : Type 0} (σ : ι ≃ ι) (e : ι → ConcreteHilbertCommutation.H_lp ℝ),
      (∀ i, e (σ i) = ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ) (e i)) →
      ∀ (B : ConcreteHilbertCommutation.H_lp ℝ →L[ℝ] ConcreteHilbertCommutation.H_lp ℝ),
        (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).comp
            (B.comp (ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ))) = B →
        Summable (fun i : ι =>
          inner ℝ (e i) (((ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)).comp B) (e i))) →
        (∑' i : ι,
          inner ℝ (e i) (((ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)).comp B) (e i))) = 0)
  evidence := fun _ =>
    ⟨ConcreteHilbertSewnAnomaly.J_lp_clm_isometry (E := ℝ),
     ConcreteHilbertSewnAnomaly.epsilon_lp_clm_isometry (E := ℝ),
     ConcreteHilbertSewnAnomaly.J_lp_clm_anticomm_epsilon_lp_clm (E := ℝ),
     ConcreteHilbertSewnAnomaly.S_left_right_lp_clm_noncomm,
     ConcreteHilbertSewnAnomaly.S_left_lp_clm_sewn_invariant (E := ℝ),
     ConcreteHilbertSewnAnomaly.S_right_lp_clm_sewn_invariant (E := ℝ),
     ConcreteHilbertSewnAnomaly.canonicalCantorSewnState_ne_zero,
     ConcreteHilbertSewnAnomaly.canonicalCantorSewnState_fixed,
     fun B hB ψ hψ =>
       ConcreteHilbertSewnAnomaly.infinite_hilbert_sewn_chiral_expectation_zero B hB ψ hψ,
     fun σ e he B hB hsum =>
       ConcreteHilbertSewnAnomaly.infinite_hilbert_tsum_chiral_index_zero σ e he B hB hsum⟩

#register_archetype d7InfiniteHilbertSewnAnomalyCancellationArchetype
#audit_archetype d7InfiniteHilbertSewnAnomalyCancellationArchetype

end InfoGeometry.Canonical.SouriauBostConnesTransition
