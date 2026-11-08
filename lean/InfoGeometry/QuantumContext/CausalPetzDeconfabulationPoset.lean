import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Order
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import InfoGeometry.Physics.FiniteRelativeModularOperator
import InfoGeometry.QuantumContext.CausalPetzRelativeModularBridge
import InfoGeometry.Epistemology.Deconfabulation
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Deconfabulation & Synthesis: The Causal POSET of the Causal Petz Recovery Map

This module formalizes the rigorous mathematical deconfabulation of the
"Drunken Professor" stream of consciousness on causal operator truncation and
retrocausal quantum context recovery:

$$\mathcal{R}_{\rho, \mathcal{E}}(\sigma) = V \sigma V^\dagger, \qquad V \equiv \rho^{1/2} (\Pi \rho \Pi)^{+/2}$$

### The 6 Canonical Mathematical Archetypes
1. **$\mathcal{A}_1$ (`pastFiltrationProjector`)**:
   Discrete Past Filtration & Triangular Projector ($P_i, \Pi, \Pi^\perp$).
2. **$\mathcal{A}_2$ (`causalPinchingChannel`)**:
   Causal Pinching Channel $\mathcal{E}(X) = \Pi X \Pi$ & Acausal Annihilation ($\mathcal{E}(\Pi^\perp) = 0$).
3. **$\mathcal{A}_3$ (`petzGramIntertwiner`)**:
   Petz Intertwiner & Gram Partial Isometry ($P^+ \rho P^+ = P^+ (\Pi \rho \Pi) P^+$).
4. **$\mathcal{A}_4$ (`pastFutureBlockSplitting`)**:
   Past-Future $2 \times 2$ Subspace Splitting & Transfer Operators ($K_i, L_i$).
5. **$\mathcal{A}_5$ (`retrocausalReconstruction`)**:
   Retrocausal Reconstruction Matrix across the 4 Peirce blocks (Past, Coherences, Future).
6. **$\mathcal{A}_6$ (`markovModularSufficiency`)**:
   Quantum Markov Sufficiency & Relative Modular Flow Intertwining ($\Delta_{\rho, \sigma} \circ \mathcal{E} = \mathcal{E} \circ \Delta_{\rho, \sigma}$).

### The Strict Causal POSET Architecture
$$\mathcal{A}_1 \prec \mathcal{A}_2 \prec \mathcal{A}_3 \prec \mathcal{A}_4 \prec \mathcal{A}_5 \prec \mathcal{A}_6$$

All proofs are native Mathlib with 0 sorry, 0 admit, and 0 custom axioms.
-/

namespace InfoGeometry.QuantumContext.CausalPetzDeconfabulationPoset

open scoped Matrix BigOperators
open InfoGeometry.Physics.FiniteRelativeModularOperator
open InfoGeometry.QuantumContext.CausalPetzRelativeModularBridge
open InfoGeometry.Epistemology.Deconfabulation

/-! ### Part I: The Strict Causal POSET of Mathematical Archetypes -/

/-- The six canonical mathematical archetypes extracted from the raw stream. -/
inductive CausalPetzArchetype
  | pastFiltrationProjector      -- 𝒜₁
  | causalPinchingChannel        -- 𝒜₂
  | petzGramIntertwiner          -- 𝒜₃
  | pastFutureBlockSplitting     -- 𝒜₄
  | retrocausalReconstruction    -- 𝒜₅
  | markovModularSufficiency     -- 𝒜₆
  deriving DecidableEq

instance : Fintype CausalPetzArchetype where
  elems := { .pastFiltrationProjector, .causalPinchingChannel,
             .petzGramIntertwiner, .pastFutureBlockSplitting,
             .retrocausalReconstruction, .markovModularSufficiency }
  complete := by
    intro x
    cases x <;> simp

/-- Explicit prerequisite index sets encoding the causal ordering of archetypes. -/
def prerequisites : CausalPetzArchetype → Finset ℕ
  | .pastFiltrationProjector   => {0}
  | .causalPinchingChannel     => {0, 1}
  | .petzGramIntertwiner       => {0, 1, 2}
  | .pastFutureBlockSplitting  => {0, 1, 2, 3}
  | .retrocausalReconstruction => {0, 1, 2, 3, 4}
  | .markovModularSufficiency  => {0, 1, 2, 3, 4, 5}

/-- **Theorem**: The prerequisite encoding is strictly injective. -/
theorem prerequisites_injective : Function.Injective prerequisites := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals revert h; decide

/-- The canonical Partial Order on the Causal Petz archetypes. -/
instance : PartialOrder CausalPetzArchetype :=
  PartialOrder.lift prerequisites prerequisites_injective

/-- Decidable ordering relation for automated verification. -/
instance : DecidableRel (α := CausalPetzArchetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

instance : DecidableRel (α := CausalPetzArchetype) (· < ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊂ prerequisites right))

/-- **POSET Theorem 1**: $\mathcal{A}_1$ is the absolute root of the causal poset. -/
theorem a1_precedes_all (a : CausalPetzArchetype) :
    CausalPetzArchetype.pastFiltrationProjector ≤ a := by
  cases a <;> decide

/-- **POSET Theorem 2**: $\mathcal{A}_1 \prec \mathcal{A}_2$: Past filtration precedes pinching channel. -/
theorem a1_le_a2 :
    CausalPetzArchetype.pastFiltrationProjector ≤ CausalPetzArchetype.causalPinchingChannel := by
  decide

/-- **POSET Theorem 3**: $\mathcal{A}_2 \prec \mathcal{A}_3$: Pinching channel precedes Petz intertwiner. -/
theorem a2_le_a3 :
    CausalPetzArchetype.causalPinchingChannel ≤ CausalPetzArchetype.petzGramIntertwiner := by
  decide

/-- **POSET Theorem 4**: $\mathcal{A}_3 \prec \mathcal{A}_4$: Petz intertwiner precedes $2 \times 2$ block splitting. -/
theorem a3_le_a4 :
    CausalPetzArchetype.petzGramIntertwiner ≤ CausalPetzArchetype.pastFutureBlockSplitting := by
  decide

/-- **POSET Theorem 5**: $\mathcal{A}_4 \prec \mathcal{A}_5$: Block splitting precedes retrocausal reconstruction. -/
theorem a4_le_a5 :
    CausalPetzArchetype.pastFutureBlockSplitting ≤ CausalPetzArchetype.retrocausalReconstruction := by
  decide

/-- **POSET Theorem 6**: $\mathcal{A}_5 \prec \mathcal{A}_6$: Reconstruction precedes modular sufficiency. -/
theorem a5_le_a6 :
    CausalPetzArchetype.retrocausalReconstruction ≤ CausalPetzArchetype.markovModularSufficiency := by
  decide

/-- **POSET Theorem 7 (Strict Causal Chain)**:
    All 5 steps in the chain are strict inequalities:
    $\mathcal{A}_1 < \mathcal{A}_2 < \mathcal{A}_3 < \mathcal{A}_4 < \mathcal{A}_5 < \mathcal{A}_6$. -/
theorem strict_causal_chain :
    (CausalPetzArchetype.pastFiltrationProjector < CausalPetzArchetype.causalPinchingChannel) ∧
    (CausalPetzArchetype.causalPinchingChannel < CausalPetzArchetype.petzGramIntertwiner) ∧
    (CausalPetzArchetype.petzGramIntertwiner < CausalPetzArchetype.pastFutureBlockSplitting) ∧
    (CausalPetzArchetype.pastFutureBlockSplitting < CausalPetzArchetype.retrocausalReconstruction) ∧
    (CausalPetzArchetype.retrocausalReconstruction < CausalPetzArchetype.markovModularSufficiency) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ### Part II: Archetype 𝒜₁ — Discrete Past Filtration & Triangular Projector -/

/-- **Theorem**: Triangular rank formula:
    $2 \sum_{i=0}^{N-1} (i + 1) = N(N + 1)$. -/
theorem triangular_rank_formula (N : ℕ) :
    2 * (∑ i ∈ Finset.range N, (i + 1)) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- An algebraic causal projector system with complementary acausal projector. -/
structure CausalProjectorSystem {R : Type*} [Ring R] (Pi Pi_perp : R) : Prop where
  proj_pi       : Pi * Pi = Pi
  proj_perp     : Pi_perp * Pi_perp = Pi_perp
  completeness  : Pi + Pi_perp = 1
  ortho_pi_perp : Pi * Pi_perp = 0
  ortho_perp_pi : Pi_perp * Pi = 0

/-- A concrete nontrivial complementary-projector model in `M₂(ℚ)`. -/
theorem standardCausalProjectorSystem :
    CausalProjectorSystem
      (Pi := !![(1 : ℚ), 0; 0, 0])
      (Pi_perp := !![(0 : ℚ), 0; 0, 1]) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Both projectors in the standard complementary pair are nonzero, so this
model is genuinely a two-sided decomposition rather than a degenerate one. -/
theorem standardCausalProjectorSystem_projectors_nonzero :
    (!![(1 : ℚ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) ≠ 0 ∧
      (!![(0 : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) ≠ 0 := by
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
    norm_num at h00
  · intro h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 1 1) h
    norm_num at h11

/-! ### Part III: Archetype 𝒜₂ — Causal Pinching Channel & Acausal Annihilation -/

/-- The causal truncation channel: $\mathcal{E}(X) = \Pi X \Pi$. -/
def causalChannel {R : Type*} [Ring R] (Pi : R) (X : R) : R :=
  Pi * X * Pi

/-- The causal channel is an idempotent operator on the ambient ring. -/
theorem causal_channel_idempotent {R : Type*} [Ring R] (Pi : R) (hPi : Pi * Pi = Pi) (X : R) :
    causalChannel Pi (causalChannel Pi X) = causalChannel Pi X := by
  dsimp [causalChannel]
  calc
    Pi * (Pi * X * Pi) * Pi = (Pi * Pi) * X * (Pi * Pi) := by repeat rw [mul_assoc]
    _ = Pi * X * Pi := by rw [hPi]

/-- The causal channel annihilates the acausal projector $\Pi^\perp$. -/
theorem causal_channel_annihilates_acausal {R : Type*} [Ring R] (Pi Pi_perp : R)
    (h_ortho : Pi * Pi_perp = 0) :
    causalChannel Pi Pi_perp = 0 := by
  dsimp [causalChannel]
  rw [h_ortho, zero_mul]

/-- Any operator supported on the causal subspace is invariant under the causal channel. -/
theorem causal_channel_preserves_supported {R : Type*} [Ring R] (Pi : R) (X : R)
    (h_supp : Pi * X * Pi = X) :
    causalChannel Pi X = X :=
  h_supp

/-! ### Part IV: Archetype 𝒜₃ — Petz Intertwiner & Gram Partial Isometry -/

/-- When an operator $P^+$ is supported on the causal subspace, it absorbs the projector. -/
theorem pinv_mul_pi_eq_self {R : Type*} [Ring R] (Pi Pi_perp P_pinv : R)
    (h_comp : Pi + Pi_perp = 1) (h_perp : P_pinv * Pi_perp = 0) :
    P_pinv * Pi = P_pinv := by
  have h1 : P_pinv = P_pinv * 1 := (mul_one P_pinv).symm
  rw [← h_comp] at h1
  rw [mul_add, h_perp, add_zero] at h1
  exact h1.symm

theorem pi_mul_pinv_eq_self {R : Type*} [Ring R] (Pi Pi_perp P_pinv : R)
    (h_comp : Pi + Pi_perp = 1) (h_perp : Pi_perp * P_pinv = 0) :
    Pi * P_pinv = P_pinv := by
  have h1 : P_pinv = 1 * P_pinv := (one_mul P_pinv).symm
  rw [← h_comp] at h1
  rw [add_mul, h_perp, add_zero] at h1
  exact h1.symm

/-- **Theorem**: Gram operator identity:
    The unmasked ambient state $\rho$ evaluates identically to the causal state
    $\rho_{\text{causal}} = \Pi \rho \Pi$ when contracted against the causal pseudoinverse $P^+$:
    $P^+ \rho P^+ = P^+ (\Pi \rho \Pi) P^+$. -/
theorem petz_gram_operator_identity {R : Type*} [Ring R] (Pi Pi_perp P_pinv rho : R)
    (h_comp : Pi + Pi_perp = 1)
    (h_perp_right : P_pinv * Pi_perp = 0)
    (h_perp_left : Pi_perp * P_pinv = 0) :
    P_pinv * rho * P_pinv = P_pinv * (causalChannel Pi rho) * P_pinv := by
  have h_right : P_pinv * Pi = P_pinv := pinv_mul_pi_eq_self Pi Pi_perp P_pinv h_comp h_perp_right
  have h_left : Pi * P_pinv = P_pinv := pi_mul_pinv_eq_self Pi Pi_perp P_pinv h_comp h_perp_left
  dsimp [causalChannel]
  calc
    P_pinv * rho * P_pinv = (P_pinv * Pi) * rho * (Pi * P_pinv) := by rw [h_right, h_left]
    _ = P_pinv * (Pi * rho * Pi) * P_pinv := by repeat rw [mul_assoc]

/-! ### Part V: Archetype 𝒜₄ — Past-Future 2x2 Block Splitting & Transfer Operators -/

variable {R : Type*} [CommRing R]

/-- The $2 \times 2$ block intertwiner $V_i = \begin{pmatrix} K & 0 \\ L & 0 \end{pmatrix}$. -/
def blockIntertwiner (K L : R) : Matrix (Fin 2) (Fin 2) R :=
  !![K, 0; L, 0]

/-- The causal state on the retained past subspace $\sigma_i = \begin{pmatrix} s & 0 \\ 0 & 0 \end{pmatrix}$. -/
def blockCausalState (s : R) : Matrix (Fin 2) (Fin 2) R :=
  !![s, 0; 0, 0]

/-- The Gram operator of the block intertwiner is diagonal, with retained entry $K^2 + L^2$. -/
theorem blockIntertwiner_gram (K L : R) :
    (blockIntertwiner K L)ᵀ * blockIntertwiner K L =
      !![K ^ 2 + L ^ 2, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockIntertwiner, Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- The Gram operator equals the retained-support projection exactly when $K^2 + L^2 = 1$. -/
theorem gram_isometry_iff_stiefel (K L : R) :
    (blockIntertwiner K L)ᵀ * blockIntertwiner K L = !![1, 0; 0, 0] ↔
      K ^ 2 + L ^ 2 = 1 := by
  rw [blockIntertwiner_gram]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simpa using h00
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]

/-- Stiefel zero-sum trade-off: $L^2 = 1 - K^2$. -/
theorem stiefel_tradeoff (K L : R) (h_stiefel : K ^ 2 + L ^ 2 = 1) :
    L ^ 2 = 1 - K ^ 2 := by
  calc
    L ^ 2 = (K ^ 2 + L ^ 2) - K ^ 2 := by ring
    _ = 1 - K ^ 2 := by rw [h_stiefel]

/-- Past normalization forces the future squared weight to vanish. -/
theorem past_normalization_forces_future_zero (K L : R)
    (h_stiefel : K ^ 2 + L ^ 2 = 1) (h_past : K ^ 2 = 1) :
    L ^ 2 = 0 := by
  rw [stiefel_tradeoff K L h_stiefel, h_past, sub_self]

/-! ### Part VI: Archetype 𝒜₅ — Retrocausal Reconstruction Matrix -/

/-- The Petz block reconstruction map $\mathcal{R}_i(\sigma_i) = V_i \sigma_i V_i^\top$. -/
def petzBlockReconstruct (K L s : R) : Matrix (Fin 2) (Fin 2) R :=
  blockIntertwiner K L * blockCausalState s * (blockIntertwiner K L)ᵀ

/-- **Theorem**: Past Restoration ($PP$ block, index $(0, 0)$):
    $[\mathcal{R}_i(\sigma_i)]_{0,0} = s K^2$. -/
theorem petz_block_past (K L s : R) :
    petzBlockReconstruct K L s 0 0 = s * K ^ 2 := by
  dsimp [petzBlockReconstruct, blockIntertwiner, blockCausalState]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Theorem**: Past-Future Coherence Regeneration ($PQ$ block, index $(0, 1)$):
    $[\mathcal{R}_i(\sigma_i)]_{0,1} = s K L$. -/
theorem petz_block_coherence_PQ (K L s : R) :
    petzBlockReconstruct K L s 0 1 = s * K * L := by
  dsimp [petzBlockReconstruct, blockIntertwiner, blockCausalState]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Theorem**: Future-Past Coherence Regeneration ($QP$ block, index $(1, 0)$):
    $[\mathcal{R}_i(\sigma_i)]_{1,0} = s K L$. -/
theorem petz_block_coherence_QP (K L s : R) :
    petzBlockReconstruct K L s 1 0 = s * K * L := by
  dsimp [petzBlockReconstruct, blockIntertwiner, blockCausalState]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Theorem**: Retrocausal Future Synthesis ($QQ$ block, index $(1, 1)$):
    $[\mathcal{R}_i(\sigma_i)]_{1,1} = s L^2$. -/
theorem petz_block_future (K L s : R) :
    petzBlockReconstruct K L s 1 1 = s * L ^ 2 := by
  dsimp [petzBlockReconstruct, blockIntertwiner, blockCausalState]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Full Matrix Representation of the Petz Reconstruction. -/
theorem petz_block_reconstruct_matrix (K L s : R) :
    petzBlockReconstruct K L s = !![s * K ^ 2, s * K * L; s * K * L, s * L ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact petz_block_past K L s
  · exact petz_block_coherence_PQ K L s
  · exact petz_block_coherence_QP K L s
  · exact petz_block_future K L s

/-- The reconstructed trace equals $s(K^2 + L^2)$. -/
theorem petz_block_trace (K L s : R) :
    Matrix.trace (petzBlockReconstruct K L s) = s * (K ^ 2 + L ^ 2) := by
  rw [petz_block_reconstruct_matrix]
  simp [Matrix.trace]
  ring

/-- Trace preservation on input support under the Stiefel condition. -/
theorem petz_block_trace_preservation_on_support (K L s : R)
    (h_stiefel : K ^ 2 + L ^ 2 = 1) :
    Matrix.trace (petzBlockReconstruct K L s) = s := by
  rw [petz_block_trace, h_stiefel, mul_one]

/-- **Coherence Determinant / Cauchy-Schwarz Equality**:
    The product of off-diagonal coherence blocks equals the product of past and future diagonal blocks:
    $[\mathcal{R}]_{0,1} \cdot [\mathcal{R}]_{1,0} = [\mathcal{R}]_{0,0} \cdot [\mathcal{R}]_{1,1}$. -/
theorem petz_block_coherence_cauchy_schwarz (K L s : R) :
    petzBlockReconstruct K L s 0 1 * petzBlockReconstruct K L s 1 0 =
    petzBlockReconstruct K L s 0 0 * petzBlockReconstruct K L s 1 1 := by
  rw [petz_block_coherence_PQ, petz_block_coherence_QP, petz_block_past, petz_block_future]
  ring

/-- Decoupling Limit: When $L = 0$, future and coherences vanish. -/
theorem petz_decoupled_future_zero (K s : R) :
    petzBlockReconstruct K 0 s 1 1 = 0 ∧
    petzBlockReconstruct K 0 s 0 1 = 0 := by
  constructor
  · rw [petz_block_future]; ring
  · rw [petz_block_coherence_PQ]; ring

/-- Exact Past Preservation: When $K^2 = 1$, past is preserved identically. -/
theorem petz_past_exact_preservation (K L s : R) (hK : K ^ 2 = 1) :
    petzBlockReconstruct K L s 0 0 = s := by
  rw [petz_block_past, hK, mul_one]

/-! ### Part VII: Archetype 𝒜₆ — Quantum Markov Sufficiency & Relative Modular Flow -/

/-- Intertwining of the Araki relative modular operator with causal corner compression:
    When the projector $P$ commutes with $\rho$ and $\sigma^{-1}$,
    compression to the causal corner commutes with the relative modular action. -/
theorem relativeModularOperator_intertwines_causal_compression
    {A : Type*} [Ring A] [Algebra R A]
    (rho sigmaInv P : A)
    (hρ : P * rho = rho * P)
    (hσ : P * sigmaInv = sigmaInv * P) :
    (relativeModularOperator (R := R) rho sigmaInv).comp
        (causalCompression (R := R) P) =
      (causalCompression (R := R) P).comp
        (relativeModularOperator (R := R) rho sigmaInv) :=
  relativeModularOperator_commutes_with_causalCompression rho sigmaInv P hρ hσ

/-- Pointwise modular preservation on causal observables:
    $\Delta_{\rho, \sigma}(P X P) = P \Delta_{\rho, \sigma}(X) P$. -/
theorem relativeModularOperator_preserves_causal_observables
    {A : Type*} [Ring A] [Algebra R A]
    (rho sigmaInv P X : A)
    (hρ : P * rho = rho * P)
    (hσ : P * sigmaInv = sigmaInv * P) :
    relativeModularOperator (R := R) rho sigmaInv (P * X * P) =
      P * (rho * X * sigmaInv) * P :=
  relativeModularOperator_causalCompression_apply rho sigmaInv P X hρ hσ

/-! ### Part VIII: Epistemic Deconfabulation Mapping & Quadratic Response -/

/-- Natural morphism from the 5-stage epistemic compiler to the 6-stage causal Petz poset. -/
def deconfabulateMap : Epistemology.Deconfabulation.Archetype → CausalPetzArchetype
  | .primaMateria      => .pastFiltrationProjector
  | .shadowProjection  => .causalPinchingChannel
  | .animusLogos       => .pastFutureBlockSplitting
  | .chiralSyzygy      => .retrocausalReconstruction
  | .selfIndividuation => .markovModularSufficiency

/-- **Theorem**: The deconfabulation mapping is order-preserving (monotone). -/
theorem deconfabulateMap_monotone (a b : Epistemology.Deconfabulation.Archetype) (h : a ≤ b) :
    deconfabulateMap a ≤ deconfabulateMap b := by
  cases a <;> cases b <;> revert h <;> decide

/-- **Quadratic Response Correspondence**:
    In the Stiefel geometry $K^2 + L^2 = 1$, the squared coherence $(K L)^2 = u(1 - u)$
    where $u = K^2$, exactly matches the DeconfabulationModel response $C u - K_0 u^2$
    with $C = 1$ and $K_0 = 1$. -/
theorem stiefel_coherence_is_quadratic_response (u : ℝ) :
    u * (1 - u) = 1 * u - 1 * u ^ 2 := by
  ring

/-- The apex of the Stiefel coherence response occurs at $u^* = 1/2$, yielding
    the maximum activity of $1/4$. -/
theorem stiefel_coherence_optimal_activity :
    optimalCoordinate 1 1 = (1 : ℝ) / 2 ∧
    1 * (optimalCoordinate 1 1) - 1 * (optimalCoordinate 1 1) ^ 2 = (1 : ℝ) / 4 := by
  constructor
  · dsimp [optimalCoordinate]; ring
  · rw [response_at_optimal 1 1 (by norm_num)]
    norm_num

/-! ### Part IX: Master Certificate & Formal Verification -/

/-- Master certificate bundling the verified components of the Causal Petz Deconfabulation Poset. -/
structure CausalPetzDeconfabulationCertificate : Prop where
  poset_root : ∀ a, CausalPetzArchetype.pastFiltrationProjector ≤ a
  poset_strict_chain :
    (CausalPetzArchetype.pastFiltrationProjector < CausalPetzArchetype.causalPinchingChannel) ∧
    (CausalPetzArchetype.causalPinchingChannel < CausalPetzArchetype.petzGramIntertwiner) ∧
    (CausalPetzArchetype.petzGramIntertwiner < CausalPetzArchetype.pastFutureBlockSplitting) ∧
    (CausalPetzArchetype.pastFutureBlockSplitting < CausalPetzArchetype.retrocausalReconstruction) ∧
    (CausalPetzArchetype.retrocausalReconstruction < CausalPetzArchetype.markovModularSufficiency)
  triangular_rank : ∀ (N : ℕ), 2 * (∑ i ∈ Finset.range N, (i + 1)) = N * (N + 1)
  causal_channel_idempotent : ∀ {R : Type*} [Ring R] (Pi : R) (h : Pi * Pi = Pi) (X : R),
    causalChannel Pi (causalChannel Pi X) = causalChannel Pi X
  causal_channel_annihilates_acausal : ∀ {R : Type*} [Ring R] (Pi Pi_perp : R) (h : Pi * Pi_perp = 0),
    causalChannel Pi Pi_perp = 0
  petz_gram_isometry : ∀ {R : Type*} [Ring R] (Pi Pi_perp P_pinv rho : R)
    (h_comp : Pi + Pi_perp = 1) (h_r : P_pinv * Pi_perp = 0) (h_l : Pi_perp * P_pinv = 0),
    P_pinv * rho * P_pinv = P_pinv * (causalChannel Pi rho) * P_pinv
  gram_stiefel_constraint : ∀ {R : Type*} [CommRing R] (K L : R),
    ((blockIntertwiner K L)ᵀ * blockIntertwiner K L = !![1, 0; 0, 0] ↔
      K ^ 2 + L ^ 2 = 1)
  stiefel_tradeoff : ∀ {R : Type*} [CommRing R] (K L : R),
    K ^ 2 + L ^ 2 = 1 → L ^ 2 = 1 - K ^ 2
  past_normalization_forces_future_zero : ∀ {R : Type*} [CommRing R] (K L : R),
    K ^ 2 + L ^ 2 = 1 → K ^ 2 = 1 → L ^ 2 = 0
  past_restoration : ∀ {R : Type*} [CommRing R] (K L s : R),
    petzBlockReconstruct K L s 0 0 = s * K ^ 2
  coherence_PQ : ∀ {R : Type*} [CommRing R] (K L s : R),
    petzBlockReconstruct K L s 0 1 = s * K * L
  coherence_QP : ∀ {R : Type*} [CommRing R] (K L s : R),
    petzBlockReconstruct K L s 1 0 = s * K * L
  future_synthesis : ∀ {R : Type*} [CommRing R] (K L s : R),
    petzBlockReconstruct K L s 1 1 = s * L ^ 2
  coherence_cauchy_schwarz : ∀ {R : Type*} [CommRing R] (K L s : R),
    petzBlockReconstruct K L s 0 1 * petzBlockReconstruct K L s 1 0 =
    petzBlockReconstruct K L s 0 0 * petzBlockReconstruct K L s 1 1
  supported_trace_preservation : ∀ {R : Type*} [CommRing R] (K L s : R),
    K ^ 2 + L ^ 2 = 1 → Matrix.trace (petzBlockReconstruct K L s) = s
  deconfabulation_monotone : ∀ (a b : Epistemology.Deconfabulation.Archetype),
    a ≤ b → deconfabulateMap a ≤ deconfabulateMap b
  stiefel_quadratic_response : ∀ (u : ℝ), u * (1 - u) = 1 * u - 1 * u ^ 2
  stiefel_optimal_activity : optimalCoordinate 1 1 = (1 : ℝ) / 2 ∧
    1 * (optimalCoordinate 1 1) - 1 * (optimalCoordinate 1 1) ^ 2 = (1 : ℝ) / 4

/-- Instant certification of the master certificate with zero open assumptions. -/
theorem compile_causal_petz_deconfabulation : CausalPetzDeconfabulationCertificate where
  poset_root := a1_precedes_all
  poset_strict_chain := strict_causal_chain
  triangular_rank := triangular_rank_formula
  causal_channel_idempotent := fun Pi h X => causal_channel_idempotent Pi h X
  causal_channel_annihilates_acausal := fun Pi Pi_perp h => causal_channel_annihilates_acausal Pi Pi_perp h
  petz_gram_isometry := fun Pi Pi_perp P_pinv rho h_c h_r h_l =>
    petz_gram_operator_identity Pi Pi_perp P_pinv rho h_c h_r h_l
  gram_stiefel_constraint := gram_isometry_iff_stiefel
  stiefel_tradeoff := stiefel_tradeoff
  past_normalization_forces_future_zero := past_normalization_forces_future_zero
  past_restoration := petz_block_past
  coherence_PQ := petz_block_coherence_PQ
  coherence_QP := petz_block_coherence_QP
  future_synthesis := petz_block_future
  coherence_cauchy_schwarz := petz_block_coherence_cauchy_schwarz
  supported_trace_preservation := petz_block_trace_preservation_on_support
  deconfabulation_monotone := deconfabulateMap_monotone
  stiefel_quadratic_response := stiefel_coherence_is_quadratic_response
  stiefel_optimal_activity := stiefel_coherence_optimal_activity

end InfoGeometry.QuantumContext.CausalPetzDeconfabulationPoset
