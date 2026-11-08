import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Sandbox finite algebraic causal truncation

This file proves finite ring and matrix identities for an idempotent
compression and an explicit `2 × 2` reconstruction model. Its exact recovery
statement is limited to the case where the past coefficient squares to one
and the future coefficient is zero. It does not formalize general Petz
sufficiency or modular flow.
-/

namespace InfoGeometry.Experimental.CausalPetz

open scoped Matrix BigOperators

/-! ### Section 1: Kinematics of Causal Truncation -/

/-- **Theorem**: The triangular rank identity:
    $\operatorname{rank}(\Pi) = \sum_{i=1}^N i = \frac{N(N+1)}{2}$.
    Formulated over $\mathbb{N}$ without division: $2 \sum_{i=0}^{N-1} (i + 1) = N(N + 1)$. -/
theorem triangular_rank_formula (N : ℕ) :
    2 * (∑ i ∈ Finset.range N, (i + 1)) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- An algebraic causal projector system with complementary acausal projector. -/
structure CausalProjectorSystem {R : Type*} [Ring R] (Pi Pi_perp : R) : Prop where
  proj_pi      : Pi * Pi = Pi
  proj_perp    : Pi_perp * Pi_perp = Pi_perp
  completeness : Pi + Pi_perp = 1
  ortho_pi_perp: Pi * Pi_perp = 0
  ortho_perp_pi: Pi_perp * Pi = 0

/-- A concrete nontrivial complementary-projector model in the real `2 × 2`
matrix algebra. -/
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

/-- The causal truncation channel: $\mathcal{E}(X) = \Pi X \Pi$. -/
def causalChannel {R : Type*} [Ring R] (Pi : R) (X : R) : R :=
  Pi * X * Pi

/-- The causal channel is an idempotent operator on the ambient ring. -/
theorem causal_channel_idempotent {R : Type*} [Ring R] (Pi : R) (hPi : Pi * Pi = Pi) (X : R) :
    causalChannel Pi (causalChannel Pi X) = causalChannel Pi X := by
  dsimp [causalChannel]
  calc
    Pi * (Pi * X * Pi) * Pi = (Pi * Pi) * X * (Pi * Pi) := by
      repeat rw [mul_assoc]
    _ = Pi * X * Pi := by rw [hPi]

/-- The causal channel annihilates the strictly upper-triangular acausal projector $\Pi^\perp$. -/
theorem causal_channel_annihilates_acausal {R : Type*} [Ring R] (Pi Pi_perp : R)
    (h_ortho : Pi * Pi_perp = 0) :
    causalChannel Pi Pi_perp = 0 := by
  dsimp [causalChannel]
  rw [h_ortho, zero_mul]

/-- The causal state $\rho_{\text{causal}} = \mathcal{E}(\rho)$ is supported strictly on $\Pi$. -/
theorem causal_state_supported_on_pi {R : Type*} [Ring R] (Pi : R) (hPi : Pi * Pi = Pi) (rho : R) :
    Pi * (causalChannel Pi rho) * Pi = causalChannel Pi rho :=
  causal_channel_idempotent Pi hPi rho

/-! ### Section 2: The Petz Intertwiner & Gram Partial Isometry -/

/-- When an operator $P^+$ is supported on the causal subspace ($\Pi P^+ = P^+$ and $P^+ \Pi^\perp = 0$),
    it absorbs the causal projector: $P^+ \Pi = P^+$. -/
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
    _ = P_pinv * (Pi * rho * Pi) * P_pinv := by
      repeat rw [mul_assoc]

/-! ### Section 3: Past-Future 2x2 Block Splitting & Transfer Operators -/

variable {R : Type*} [CommRing R]

/-- The two off-diagonal matrix units do not commute in the real `2 × 2`
operator algebra. -/
def matrixUnit01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def matrixUnit10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

theorem matrix_units_noncommutative :
    matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The $2 \times 2$ block intertwiner $V_i = \begin{pmatrix} K & 0 \\ L & 0 \end{pmatrix}$. -/
def blockIntertwiner (K L : R) : Matrix (Fin 2) (Fin 2) R :=
  !![K, 0; L, 0]

/-- The causal state on the retained past subspace $\sigma_i = \begin{pmatrix} s & 0 \\ 0 & 0 \end{pmatrix}$. -/
def blockCausalState (s : R) : Matrix (Fin 2) (Fin 2) R :=
  !![s, 0; 0, 0]

/-- The Petz block reconstruction map $\mathcal{R}_i(\sigma_i) = V_i \sigma_i V_i^\top$. -/
def petzBlockReconstruct (K L s : R) : Matrix (Fin 2) (Fin 2) R :=
  blockIntertwiner K L * blockCausalState s * (blockIntertwiner K L)ᵀ

/-- **Theorem**: Past Restoration ($PP$ block, index $(0, 0)$):
    The $(0, 0)$ block reconstructs the past state modulated by $K^2$:
    $[\mathcal{R}_i(\sigma_i)]_{0,0} = s K^2$. -/
theorem petz_block_past (K L s : R) :
    petzBlockReconstruct K L s 0 0 = s * K ^ 2 := by
  dsimp [petzBlockReconstruct, blockIntertwiner, blockCausalState]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Theorem**: Past-Future Coherence Regeneration ($PQ$ block, index $(0, 1)$):
    The $(0, 1)$ block repopulates quantum coherence between past and future:
    $[\mathcal{R}_i(\sigma_i)]_{0,1} = s K L$. -/
theorem petz_block_coherence_PQ (K L s : R) :
    petzBlockReconstruct K L s 0 1 = s * K * L := by
  dsimp [petzBlockReconstruct, blockIntertwiner, blockCausalState]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Theorem**: Future-Past Coherence Regeneration ($QP$ block, index $(1, 0)$):
    The $(1, 0)$ block matches the adjoint coherence:
    $[\mathcal{R}_i(\sigma_i)]_{1,0} = s K L$. -/
theorem petz_block_coherence_QP (K L s : R) :
    petzBlockReconstruct K L s 1 0 = s * K * L := by
  dsimp [petzBlockReconstruct, blockIntertwiner, blockCausalState]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Theorem**: Retrocausal Future Synthesis ($QQ$ block, index $(1, 1)$):
    The $(1, 1)$ block extrapolates a non-zero state on the evicted future tokens:
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

/-! ### Section 4: Decoupling Limits & Retrocausal Generation -/

/-- **Theorem**: Product State / Decoupling Limit:
    When the future transfer operator vanishes ($L = 0$),
    both the reconstructed future and coherence vanish identically. -/
theorem petz_decoupled_future_zero (K s : R) :
    petzBlockReconstruct K 0 s 1 1 = 0 ∧
    petzBlockReconstruct K 0 s 0 1 = 0 := by
  constructor
  · rw [petz_block_future]
    ring
  · rw [petz_block_coherence_PQ]
    ring

/-- **Theorem**: Exact Past Preservation:
    When the past transfer operator is normalized ($K^2 = 1$),
    the visible past state is preserved identically: $[\mathcal{R}_i(\sigma_i)]_{0,0} = s$. -/
theorem petz_past_exact_preservation (K L s : R) (hK : K ^ 2 = 1) :
    petzBlockReconstruct K L s 0 0 = s := by
  rw [petz_block_past, hK, mul_one]

/-- **Theorem**: Future State Non-Vanishing:
    If the future transfer operator $L \ne 0$ and the past state $s \ne 0$ in an integral domain,
    the Petz map generates a non-zero future state. -/
theorem petz_future_nonvanishing {F : Type*} [Field F] (K L s : F)
    (hs : s ≠ 0) (hL : L ≠ 0) :
    petzBlockReconstruct K L s 1 1 ≠ 0 := by
  rw [petz_block_future]
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
  exact mul_ne_zero hs hL2

/-! ### Section 5: Exact recovery in the finite block model -/

/-- With normalized past transfer and zero future transfer, the concrete
block reconstruction recovers exactly the retained causal state. -/
theorem petz_reconstructs_reference (K s : R) (hK : K ^ 2 = 1) :
    petzBlockReconstruct K 0 s = blockCausalState s := by
  rw [petz_block_reconstruct_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockCausalState, hK]

/-! ### Section 6: Master Verification Certificate -/

/-- Master certificate bundling the proved stages of Causal Petz Recovery with genuine Prop fields. -/
structure CausalPetzRecoveryCertificate where
  triangular_rank : ∀ (N : ℕ), 2 * (∑ i ∈ Finset.range N, (i + 1)) = N * (N + 1)
  causal_pinching_annihilates_acausal : ∀ {R : Type*} [Ring R] (Pi Pi_perp : R) (h : Pi * Pi_perp = 0),
    causalChannel Pi Pi_perp = 0
  petz_gram_isometry : ∀ {R : Type*} [Ring R] (Pi Pi_perp P_pinv rho : R)
    (h_comp : Pi + Pi_perp = 1) (h_r : P_pinv * Pi_perp = 0) (h_l : Pi_perp * P_pinv = 0),
    P_pinv * rho * P_pinv = P_pinv * (causalChannel Pi rho) * P_pinv
  past_restoration : ∀ {R : Type*} [CommRing R] (K L s : R),
    petzBlockReconstruct K L s 0 0 = s * K ^ 2
  coherence_regeneration_PQ : ∀ {R : Type*} [CommRing R] (K L s : R),
    petzBlockReconstruct K L s 0 1 = s * K * L
  coherence_regeneration_QP : ∀ {R : Type*} [CommRing R] (K L s : R),
    petzBlockReconstruct K L s 1 0 = s * K * L
  future_synthesis : ∀ {R : Type*} [CommRing R] (K L s : R),
    petzBlockReconstruct K L s 1 1 = s * L ^ 2
  decoupling_limit : ∀ {R : Type*} [CommRing R] (K s : R),
    petzBlockReconstruct K 0 s 1 1 = 0 ∧ petzBlockReconstruct K 0 s 0 1 = 0

/-- Instantiation of the master certificate with zero open assumptions. -/
theorem compile_causal_petz_recovery : CausalPetzRecoveryCertificate :=
  { triangular_rank := triangular_rank_formula
    causal_pinching_annihilates_acausal := fun Pi Pi_perp h => causal_channel_annihilates_acausal Pi Pi_perp h
    petz_gram_isometry := fun Pi Pi_perp P_pinv rho h_comp h_r h_l =>
      petz_gram_operator_identity Pi Pi_perp P_pinv rho h_comp h_r h_l
    past_restoration := petz_block_past
    coherence_regeneration_PQ := petz_block_coherence_PQ
    coherence_regeneration_QP := petz_block_coherence_QP
    future_synthesis := petz_block_future
    decoupling_limit := petz_decoupled_future_zero }

end InfoGeometry.Experimental.CausalPetz
