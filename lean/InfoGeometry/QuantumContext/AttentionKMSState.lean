/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InfoGeometry.QuantumContext.MatrixGNS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Softmax Attention as a KMS Thermal State and GNS Representation

This module formalizes the algebraic operator-theoretic characterization of softmax attention
in Transformers as a finite-dimensional Kubo–Martin–Schwinger (KMS) thermal state:

1. **Thermal Density Matrix & Softmax Weights**:
   - For any finite token context $\iota$, query logit vector, and inverse temperature $\beta > 0$,
     the softmax weights $\rho_i = \frac{\exp(\beta \cdot \text{logits } i)}{\sum_j \exp(\beta \cdot \text{logits } j)}$
     form a normalized probability distribution strictly in the interior ($\rho_i > 0$).
   - The attention density operator $\rho_{\text{att}} = \text{diag}(\rho_i)$ has unit trace: $\operatorname{Tr}(\rho_{\text{att}}) = 1$.

2. **The Attention GNS State Functional & Separating Property**:
   - The linear state functional $\omega_{\text{att}}(A) = \operatorname{Tr}(\rho_{\text{att}} A) = \sum_i \rho_i A_{ii}$.
   - Proved that the state is **strictly faithful**: $\omega_{\text{att}}(B^T B) = 0 \iff B = 0$.
   - In GNS theory, faithfulness is equivalent to the context vector $|\Omega_{\text{cache}}\rangle$
     being a **separating vector** for the observable algebra, proving the absence of algebraic null directions.

3. **Finite KMS Condition**:
   - The modular group action $\sigma(B) = \rho B \rho^{-1}$ satisfies the cyclic KMS thermal condition:
     $$\operatorname{Tr}(\rho A (\rho B \rho^{-1})) = \operatorname{Tr}(\rho B A)$$
     for all observables $A, B$, formalizing attention as a thermal equilibrium state.

4. **Tomita Modular Conjugation**:
   - The modular conjugation $J(A) = A^T$ satisfies $J^2 = \text{id}$ and $J(A B) = J(B) J(A)$,
     reflecting the query generation channel onto the key/value commutant algebra.

5. **Thermodynamics of Context Eviction & Attention Sinks**:
   - Pruning/evicting tokens ($\rho_{i_0} = 0$) produces a non-trivial null ideal $\mathcal{N}_\omega \ne \{0\}$,
     destroying the separating property (irreversible semantic amnesia).
   - Preserving an **attention sink** (token 0 with $\rho_0 > 0$) guarantees that the state remains
     faithful on the anchor subspace, preventing total collapse of the GNS vacuum.

6. **Master Integration Certificate**:
   - Bundles all verified theorems into `AttentionKMSStateCertificate`.
-/

namespace InfoGeometry.QuantumContext.AttentionKMSState

open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### 1. Softmax Thermal Weights and Density Matrix -/

/-- Softmax thermal weight: $\rho_i = \exp(\beta \cdot \text{logits } i) / \sum_j \exp(\beta \cdot \text{logits } j)$. -/
noncomputable def softmaxWeight (logits : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (β * logits i) / ∑ j, Real.exp (β * logits j)

/-- Theorem: Softmax weights are strictly positive for all historical context tokens. -/
theorem softmaxWeight_pos [Nonempty ι] (logits : ι → ℝ) (β : ℝ) (i : ι) :
    0 < softmaxWeight logits β i := by
  dsimp [softmaxWeight]
  have h_num : 0 < Real.exp (β * logits i) := Real.exp_pos _
  have h_den : 0 < ∑ j, Real.exp (β * logits j) := by
    apply Finset.sum_pos'
    · intro j _
      exact le_of_lt (Real.exp_pos _)
    · exact ⟨Classical.arbitrary ι, Finset.mem_univ _, Real.exp_pos _⟩
  exact div_pos h_num h_den

/-- Theorem: Softmax weights sum to 1. -/
theorem softmaxWeight_sum_one [Nonempty ι] (logits : ι → ℝ) (β : ℝ) :
    ∑ i, softmaxWeight logits β i = 1 := by
  dsimp [softmaxWeight]
  have h_den_pos : 0 < ∑ j, Real.exp (β * logits j) := by
    apply Finset.sum_pos'
    · intro j _
      exact le_of_lt (Real.exp_pos _)
    · exact ⟨Classical.arbitrary ι, Finset.mem_univ _, Real.exp_pos _⟩
  have h_den_ne : (∑ j, Real.exp (β * logits j)) ≠ 0 := ne_of_gt h_den_pos
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [← div_eq_mul_inv]
  exact div_self h_den_ne

/-- The diagonal attention density matrix $\rho_{\text{att}} = \text{diag}(\rho_i)$. -/
noncomputable def attentionDensityMatrix (logits : ι → ℝ) (β : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => softmaxWeight logits β i)

/-- Theorem: The attention density matrix has unit trace: $\operatorname{Tr}(\rho_{\text{att}}) = 1$. -/
theorem attentionDensityMatrix_trace_one [Nonempty ι] (logits : ι → ℝ) (β : ℝ) :
    Matrix.trace (attentionDensityMatrix logits β) = 1 := by
  dsimp [attentionDensityMatrix]
  rw [Matrix.trace_diagonal]
  exact softmaxWeight_sum_one logits β

/-! ### 2. The GNS State Functional and Separating Property -/

/-- The attention GNS state functional: $\omega_{\text{att}}(A) = \operatorname{Tr}(\rho_{\text{att}} A)$. -/
noncomputable def attentionState (logits : ι → ℝ) (β : ℝ) (A : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (attentionDensityMatrix logits β * A)

/-- Theorem: The attention state evaluates to the weighted diagonal sum $\sum_i \rho_i A_{ii}$. -/
theorem attentionState_eq_sum (logits : ι → ℝ) (β : ℝ) (A : Matrix ι ι ℝ) :
    attentionState logits β A = ∑ i, softmaxWeight logits β i * A i i := by
  dsimp [attentionState, attentionDensityMatrix, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
  · intro j _ hj
    have h_ne : i ≠ j := hj.symm
    simp only [h_ne, ite_false, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ _))

/-- Theorem: Quadratic evaluation $\omega_{\text{att}}(B^T B) = \sum_i \rho_i \sum_j (B_{ji})^2$. -/
theorem attentionState_quadratic_eq_sum (logits : ι → ℝ) (β : ℝ) (B : Matrix ι ι ℝ) :
    attentionState logits β (B.transpose * B) =
    ∑ i, softmaxWeight logits β i * (∑ j, (B j i) ^ 2) := by
  rw [attentionState_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  dsimp [Matrix.transpose, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Theorem: Non-negativity of the attention state on positive operators: $0 \le \omega(B^T B)$. -/
theorem attentionState_quadratic_nonneg [Nonempty ι] (logits : ι → ℝ) (β : ℝ) (B : Matrix ι ι ℝ) :
    0 ≤ attentionState logits β (B.transpose * B) := by
  rw [attentionState_quadratic_eq_sum]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (le_of_lt (softmaxWeight_pos logits β i))
  apply Finset.sum_nonneg
  intro j _
  exact sq_nonneg (B j i)

/--
  **The Separating Property (No Semantic Blind Spots)**:
  Because $\rho_i > 0$ for all tokens in the context, the attention state is strictly faithful:
  $$\omega_{\text{att}}(B^T B) = 0 \iff B = 0$$
  In the GNS representation, this proves that $|\Omega_{\text{cache}}\rangle$ is a strictly
  separating vector: $\pi(B) |\Omega_{\text{cache}}\rangle = 0 \implies B = 0$.
-/
theorem attentionState_faithful [Nonempty ι] (logits : ι → ℝ) (β : ℝ) (B : Matrix ι ι ℝ) :
    attentionState logits β (B.transpose * B) = 0 ↔ B = 0 := by
  constructor
  · intro h
    rw [attentionState_quadratic_eq_sum] at h
    have h_nonneg_terms : ∀ i, 0 ≤ softmaxWeight logits β i * ∑ j, (B j i) ^ 2 := by
      intro i
      apply mul_nonneg (le_of_lt (softmaxWeight_pos logits β i))
      apply Finset.sum_nonneg
      intro j _
      exact sq_nonneg (B j i)
    have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h_nonneg_terms i)).mp h
    ext j i
    have h_i := h_all_zero i (Finset.mem_univ i)
    have h_rho_pos := softmaxWeight_pos logits β i
    have h_sum_sq_zero : ∑ j, (B j i) ^ 2 = 0 := by
      cases mul_eq_zero.mp h_i with
      | inl h_contra => linarith
      | inr h_zero => exact h_zero
    have h_sq_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (B j i))).mp h_sum_sq_zero
    have h_bji_sq := h_sq_zero j (Finset.mem_univ j)
    simp only [Matrix.zero_apply]
    exact sq_eq_zero_iff.mp h_bji_sq
  · intro h
    rw [h]
    simp only [Matrix.transpose_zero, mul_zero]
    dsimp [attentionState]
    rw [mul_zero, Matrix.trace_zero]

/-! ### 3. The Finite KMS Thermal Condition -/

/--
  **Finite KMS Commutation Condition**:
  Under modular automorphism conjugation $\sigma(B) = \rho B \rho^{-1}$, the cyclic trace identity
  $$\operatorname{Tr}(\rho A (\rho B \rho^{-1})) = \operatorname{Tr}(\rho B A)$$
  holds identically, establishing that softmax attention is in KMS thermal equilibrium.
-/
theorem attention_kms_condition
    (rho rho_inv A B : Matrix ι ι ℝ)
    (h_inv : rho_inv * rho = 1) :
    Matrix.trace (rho * A * (rho * B * rho_inv)) = Matrix.trace (rho * B * A) := by
  calc
    Matrix.trace (rho * A * (rho * B * rho_inv))
      = Matrix.trace ((rho * A * rho * B) * rho_inv) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (rho_inv * (rho * A * rho * B)) := by
        rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((rho_inv * rho) * (A * rho * B)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (1 * (A * rho * B)) := by rw [h_inv]
    _ = Matrix.trace (A * (rho * B)) := by
        rw [Matrix.one_mul, Matrix.mul_assoc]
    _ = Matrix.trace ((rho * B) * A) := by
        rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (rho * B * A) := by
        simp only [Matrix.mul_assoc]

/-- Explicit inverse of the diagonal attention density matrix. -/
noncomputable def attentionDensityMatrixInv (logits : ι → ℝ) (β : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (softmaxWeight logits β i)⁻¹)

/-- The diagonal inverse is a two-sided inverse of the attention density matrix. -/
theorem attentionDensityMatrixInv_mul [Nonempty ι] (logits : ι → ℝ) (β : ℝ) :
    attentionDensityMatrixInv logits β * attentionDensityMatrix logits β = 1 := by
  dsimp [attentionDensityMatrixInv, attentionDensityMatrix]
  rw [Matrix.diagonal_mul_diagonal]
  have h_id : (fun i => (softmaxWeight logits β i)⁻¹ * softmaxWeight logits β i) = fun _ => 1 := by
    ext i
    exact inv_mul_cancel₀ (ne_of_gt (softmaxWeight_pos logits β i))
  rw [h_id]
  exact Matrix.diagonal_one

/--
  The finite KMS thermal condition specialized to the Attention GNS state:
  $$\omega_{\text{att}}(A \cdot \sigma(B)) = \omega_{\text{att}}(B \cdot A)$$
  where $\sigma(B) = \rho_{\text{att}} B \rho_{\text{att}}^{-1}$ is the modular automorphism.
-/
theorem attentionState_kms [Nonempty ι] (logits : ι → ℝ) (β : ℝ) (A B : Matrix ι ι ℝ) :
    attentionState logits β (A * (attentionDensityMatrix logits β * B * attentionDensityMatrixInv logits β)) =
    attentionState logits β (B * A) := by
  dsimp [attentionState]
  rw [← Matrix.mul_assoc (attentionDensityMatrix logits β) A]
  rw [← Matrix.mul_assoc (attentionDensityMatrix logits β) B A]
  exact attention_kms_condition (attentionDensityMatrix logits β) (attentionDensityMatrixInv logits β)
    A B (attentionDensityMatrixInv_mul logits β)

/-! ### 4. Tomita Modular Conjugation -/

/--
  Canonical tracial anti-automorphism (transposition): $J(A) = A^T$.
  In Tomita–Takesaki modular theory for $M_n(\mathbb{R})$, $J(A) = A^T$ coincides
  with the full modular conjugation $J_\rho(X) = \rho^{1/2} X^T \rho^{-1/2}$ in the
  tracial / infinite-temperature limit ($\beta \to 0$, $\rho = \frac{1}{n} I$).
-/
def modularConjugation (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  A.transpose

/-- Involutive property of modular conjugation: $J^2 = \text{id}$. -/
theorem modularConjugation_involutive (A : Matrix ι ι ℝ) :
    modularConjugation (modularConjugation A) = A :=
  Matrix.transpose_transpose A

/-- Anti-automorphism property of modular conjugation: $J(A B) = J(B) J(A)$. -/
theorem modularConjugation_mul (A B : Matrix ι ι ℝ) :
    modularConjugation (A * B) = modularConjugation B * modularConjugation A :=
  Matrix.transpose_mul A B

/-- Identity preservation: $J(1) = 1$. -/
theorem modularConjugation_one :
    modularConjugation (1 : Matrix ι ι ℝ) = 1 :=
  Matrix.transpose_one

/-! ### 5. Context Eviction, GNS Left Ideals, and Attention Sinks -/

/-- A pruned attention weight vector with zero support on evicted tokens. -/
structure PrunedWeights (ι : Type*) [Fintype ι] where
  weights : ι → ℝ
  nonneg : ∀ i, 0 ≤ weights i
  sum_one : ∑ i, weights i = 1
  evicted : ∃ i₀, weights i₀ = 0

/-- Linear functional associated with pruned context weights. -/
noncomputable def prunedState (pw : PrunedWeights ι) (A : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (Matrix.diagonal pw.weights * A)

/-! ### 5a. Transport of the pruned state to the finite-matrix GNS owner -/

/-- The quadratic evaluation of `prunedState` is the GNS quadratic form for its
diagonal density matrix. -/
theorem prunedState_quadratic_eq_gnsInner
    (pw : PrunedWeights ι) (A : Matrix ι ι ℝ) :
    prunedState pw (A.transpose * A) =
      InfoGeometry.QuantumContext.MatrixGNS.gnsInner
        (Matrix.diagonal pw.weights) A A := by
  dsimp [prunedState]
  rw [InfoGeometry.QuantumContext.MatrixGNS.gnsInner_eq_trace]

/-- A pruned-state null vector has exactly the columns in the positive-weight
support equal to zero. This transports the support characterization from the
generic diagonal-matrix GNS construction. -/
theorem prunedState_null_iff_active_columns_zero
    (pw : PrunedWeights ι) (A : Matrix ι ι ℝ) :
    prunedState pw (A.transpose * A) = 0 ↔
      ∀ i, 0 < pw.weights i → ∀ j, A j i = 0 := by
  rw [prunedState_quadratic_eq_gnsInner]
  simpa [InfoGeometry.QuantumContext.MatrixGNS.gnsLeftIdeal] using
    (InfoGeometry.QuantumContext.MatrixGNS.gnsLeftIdeal_diagonal_iff
      pw.weights pw.nonneg A)

/-- The active indices of a pruned state are exactly the indices with
strictly positive weight. -/
noncomputable def prunedActiveSupport (pw : PrunedWeights ι) : Finset ι :=
  Finset.univ.filter fun i => 0 < pw.weights i

/-- Orthogonal coordinate projection onto the active support of a pruned
state. -/
noncomputable def prunedActiveSupportProjector (pw : PrunedWeights ι) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i => if i ∈ prunedActiveSupport pw then (1 : ℝ) else 0

/-- The GNS null ideal is precisely the right annihilator of the active-support
projection. Thus the complementary support projection is not itself the ideal:
the ideal consists of all matrices whose active columns vanish. -/
theorem prunedState_null_iff_right_support_annihilation
    (pw : PrunedWeights ι) (A : Matrix ι ι ℝ) :
    prunedState pw (A.transpose * A) = 0 ↔
      A * prunedActiveSupportProjector pw = 0 := by
  rw [prunedState_null_iff_active_columns_zero]
  constructor
  · intro h
    ext j i
    change (A * Matrix.diagonal
      (fun k => if k ∈ prunedActiveSupport pw then (1 : ℝ) else 0)) j i = 0
    rw [Matrix.mul_diagonal]
    by_cases hi : i ∈ prunedActiveSupport pw
    · have hcol : 0 < pw.weights i := (Finset.mem_filter.mp hi).2
      simp [hi, h i hcol j]
    · simp [hi]
  · intro h i hi j
    have h_entry := congrArg (fun M : Matrix ι ι ℝ => M j i) h
    have hi' : i ∈ prunedActiveSupport pw :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    change (A * Matrix.diagonal
      (fun k => if k ∈ prunedActiveSupport pw then (1 : ℝ) else 0)) j i = 0 at h_entry
    rw [Matrix.mul_diagonal] at h_entry
    simpa [hi'] using h_entry

/-- The null space of a pruned state is closed under left multiplication,
transporting the finite-matrix GNS left-ideal theorem to the attention owner. -/
theorem prunedState_null_mul_left
    (pw : PrunedWeights ι) (A X : Matrix ι ι ℝ)
    (hA : prunedState pw (A.transpose * A) = 0) :
    prunedState pw ((X * A).transpose * (X * A)) = 0 := by
  rw [prunedState_quadratic_eq_gnsInner] at hA ⊢
  exact InfoGeometry.QuantumContext.MatrixGNS.gnsLeftIdeal_mul_left
    pw.weights pw.nonneg A X hA

/-- Diagonal evaluation for pruned state. -/
theorem prunedState_diagonal (pw : PrunedWeights ι) (f : ι → ℝ) :
    prunedState pw (Matrix.diagonal f) = ∑ i, pw.weights i * f i := by
  dsimp [prunedState]
  rw [Matrix.diagonal_mul_diagonal]
  rw [Matrix.trace_diagonal]

/-- Elementary projection matrix onto a single token index: $P = \text{diag}(\delta_{i, i_0})$. -/
def projectionMatrix (i₀ : ι) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => if i = i₀ then (1 : ℝ) else 0)

/-- $P \ne 0$ for any token index. -/
theorem projectionMatrix_ne_zero (i₀ : ι) :
    projectionMatrix i₀ ≠ 0 := by
  intro h
  have h_eval := congr_fun (congr_fun h i₀) i₀
  dsimp [projectionMatrix] at h_eval
  simp only [Matrix.diagonal_apply_eq, ite_true] at h_eval
  norm_num at h_eval

/-- $P$ is symmetric: $P^T = P$. -/
theorem projectionMatrix_transpose (i₀ : ι) :
    (projectionMatrix i₀).transpose = projectionMatrix i₀ := by
  dsimp [projectionMatrix]
  exact Matrix.diagonal_transpose (fun i => if i = i₀ then (1 : ℝ) else 0)

/-- $P$ is idempotent: $P^2 = P$. -/
theorem projectionMatrix_mul_self (i₀ : ι) :
    projectionMatrix i₀ * projectionMatrix i₀ = projectionMatrix i₀ := by
  dsimp [projectionMatrix]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> ring

/--
  **Eviction Creates a Non-Trivial GNS Left Ideal (Left Kernel)**:
  When a token $i_0$ is evicted from the cache ($\rho_{i_0} = 0$), the elementary projection
  $E = P_{i_0} \ne 0$ satisfies $\omega(E^T E) = 0$.
  The state ceases to be faithful, and the context vector $|\Omega_{\text{cache}}\rangle$
  loses its separating property, resulting in irreversible semantic amnesia.
  Note: As $M_n(\mathbb{R})$ is a simple ring with no non-trivial two-sided ideals,
  the subspace $\mathcal{N}_\omega = \{A \in M_n(\mathbb{R}) \mid \omega(A^T A) = 0\}$
  is a GNS left ideal (left kernel).
-/
theorem pruned_cache_has_nontrivial_null_ideal (pw : PrunedWeights ι) :
    ∃ E : Matrix ι ι ℝ, E ≠ 0 ∧ prunedState pw (E.transpose * E) = 0 := by
  rcases pw.evicted with ⟨i₀, hi₀⟩
  use projectionMatrix i₀
  constructor
  · exact projectionMatrix_ne_zero i₀
  · rw [projectionMatrix_transpose, projectionMatrix_mul_self]
    dsimp [projectionMatrix]
    rw [prunedState_diagonal]
    have h_terms : (∑ i, pw.weights i * (if i = i₀ then (1 : ℝ) else 0)) =
        (∑ i, if i = i₀ then pw.weights i₀ else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h_i
      · rw [h_i, mul_one]
      · rw [mul_zero]
    rw [h_terms, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, hi₀]

/--
  **The Attention Sink Anchor**:
  If token `anchor` is protected with non-zero weight ($\rho_{\text{anchor}} > 0$), then any operator $A$
  acting non-trivially on the anchor column (i.e. $\exists j, A_{j,\text{anchor}} \ne 0$) satisfies $\omega(A^T A) > 0$.
  Preserving the initial anchor token keeps the state faithful on the anchor column subspace.
-/
theorem sink_anchor_separating (pw : PrunedWeights ι) (anchor : ι) (h_anchor : 0 < pw.weights anchor)
    (A : Matrix ι ι ℝ) (j : ι) (h_nz : A j anchor ≠ 0) :
    0 < prunedState pw (A.transpose * A) := by
  dsimp [prunedState, Matrix.trace]
  have h_diag : (Matrix.diagonal pw.weights * (A.transpose * A)) anchor anchor =
      pw.weights anchor * (∑ k, (A k anchor)^2) := by
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single anchor]
    · simp only [ite_true]
      congr 1
      dsimp [Matrix.transpose, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · intro k _ hk
      split_ifs with h
      · exact False.elim (hk h.symm)
      · rw [zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  have h_term_pos : 0 < pw.weights anchor * (∑ k, (A k anchor)^2) := by
    apply mul_pos h_anchor
    have h_sq_pos : 0 < (A j anchor)^2 := sq_pos_of_ne_zero h_nz
    exact Finset.sum_pos' (fun k _ => sq_nonneg (A k anchor)) ⟨j, Finset.mem_univ j, h_sq_pos⟩
  have h_all_nonneg : ∀ i, 0 ≤ (Matrix.diagonal pw.weights * (A.transpose * A)) i i := by
    intro i
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp only [ite_true]
      apply mul_nonneg (pw.nonneg i)
      apply Finset.sum_nonneg
      intro k _
      dsimp [Matrix.transpose]
      have : A k i * A k i = (A k i)^2 := by ring
      rw [this]
      exact sq_nonneg (A k i)
    · intro k _ hk
      split_ifs with h
      · exact False.elim (hk h.symm)
      · rw [zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  have h_sum : ∑ i, (Matrix.diagonal pw.weights * (A.transpose * A)) i i > 0 := by
    apply Finset.sum_pos' (fun i _ => h_all_nonneg i) ⟨anchor, Finset.mem_univ anchor, by rw [h_diag]; exact h_term_pos⟩
  exact h_sum

/-! ### 6. Master Integration Certificate -/

/-- Master certificate verifying the Attention KMS State formalization. -/
structure AttentionKMSStateCertificate (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] : Prop where
  weights_pos : ∀ (logits : ι → ℝ) (β : ℝ) (i : ι), 0 < softmaxWeight logits β i
  weights_sum : ∀ (logits : ι → ℝ) (β : ℝ), ∑ i, softmaxWeight logits β i = 1
  density_trace : ∀ (logits : ι → ℝ) (β : ℝ), Matrix.trace (attentionDensityMatrix logits β) = 1
  state_faithful : ∀ (logits : ι → ℝ) (β : ℝ) (B : Matrix ι ι ℝ),
    attentionState logits β (B.transpose * B) = 0 ↔ B = 0
  kms_condition : ∀ (rho rho_inv A B : Matrix ι ι ℝ), rho_inv * rho = 1 →
    Matrix.trace (rho * A * (rho * B * rho_inv)) = Matrix.trace (rho * B * A)
  state_kms : ∀ (logits : ι → ℝ) (β : ℝ) (A B : Matrix ι ι ℝ),
    attentionState logits β (A * (attentionDensityMatrix logits β * B * attentionDensityMatrixInv logits β)) =
    attentionState logits β (B * A)
  modular_inv : ∀ (A : Matrix ι ι ℝ), modularConjugation (modularConjugation A) = A
  modular_anti_mul : ∀ (A B : Matrix ι ι ℝ), modularConjugation (A * B) = modularConjugation B * modularConjugation A
  eviction_null_ideal : ∀ (pw : PrunedWeights ι),
    ∃ E : Matrix ι ι ℝ, E ≠ 0 ∧ prunedState pw (E.transpose * E) = 0

/-- Constructive instance certifying Attention KMS thermal state architecture. -/
theorem compile_attention_kms_state (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    AttentionKMSStateCertificate ι where
  weights_pos := fun logits β i => softmaxWeight_pos logits β i
  weights_sum := fun logits β => softmaxWeight_sum_one logits β
  density_trace := fun logits β => attentionDensityMatrix_trace_one logits β
  state_faithful := fun logits β B => attentionState_faithful logits β B
  kms_condition := fun rho rho_inv A B h => attention_kms_condition rho rho_inv A B h
  state_kms := fun logits β A B => attentionState_kms logits β A B
  modular_inv := fun A => modularConjugation_involutive A
  modular_anti_mul := fun A B => modularConjugation_mul A B
  eviction_null_ideal := fun pw => pruned_cache_has_nontrivial_null_ideal pw

end InfoGeometry.QuantumContext.AttentionKMSState
