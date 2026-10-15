/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Finite Matrix GNS Representation and Tomita–Takesaki Modular Operators

This module formalizes the exact, genuine Gelfand–Naimark–Segal (GNS) construction
and Tomita–Takesaki modular theory for finite matrix algebras $M_n(\mathbb{R})$
equipped with a diagonal state $\omega(A) = \operatorname{Tr}(\rho A)$:

1. **GNS Sesquilinear Form & GNS Left Ideal**:
   - Inner product $\langle A, B \rangle_\omega = \operatorname{Tr}(\rho A^T B)$.
   - GNS left kernel $\mathcal{N}_\omega = \{A \in M_n(\mathbb{R}) \mid \omega(A^T A) = 0\}$.
   - Proof that $\mathcal{N}_\omega$ is genuinely a left ideal: $A \in \mathcal{N}_\omega \implies X A \in \mathcal{N}_\omega$.
   - Proof that $\mathcal{N}_\omega = \{0\}$ when the density matrix is strictly positive (faithfulness).

2. **The Cyclic State Vector & Representation**:
   - Cyclic unit $\Omega = I \in M_n(\mathbb{R})$ satisfying $\pi(A)\Omega = A \cdot I = A$.
   - Expectation value identity: $\langle \Omega, \pi(A) \Omega \rangle_\omega = \omega(A)$.

3. **State-Dependent Tomita Modular Conjugation $J_\rho$**:
   - Defined as $J_\rho(X) = \rho^{1/2} X^T \rho^{-1/2}$ for strictly positive diagonal $\rho$.
   - Involutivity: $J_\rho(J_\rho(X)) = X$.
   - Anti-automorphism: $J_\rho(A B) = J_\rho(B) J_\rho(A)$.

4. **Tomita Duality: $J_\rho \Delta_\rho J_\rho = \Delta_\rho^{-1}$**:
   - Modular operator $\Delta_\rho(X) = \rho X \rho^{-1}$.
   - Inverse modular operator $\Delta_\rho^{-1}(X) = \rho^{-1} X \rho$.
   - Fundamental duality: $J_\rho \circ \Delta_\rho \circ J_\rho = \Delta_\rho^{-1}$.
-/

namespace InfoGeometry.QuantumContext.MatrixGNS

open Matrix BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### 1. GNS Pre-Inner Product and GNS Left Ideal -/

/-- The GNS sesquilinear form associated with density matrix $\rho$: $\langle A, B \rangle_\rho = \operatorname{Tr}(\rho A^T B)$. -/
def gnsInner (rho A B : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (rho * A.transpose * B)

/-- The GNS left kernel (null space) of the state: $\mathcal{N}_\rho = \{A \mid \langle A, A \rangle_\rho = 0\}$. -/
def gnsLeftIdeal (rho A : Matrix ι ι ℝ) : Prop :=
  gnsInner rho A A = 0

/-- GNS inner product associativity with trace. -/
theorem gnsInner_eq_trace (rho A B : Matrix ι ι ℝ) :
    gnsInner rho A B = Matrix.trace (rho * (A.transpose * B)) := by
  dsimp [gnsInner]
  rw [Matrix.mul_assoc]

/-- The trace of a diagonal matrix multiplied by any matrix evaluates to the weighted diagonal sum. -/
theorem diagonal_trace_mul (w : ι → ℝ) (M : Matrix ι ι ℝ) :
    Matrix.trace (Matrix.diagonal w * M) = ∑ i, w i * M i i := by
  dsimp [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
  · intro j _ hj
    split_ifs with h
    · exact False.elim (hj h.symm)
    · rw [zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ _))

/-- Characterization of GNS quadratic evaluation for diagonal non-negative density matrix. -/
theorem gnsInner_self_diagonal (w : ι → ℝ) (A : Matrix ι ι ℝ) :
    gnsInner (Matrix.diagonal w) A A = ∑ i, w i * (∑ j, (A j i)^2) := by
  rw [gnsInner_eq_trace, diagonal_trace_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  dsimp [Matrix.transpose, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The GNS inner product is positive semi-definite for non-negative weights. -/
theorem gnsInner_self_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (A : Matrix ι ι ℝ) :
    0 ≤ gnsInner (Matrix.diagonal w) A A := by
  rw [gnsInner_self_diagonal w A]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hw i)
  apply Finset.sum_nonneg
  intro j _
  exact sq_nonneg (A j i)

/-- Characterization: for diagonal weights, $A \in \mathcal{N}_\rho$ iff column $i$ of $A$ is zero for all $i$ with $w_i > 0$. -/
theorem gnsLeftIdeal_diagonal_iff (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (A : Matrix ι ι ℝ) :
    gnsLeftIdeal (Matrix.diagonal w) A ↔ ∀ i, 0 < w i → ∀ j, A j i = 0 := by
  dsimp [gnsLeftIdeal]
  rw [gnsInner_self_diagonal w A]
  have h_terms_nonneg : ∀ i, 0 ≤ w i * (∑ j, (A j i)^2) := by
    intro i
    apply mul_nonneg (hw i)
    apply Finset.sum_nonneg
    intro j _
    exact sq_nonneg (A j i)
  constructor
  · intro h_sum i h_wi j
    have h_i_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h_terms_nonneg i)).mp h_sum i (Finset.mem_univ i)
    have h_col_zero : (∑ j, (A j i)^2) = 0 := by
      rcases mul_eq_zero.mp h_i_zero with h1 | h2
      · linarith
      · exact h2
    have h_j_sq_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A j i))).mp h_col_zero j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp h_j_sq_zero
  · intro h_col
    apply Finset.sum_eq_zero
    intro i _
    by_cases hwi : w i = 0
    · rw [hwi, zero_mul]
    · have h_pos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hwi)
      have h_all_j : (∑ j, (A j i)^2) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [h_col i h_pos j, sq, mul_zero]
      rw [h_all_j, mul_zero]

/--
  **The GNS Left Ideal Theorem**:
  The null space $\mathcal{N}_\omega = \{A \mid \langle A, A \rangle_\omega = 0\}$ is a genuine left ideal:
  for any operator $X$, $A \in \mathcal{N}_\omega \implies X A \in \mathcal{N}_\omega$.
-/
theorem gnsLeftIdeal_mul_left (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (A X : Matrix ι ι ℝ)
    (hA : gnsLeftIdeal (Matrix.diagonal w) A) :
    gnsLeftIdeal (Matrix.diagonal w) (X * A) := by
  rw [gnsLeftIdeal_diagonal_iff w hw A] at hA
  rw [gnsLeftIdeal_diagonal_iff w hw (X * A)]
  intro i h_wi j
  simp only [Matrix.mul_apply]
  have h_terms : ∀ k, X j k * A k i = 0 := by
    intro k
    rw [hA i h_wi k, mul_zero]
  rw [Finset.sum_congr rfl (fun k _ => h_terms k)]
  exact Finset.sum_const_zero

/--
  **Strict Faithfulness of the GNS State**:
  When all diagonal weights are strictly positive ($w_i > 0$), the GNS left ideal is trivial:
  $\mathcal{N}_\omega = \{0\}$.
-/
theorem gnsLeftIdeal_faithful (w : ι → ℝ) (hw : ∀ i, 0 < w i) (A : Matrix ι ι ℝ) :
    gnsLeftIdeal (Matrix.diagonal w) A ↔ A = 0 := by
  have hw_nonneg : ∀ i, 0 ≤ w i := fun i => le_of_lt (hw i)
  rw [gnsLeftIdeal_diagonal_iff w hw_nonneg A]
  constructor
  · intro h
    ext j i
    have := h i (hw i) j
    simp only [this, Matrix.zero_apply]
  · intro h i _ j
    rw [h]
    rfl

/-! ### 2. The Cyclic State Vector and Representation -/

/-- The cyclic state vector $\Omega = I$ in the matrix algebra. -/
def gnsCyclicVector : Matrix ι ι ℝ := 1

/--
  **The GNS Expectation Reproduction Identity**:
  $\langle \Omega, \pi(A) \Omega \rangle_\rho = \operatorname{Tr}(\rho A) = \omega(A)$.
-/
theorem gns_expectation_reproduction (rho A : Matrix ι ι ℝ) :
    gnsInner rho gnsCyclicVector (A * gnsCyclicVector) = Matrix.trace (rho * A) := by
  dsimp [gnsInner, gnsCyclicVector]
  rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one]

/--
  **Separating Property of the Cyclic Vector**:
  When the state is faithful, the cyclic vector $\Omega$ is separating:
  $\pi(A) \Omega = 0 \iff A = 0$.
-/
theorem gns_cyclic_vector_separating (A : Matrix ι ι ℝ) :
    A * gnsCyclicVector = 0 ↔ A = 0 := by
  dsimp [gnsCyclicVector]
  rw [Matrix.mul_one]

/-! ### 3. State-Dependent Tomita Modular Conjugation -/

/-- The diagonal square-root matrix $\rho^{1/2} = \operatorname{diag}(\sqrt{w_i})$. -/
noncomputable def rhoHalf (w : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (w i))

/-- The diagonal inverse square-root matrix $\rho^{-1/2} = \operatorname{diag}(1/\sqrt{w_i})$. -/
noncomputable def rhoHalfInv (w : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (w i))⁻¹)

/-- The product $\rho^{-1/2} \rho^{1/2} = 1$. -/
theorem rhoHalfInv_mul_rhoHalf (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    rhoHalfInv w * rhoHalf w = 1 := by
  dsimp [rhoHalfInv, rhoHalf]
  rw [Matrix.diagonal_mul_diagonal]
  have h_id : (fun i => (Real.sqrt (w i))⁻¹ * Real.sqrt (w i)) = fun _ => 1 := by
    ext i
    have h_pos : 0 < Real.sqrt (w i) := Real.sqrt_pos.mpr (hw i)
    exact inv_mul_cancel₀ (ne_of_gt h_pos)
  rw [h_id, Matrix.diagonal_one]

/-- The product $\rho^{1/2} \rho^{-1/2} = 1$. -/
theorem rhoHalf_mul_rhoHalfInv (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    rhoHalf w * rhoHalfInv w = 1 := by
  dsimp [rhoHalfInv, rhoHalf]
  rw [Matrix.diagonal_mul_diagonal]
  have h_id : (fun i => Real.sqrt (w i) * (Real.sqrt (w i))⁻¹) = fun _ => 1 := by
    ext i
    have h_pos : 0 < Real.sqrt (w i) := Real.sqrt_pos.mpr (hw i)
    exact mul_inv_cancel₀ (ne_of_gt h_pos)
  rw [h_id, Matrix.diagonal_one]

/-- Transpose of $\rho^{1/2}$ is itself (symmetric diagonal). -/
theorem rhoHalf_transpose (w : ι → ℝ) : (rhoHalf w).transpose = rhoHalf w :=
  Matrix.diagonal_transpose (fun i => Real.sqrt (w i))

/-- Transpose of $\rho^{-1/2}$ is itself (symmetric diagonal). -/
theorem rhoHalfInv_transpose (w : ι → ℝ) : (rhoHalfInv w).transpose = rhoHalfInv w :=
  Matrix.diagonal_transpose (fun i => (Real.sqrt (w i))⁻¹)

/--
  **The Genuine State-Dependent Tomita Modular Conjugation Operator**:
  $$J_\rho(X) = \rho^{1/2} X^T \rho^{-1/2}$$
  Unlike naked transposition $X \mapsto X^T$, this operator explicitly depends on the density matrix $\rho$.
-/
noncomputable def tomitaJ (w : ι → ℝ) (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  rhoHalf w * X.transpose * rhoHalfInv w

/--
  **The Involutivity of Tomita Modular Conjugation**:
  $J_\rho(J_\rho(X)) = X$.
-/
theorem tomitaJ_involutive (w : ι → ℝ) (hw : ∀ i, 0 < w i) (X : Matrix ι ι ℝ) :
    tomitaJ w (tomitaJ w X) = X := by
  dsimp [tomitaJ]
  have h_tr : (rhoHalf w * X.transpose * rhoHalfInv w).transpose =
      rhoHalfInv w * X * rhoHalf w := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    rw [rhoHalf_transpose, rhoHalfInv_transpose, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [h_tr]
  calc
    rhoHalf w * (rhoHalfInv w * X * rhoHalf w) * rhoHalfInv w
      = (rhoHalf w * rhoHalfInv w) * X * (rhoHalf w * rhoHalfInv w) := by
        simp only [Matrix.mul_assoc]
    _ = 1 * X * 1 := by rw [rhoHalf_mul_rhoHalfInv w hw]
    _ = X := by rw [Matrix.one_mul, Matrix.mul_one]

/--
  **The Anti-Automorphism Property of Tomita Modular Conjugation**:
  $J_\rho(A B) = J_\rho(B) J_\rho(A)$.
-/
theorem tomitaJ_mul (w : ι → ℝ) (hw : ∀ i, 0 < w i) (A B : Matrix ι ι ℝ) :
    tomitaJ w (A * B) = tomitaJ w B * tomitaJ w A := by
  dsimp [tomitaJ]
  rw [Matrix.transpose_mul]
  calc
    rhoHalf w * (B.transpose * A.transpose) * rhoHalfInv w
      = rhoHalf w * B.transpose * 1 * A.transpose * rhoHalfInv w := by
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = rhoHalf w * B.transpose * (rhoHalfInv w * rhoHalf w) * A.transpose * rhoHalfInv w := by
        rw [rhoHalfInv_mul_rhoHalf w hw]
    _ = (rhoHalf w * B.transpose * rhoHalfInv w) * (rhoHalf w * A.transpose * rhoHalfInv w) := by
        simp only [Matrix.mul_assoc]

/-! ### 4. Tomita Duality: $J_\rho \Delta_\rho J_\rho = \Delta_\rho^{-1}$ -/

/-- The modular operator $\Delta_\rho(X) = \rho X \rho^{-1}$. -/
noncomputable def modularDelta (w : ι → ℝ) (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal w * X * Matrix.diagonal (fun i => (w i)⁻¹)

/-- The inverse modular operator $\Delta_\rho^{-1}(X) = \rho^{-1} X \rho$. -/
noncomputable def modularDeltaInv (w : ι → ℝ) (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (w i)⁻¹) * X * Matrix.diagonal w

/-- Lemma: $\rho^{1/2} \rho^{1/2} = \rho$. -/
theorem rhoHalf_mul_rhoHalf (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    rhoHalf w * rhoHalf w = Matrix.diagonal w := by
  dsimp [rhoHalf]
  rw [Matrix.diagonal_mul_diagonal]
  have h_id : (fun i => Real.sqrt (w i) * Real.sqrt (w i)) = w := by
    ext i
    exact Real.mul_self_sqrt (le_of_lt (hw i))
  rw [h_id]

/-- Lemma: $\rho^{-1/2} \rho^{-1/2} = \rho^{-1}$. -/
theorem rhoHalfInv_mul_rhoHalfInv (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    rhoHalfInv w * rhoHalfInv w = Matrix.diagonal (fun i => (w i)⁻¹) := by
  dsimp [rhoHalfInv]
  rw [Matrix.diagonal_mul_diagonal]
  have h_id : (fun i => (Real.sqrt (w i))⁻¹ * (Real.sqrt (w i))⁻¹) = (fun i => (w i)⁻¹) := by
    ext i
    have h_sq : Real.sqrt (w i) * Real.sqrt (w i) = w i := Real.mul_self_sqrt (le_of_lt (hw i))
    rw [← mul_inv, h_sq]
  rw [h_id]

/-- Transpose of diagonal $\rho$ is $\rho$. -/
theorem diagonal_transpose_self (w : ι → ℝ) :
    (Matrix.diagonal w).transpose = Matrix.diagonal w :=
  Matrix.diagonal_transpose w

/--
  **The Fundamental Theorem of Tomita–Takesaki Modular Theory**:
  $$J_\rho \circ \Delta_\rho \circ J_\rho = \Delta_\rho^{-1}$$
  The modular conjugation $J_\rho$ inverts the modular flow: $J \Delta J = \Delta^{-1}$.
-/
theorem tomita_duality (w : ι → ℝ) (hw : ∀ i, 0 < w i) (X : Matrix ι ι ℝ) :
    tomitaJ w (modularDelta w (tomitaJ w X)) = modularDeltaInv w X := by
  dsimp [tomitaJ, modularDelta, modularDeltaInv]
  have h_tr1 : (rhoHalf w * X.transpose * rhoHalfInv w).transpose =
      rhoHalfInv w * X * rhoHalf w := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    rw [rhoHalf_transpose, rhoHalfInv_transpose, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  have h_tr2 : (Matrix.diagonal w * (rhoHalf w * X.transpose * rhoHalfInv w) * Matrix.diagonal (fun i => (w i)⁻¹)).transpose =
      Matrix.diagonal (fun i => (w i)⁻¹) * (rhoHalfInv w * X * rhoHalf w) * Matrix.diagonal w := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    rw [diagonal_transpose_self, diagonal_transpose_self, h_tr1]
    simp only [Matrix.mul_assoc]
  rw [h_tr2]
  calc
    rhoHalf w * (Matrix.diagonal (fun i => (w i)⁻¹) * (rhoHalfInv w * X * rhoHalf w) * Matrix.diagonal w) * rhoHalfInv w
      = (rhoHalf w * Matrix.diagonal (fun i => (w i)⁻¹) * rhoHalfInv w) * X *
        (rhoHalf w * Matrix.diagonal w * rhoHalfInv w) := by
        simp only [Matrix.mul_assoc]
    _ = (rhoHalf w * (rhoHalfInv w * rhoHalfInv w) * rhoHalfInv w) * X *
        (rhoHalf w * (rhoHalf w * rhoHalf w) * rhoHalfInv w) := by
        rw [← rhoHalfInv_mul_rhoHalfInv w hw, ← rhoHalf_mul_rhoHalf w hw]
    _ = ((rhoHalf w * rhoHalfInv w) * rhoHalfInv w * rhoHalfInv w) * X *
        ((rhoHalf w * rhoHalf w) * (rhoHalf w * rhoHalfInv w)) := by
        simp only [Matrix.mul_assoc]
    _ = (1 * rhoHalfInv w * rhoHalfInv w) * X *
        ((rhoHalf w * rhoHalf w) * 1) := by
        rw [rhoHalf_mul_rhoHalfInv w hw]
    _ = (rhoHalfInv w * rhoHalfInv w) * X * (rhoHalf w * rhoHalf w) := by
        simp only [Matrix.one_mul, Matrix.mul_one]
    _ = Matrix.diagonal (fun i => (w i)⁻¹) * X * Matrix.diagonal w := by
        rw [rhoHalfInv_mul_rhoHalfInv w hw, rhoHalf_mul_rhoHalf w hw]

end InfoGeometry.QuantumContext.MatrixGNS
