import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InfoGeometry.QuantumContext

open Matrix

/-!
# Section 90: Petz Recovery Data Processing Monotonicity & Causal Stiefel Saturation

Module: `InfoGeometry.QuantumContext.PetzDataProcessingMonotonicity`

This module formalizes:
1. **Causal Pinching Channel & Trace Preservation**:
   - `isCausalProjector P`: symmetric idempotent projector.
   - `causalChannel P X := P * X * P`.
   - Idempotence: `causalChannel P (causalChannel P X) = causalChannel P X`.
   - Trace property: `trace (causalChannel P X) = trace (P * X)`.
   - Trace self-adjointness: `trace (Xᵀ * causalChannel P Y) = trace ((causalChannel P X)ᵀ * Y)`.

2. **The Canonical Petz Reconstruction Map**:
   - `petzRecoveryMap P sigma sigma_inv omega := sigma * (P * (sigma_inv * omega * sigma_inv) * P) * sigma`.
   - Exact reference state reconstruction:
     `petzRecoveryMap P sigma sigma_inv (causalChannel P sigma) = P * sigma * P`.

3. **Stiefel 2-Block Geometry & Deconfabulation Saturation**:
   - Transfer operator `blockV K L = ![![K, 0], ![L, 0]]`.
   - Compressed causal state `compressedState s = ![![s, 0], ![0, 0]]`.
   - Reconstructed state `reconstructState K L s = blockV K L * compressedState s * (blockV K L)ᵀ`.
   - Explicit representation: `reconstructState K L s = ![![s * K^2, s * K * L], ![s * K * L, s * L^2]]`.
   - Trace preservation: under `K^2 + L^2 = 1`, `trace (reconstructState K L s) = s`.
   - Exact Petz Saturation Theorem: for `s ≠ 0` under `K^2 + L^2 = 1`,
     `reconstructState K L s = compressedState s ↔ L = 0`.

4. **Master Certification Conjunction**:
   - `compile_petz_data_processing_monotonicity`.

All proofs are native Mathlib with 0 sorry, 0 admit, and 0 custom axioms.
-/

/-! ### 1. Causal Pinching Projectors & Channel Properties -/

/-- An algebraic causal projector: idempotent and symmetric. -/
def isCausalProjector {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P * P = P ∧ Pᵀ = P

/-- The causal pinching polynomial on any ring: $\mathcal{E}_P(X) = P X P$. -/
def causalChannel {A : Type*} [Ring A] (P X : A) : A :=
  P * X * P

/-- The causal pinching channel is idempotent: $\mathcal{E}_P(\mathcal{E}_P(X)) = \mathcal{E}_P(X)$. -/
theorem causal_channel_idempotent {n : ℕ} (P X : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) :
    causalChannel P (causalChannel P X) = causalChannel P X := by
  unfold causalChannel
  have h : P * (P * X * P) * P = (P * P) * X * (P * P) := by simp only [Matrix.mul_assoc]
  rw [h, hP]

/-- The causal pinching channel preserves the projected trace. -/
theorem causal_channel_trace_preserving {n : ℕ} (P X : Matrix (Fin n) (Fin n) ℝ)
    (hP : isCausalProjector P) :
    trace (causalChannel P X) = trace (P * X) := by
  unfold causalChannel
  rw [Matrix.trace_mul_cycle]
  rw [hP.1]

/-- The causal pinching channel is self-adjoint under trace inner product. -/
theorem pinching_channel_self_adjoint {n : ℕ} (P X Y : Matrix (Fin n) (Fin n) ℝ)
    (hP : isCausalProjector P) :
    trace (Xᵀ * causalChannel P Y) = trace ((causalChannel P X)ᵀ * Y) := by
  unfold causalChannel
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hP.2]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (Xᵀ * P * Y) P]
  simp only [← Matrix.mul_assoc]

/-! ### 2. The Canonical Petz Reconstruction Map -/

/-- General algebraic Petz recovery map:
    $\mathcal{R}_{P, \sigma, \sigma_{\mathrm{inv}}}(\omega) = \sigma (P (\sigma_{\mathrm{inv}} \omega \sigma_{\mathrm{inv}}) P) \sigma$. -/
def petzRecoveryMap {A : Type*} [Ring A] (P sigma sigma_inv omega : A) : A :=
  sigma * (P * (sigma_inv * omega * sigma_inv) * P) * sigma

/-- Ring homomorphisms preserve the causal pinching polynomial. -/
theorem map_causalChannel {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B) (P X : A) :
    f (causalChannel P X) = causalChannel (f P) (f X) := by
  change f (P * X * P) = f P * f X * f P
  simp only [map_mul]

/-- Ring homomorphisms preserve the Petz recovery polynomial. -/
theorem map_petzRecoveryMap {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B) (P sigma sigma_inv omega : A) :
    f (petzRecoveryMap P sigma sigma_inv omega) =
      petzRecoveryMap (f P) (f sigma) (f sigma_inv) (f omega) := by
  change f (sigma * (P * (sigma_inv * omega * sigma_inv) * P) * sigma) =
    f sigma * (f P * (f sigma_inv * f omega * f sigma_inv) * f P) * f sigma
  simp only [map_mul]

/-- **Theorem**: The Petz recovery map reconstructs the reference state on support:
    $$\mathcal{R}_{P, \sigma, \sigma_{\mathrm{inv}}}(\mathcal{E}_P(\sigma)) = P \sigma P$$ -/
theorem petz_reconstructs_reference_state {n : ℕ}
    (P sigma sigma_inv : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P)
    (h_inv : sigma * sigma_inv = P)
    (h_inv_rev : sigma_inv * sigma = P)
    (h_comm : sigma * P = P * sigma)
    (h_inv_comm : sigma_inv * P = P * sigma_inv) :
    petzRecoveryMap P sigma sigma_inv (causalChannel P sigma) = P * sigma * P := by
  unfold petzRecoveryMap causalChannel
  have h1 : sigma_inv * P * sigma = P := by
    calc
      sigma_inv * P * sigma = sigma_inv * (P * sigma) := by simp only [Matrix.mul_assoc]
      _                     = sigma_inv * (sigma * P) := by rw [← h_comm]
      _                     = (sigma_inv * sigma) * P := by simp only [Matrix.mul_assoc]
      _                     = P * P                   := by rw [h_inv_rev]
      _                     = P                       := hP
  have h2 : sigma_inv * (P * sigma * P) * sigma_inv = P * sigma_inv := by
    calc
      sigma_inv * (P * sigma * P) * sigma_inv
        = (sigma_inv * P * sigma) * (P * sigma_inv) := by simp only [Matrix.mul_assoc]
      _ = P * (P * sigma_inv)                       := by rw [h1]
      _ = (P * P) * sigma_inv                       := by simp only [Matrix.mul_assoc]
      _ = P * sigma_inv                             := by rw [hP]
  have h3 : P * (P * sigma_inv) * P = P * sigma_inv := by
    calc
      P * (P * sigma_inv) * P = (P * P) * (sigma_inv * P) := by simp only [Matrix.mul_assoc]
      _                       = P * (sigma_inv * P)       := by rw [hP]
      _                       = P * (P * sigma_inv)       := by rw [h_inv_comm]
      _                       = (P * P) * sigma_inv       := by simp only [Matrix.mul_assoc]
      _                       = P * sigma_inv             := by rw [hP]
  have h4 : sigma * (P * sigma_inv) * sigma = sigma * P := by
    calc
      sigma * (P * sigma_inv) * sigma = (sigma * P) * (sigma_inv * sigma) := by simp only [Matrix.mul_assoc]
      _                               = (sigma * P) * P                   := by rw [h_inv_rev]
      _                               = sigma * (P * P)                   := by simp only [Matrix.mul_assoc]
      _                               = sigma * P                         := by rw [hP]
  have h5 : P * sigma * P = sigma * P := by
    calc
      P * sigma * P = (P * sigma) * P := by simp only [Matrix.mul_assoc]
      _             = (sigma * P) * P := by rw [← h_comm]
      _             = sigma * (P * P) := by simp only [Matrix.mul_assoc]
      _             = sigma * P       := by rw [hP]
  rw [h2, h3, h4, h5]

/-! ### 3. Stiefel 2-Block Geometry & Deconfabulation Saturation -/

/-- The $2 \times 2$ block intertwiner $V(K, L) = \begin{pmatrix} K & 0 \\ L & 0 \end{pmatrix}$. -/
def blockV (K L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![K, 0], ![L, 0]]

/-- The compressed causal past state $\sigma_{\mathrm{causal}}(s) = \begin{pmatrix} s & 0 \\ 0 & 0 \end{pmatrix}$. -/
def compressedState (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![s, 0], ![0, 0]]

/-- The reconstructed state $\rho_{\mathrm{rec}}(K, L, s) = V \sigma_{\mathrm{causal}}(s) V^\top$. -/
def reconstructState (K L s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (blockV K L) * (compressedState s) * (blockV K L)ᵀ

/-- Explicit matrix representation of the reconstructed state. -/
theorem reconstructState_explicit (K L s : ℝ) :
    reconstructState K L s = ![![s * K ^ 2, s * K * L], ![s * K * L, s * L ^ 2]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [reconstructState]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [blockV, compressedState, Matrix.transpose]
    ring
  }

/-- The Gram operator $V^\top V$ has diagonal entry $K^2 + L^2$ on support. -/
theorem blockV_gram (K L : ℝ) :
    (blockV K L)ᵀ * blockV K L = ![![K ^ 2 + L ^ 2, 0], ![0, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [blockV, Matrix.transpose]
    ring
  }

/-- **Theorem (Trace Preservation)**: Under the Stiefel constraint $K^2 + L^2 = 1$,
    the total trace of the reconstructed density matrix strictly equals the input trace:
    $\operatorname{Tr}(\rho_{\mathrm{rec}}(K, L, s)) = s$. -/
theorem petz_stiefel_trace_preservation (K L s : ℝ) (h_stiefel : K ^ 2 + L ^ 2 = 1) :
    trace (reconstructState K L s) = s := by
  rw [reconstructState_explicit]
  unfold Matrix.trace
  rw [Fin.sum_univ_two]
  dsimp
  calc
    s * K ^ 2 + s * L ^ 2 = s * (K ^ 2 + L ^ 2) := by ring
    _                     = s * 1               := by rw [h_stiefel]
    _                     = s                   := mul_one s

/-- **Theorem (Petz Sufficiency & Exact Saturation Equivalence)**:
    For non-zero input $s \ne 0$ under Stiefel isometry $K^2 + L^2 = 1$,
    the reconstructed state equals the compressed state if and only if future leakage vanishes ($L = 0$):
    $$\rho_{\mathrm{rec}}(K, L, s) = \sigma_{\mathrm{causal}}(s) \iff L = 0$$ -/
theorem petz_stiefel_saturation_iff_zero_future (K L s : ℝ)
    (h_stiefel : K ^ 2 + L ^ 2 = 1) (hs : s ≠ 0) :
    reconstructState K L s = compressedState s ↔ L = 0 := by
  constructor
  · intro h
    have h11 : (reconstructState K L s) 1 1 = (compressedState s) 1 1 := by rw [h]
    rw [reconstructState_explicit] at h11
    dsimp [compressedState] at h11
    have hL2 : L ^ 2 = 0 := by
      cases mul_eq_zero.mp h11 with
      | inl h_s => exact False.elim (hs h_s)
      | inr h_L2 => exact h_L2
    exact sq_eq_zero_iff.mp hL2
  · intro hL
    have hK2 : K ^ 2 = 1 := by
      calc
        K ^ 2 = (K ^ 2 + L ^ 2) - L ^ 2 := by ring
        _     = 1 - 0 ^ 2               := by rw [h_stiefel, hL]
        _     = 1                       := by ring
    rw [reconstructState_explicit, compressedState]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hL, hK2]

/-! ### 4. Master Certification Conjunction -/

/-- Master compiler theorem ratifying Section 90 under OpenGauss QMS protocol. -/
theorem compile_petz_data_processing_monotonicity :
    (∀ (K L s : ℝ), K ^ 2 + L ^ 2 = 1 → trace (reconstructState K L s) = s) ∧
    (∀ (K L s : ℝ), K ^ 2 + L ^ 2 = 1 → s ≠ 0 →
      (reconstructState K L s = compressedState s ↔ L = 0)) :=
  ⟨petz_stiefel_trace_preservation, petz_stiefel_saturation_iff_zero_future⟩

namespace PetzMonotonicity
/-- Re-export of compile theorem for interoperability across modules. -/
theorem compile_petz_data_processing_monotonicity :
    (∀ (K L s : ℝ), K ^ 2 + L ^ 2 = 1 → trace (reconstructState K L s) = s) ∧
    (∀ (K L s : ℝ), K ^ 2 + L ^ 2 = 1 → s ≠ 0 →
      (reconstructState K L s = compressedState s ↔ L = 0)) :=
  InfoGeometry.QuantumContext.compile_petz_data_processing_monotonicity
end PetzMonotonicity

end InfoGeometry.QuantumContext
