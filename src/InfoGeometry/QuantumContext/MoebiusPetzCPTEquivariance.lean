import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import InfoGeometry.QuantumContext.PetzDataProcessingMonotonicity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InfoGeometry.QuantumContext

open Matrix

/-!
# Section 91: Swap Covariance of the Algebraic Petz Map

Module: `InfoGeometry.QuantumContext.MoebiusPetzCPTEquivariance`

This module proves finite-matrix identities for conjugation by the swap matrix
`tau1`, together with the independent Stiefel reconstruction model. The
`petzRecoveryMap` here is a polynomial matrix expression; no positivity,
complete-positivity, or trace-preservation claim for that map is made here.

1. **The 2-Level Andreev Reflection**:
   - $\tau_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$.
   - Involution: $\tau_1^2 = 1$.
   - Symmetry: $\tau_1^\top = \tau_1$.
   - Trace vanishing: $\operatorname{Tr}(\tau_1) = 0$.
   - Pinching covariance: $\tau_1 \mathcal{E}_P(X) \tau_1 = \mathcal{E}_{\tau_1 P \tau_1}(\tau_1 X \tau_1)$.
   - Simultaneous Petz recovery covariance:
     $\tau_1 \mathcal{R}_{P, \sigma, \sigma^{-1}}(\omega) \tau_1 =
      \mathcal{R}_{\tau_1 P \tau_1, \tau_1 \sigma \tau_1, \tau_1 \sigma^{-1} \tau_1}(\tau_1 \omega \tau_1)$.

2. **Möbius Stiefel Intertwiner & Parameter Swap**:
   - `moebiusStiefelCPT (K, L) = (L, K)`.
   - Involutive and norm-preserving: $L^2 + K^2 = K^2 + L^2$.
   - Exact particle-hole reflection on reconstructed states:
     $$\tau_1 \rho_{\mathrm{rec}}(K, L, s) \tau_1 = \rho_{\mathrm{rec}}(L, K, s)$$
     swapping past causal retention ($K^2$) with forward environmental dissipation ($L^2$).

3. **Trace and Extremal Invariance**:
   - Trace preservation: $\operatorname{Tr}(\tau_1 \rho_{\mathrm{rec}}(K, L, s) \tau_1) = \operatorname{Tr}(\rho_{\mathrm{rec}}(K, L, s))$.
   - Swap-fixed point: the balanced all-entries-equal matrix is invariant under $\tau_1$.
   - Extremal boundary flip: $\tau_1$ exchanges pure past ($\sigma_{\mathrm{causal}}(s)$) with pure future.
   - Dual saturation theorem: $\tau_1 \rho_{\mathrm{rec}} \tau_1 = \sigma_{\mathrm{causal}}(s) \iff K = 0$.

4. **Swap Equilibrium Theorem**:
   - Commutativity $[\tau_1, \rho_{\mathrm{rec}}] = 0$ holds if and only if $K^2 = L^2$.

All proofs are native Mathlib with 0 sorry, 0 admit, and 0 custom axioms.
-/

/-! ### 1. The 2-Level Andreev Reflection Operator -/

/-- The canonical 2-level particle-hole / Andreev reflection matrix $\tau_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def tau1 : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1], ![1, 0]]

/-- $\tau_1$ is an involution: $\tau_1^2 = 1$. -/
theorem tau1_involutive : tau1 * tau1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [tau1, Matrix.one_apply]
    ring
  }

/-- $\tau_1$ is symmetric: $\tau_1^\top = \tau_1$. -/
theorem tau1_symmetric : tau1ᵀ = tau1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- $\tau_1$ trace vanishes: $\operatorname{Tr}(\tau_1) = 0$. -/
theorem tau1_trace_zero : trace tau1 = 0 := by
  unfold Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two]
  dsimp [tau1]
  ring

/-- Multiplicative conjugation by $\tau_1$: $\tau_1 (A B) \tau_1 = (\tau_1 A \tau_1)(\tau_1 B \tau_1)$. -/
theorem tau1_conj_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    tau1 * (A * B) * tau1 = (tau1 * A * tau1) * (tau1 * B * tau1) := by
  calc
    tau1 * (A * B) * tau1 = tau1 * A * B * tau1 := by simp only [Matrix.mul_assoc]
    _ = tau1 * A * (1 * B) * tau1 := by rw [Matrix.one_mul]
    _ = tau1 * A * (tau1 * tau1 * B) * tau1 := by rw [← tau1_involutive]
    _ = (tau1 * A * tau1) * (tau1 * B * tau1) := by noncomm_ring

/-- Conjugation by $\tau_1$ preserves the causal pinching channel structure:
    $\tau_1 \mathcal{E}_P(X) \tau_1 = \mathcal{E}_{\tau_1 P \tau_1}(\tau_1 X \tau_1)$. -/
theorem tau1_pinching_covariance (P X : Matrix (Fin 2) (Fin 2) ℝ) :
    tau1 * causalChannel P X * tau1 = causalChannel (tau1 * P * tau1) (tau1 * X * tau1) := by
  unfold causalChannel
  calc
    tau1 * (P * X * P) * tau1 = (tau1 * (P * X) * tau1) * (tau1 * P * tau1) := by rw [tau1_conj_mul]
    _ = (tau1 * P * tau1) * (tau1 * X * tau1) * (tau1 * P * tau1) := by rw [tau1_conj_mul]

/-- Conjugation by `tau1` distributes across a product of three factors. -/
private theorem tau1_conj_mul_three (A B C : Matrix (Fin 2) (Fin 2) ℝ) :
    tau1 * (A * B * C) * tau1 =
      (tau1 * A * tau1) * (tau1 * B * tau1) * (tau1 * C * tau1) := by
  calc
    tau1 * (A * B * C) * tau1 = tau1 * ((A * B) * C) * tau1 := rfl
    _ = (tau1 * (A * B) * tau1) * (tau1 * C * tau1) := tau1_conj_mul (A * B) C
    _ = ((tau1 * A * tau1) * (tau1 * B * tau1)) * (tau1 * C * tau1) := by
      rw [tau1_conj_mul]
    _ = (tau1 * A * tau1) * (tau1 * B * tau1) * (tau1 * C * tau1) := by
      simp only [Matrix.mul_assoc]

/-- The algebraic Petz map is covariant under simultaneous `tau1`-conjugation
of its projector, reference state, inverse reference, and input. -/
theorem tau1_petzRecoveryMap_covariance
    (P sigma sigmaInv omega : Matrix (Fin 2) (Fin 2) ℝ) :
    tau1 * petzRecoveryMap P sigma sigmaInv omega * tau1 =
      petzRecoveryMap (tau1 * P * tau1) (tau1 * sigma * tau1)
        (tau1 * sigmaInv * tau1) (tau1 * omega * tau1) := by
  unfold petzRecoveryMap
  rw [tau1_conj_mul_three, tau1_conj_mul_three, tau1_conj_mul_three]

/-! ### 2. Möbius Stiefel Action & State Reflection -/

/-- The Möbius CPT particle-hole swap on Stiefel parameters: $(K, L) \mapsto (L, K)$. -/
def moebiusStiefelCPT (K L : ℝ) : ℝ × ℝ := (L, K)

/-- The Möbius Stiefel reflection is involutive: $(L, K) \mapsto (K, L)$. -/
theorem moebiusStiefelCPT_involutive (K L : ℝ) :
    moebiusStiefelCPT (moebiusStiefelCPT K L).1 (moebiusStiefelCPT K L).2 = (K, L) := by
  dsimp [moebiusStiefelCPT]

/-- The Stiefel sphere constraint $K^2 + L^2$ is strictly invariant under Möbius CPT swap. -/
theorem moebiusStiefelCPT_preserves_norm (K L : ℝ) :
    (moebiusStiefelCPT K L).1 ^ 2 + (moebiusStiefelCPT K L).2 ^ 2 = K ^ 2 + L ^ 2 := by
  dsimp [moebiusStiefelCPT]
  ring

/-- **Theorem (Möbius Petz Reflection)**:
    Conjugation of the reconstructed state by $\tau_1$ exchanges retention $K$ and dissipation $L$:
    $$\tau_1 \rho_{\mathrm{rec}}(K, L, s) \tau_1 = \rho_{\mathrm{rec}}(L, K, s)$$ -/
theorem tau1_reconstructState_swap (K L s : ℝ) :
    tau1 * reconstructState K L s * tau1 = reconstructState L K s := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [reconstructState]
    repeat rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [tau1, blockV, compressedState, Matrix.transpose]
    ring
  }

/-- Intertwining identity with `moebiusStiefelCPT`. -/
theorem tau1_reconstructState_intertwine (K L s : ℝ) :
    tau1 * reconstructState K L s * tau1 =
      reconstructState (moebiusStiefelCPT K L).1 (moebiusStiefelCPT K L).2 s := by
  exact tau1_reconstructState_swap K L s

/-! ### 3. Trace and Extremal Invariance -/

/-- The trace of the reconstructed state is strictly invariant under $\tau_1$ conjugation. -/
theorem tau1_reconstructState_trace_invariant (K L s : ℝ) :
    trace (tau1 * reconstructState K L s * tau1) = trace (reconstructState K L s) := by
  rw [tau1_reconstructState_swap]
  rw [reconstructState_explicit, reconstructState_explicit]
  unfold Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  dsimp
  ring

/-- Under the Stiefel condition, the trace after $\tau_1$ conjugation equals the input trace $s$. -/
theorem tau1_reconstructState_trace_eq_input (K L s : ℝ) (h_stiefel : K ^ 2 + L ^ 2 = 1) :
    trace (tau1 * reconstructState K L s * tau1) = s := by
  rw [tau1_reconstructState_trace_invariant]
  exact petz_stiefel_trace_preservation K L s h_stiefel

/-- The self-dual state corresponding to equal retention and dissipation ($K^2 = L^2 = 1/2$). -/
noncomputable def andreevSelfDualState (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![s / 2, s / 2], ![s / 2, s / 2]]

/-- **Theorem (Self-Dual Fixed Point)**:
    The balanced state is invariant under $\tau_1$ conjugation. -/
theorem andreev_self_dual_is_fixed_point (s : ℝ) :
    tau1 * andreevSelfDualState s * tau1 = andreevSelfDualState s := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    repeat rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [tau1, andreevSelfDualState]
    ring
  }

/-- Pure future state (complete dissipation, zero retention). -/
def pureFutureState (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 0], ![0, s]]

/-- $\tau_1$ flips the deconfabulated pure past state into the pure future state. -/
theorem andreev_flips_compressed_to_future (s : ℝ) :
    tau1 * compressedState s * tau1 = pureFutureState s := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    repeat rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [tau1, compressedState, pureFutureState]
    ring
  }

/-- $\tau_1$ flips the pure future state back into the compressed past state. -/
theorem andreev_flips_future_to_compressed (s : ℝ) :
    tau1 * pureFutureState s * tau1 = compressedState s := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    repeat rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [tau1, compressedState, pureFutureState]
    ring
  }

/-- **Theorem (Dual Saturation Theorem)**:
    The Andreev-reflected Petz state saturates to the compressed past state if and only if
    original retention vanishes ($K = 0$). -/
theorem tau1_petz_saturates_iff_zero_past (K L s : ℝ)
    (h_stiefel : K ^ 2 + L ^ 2 = 1) (hs : s ≠ 0) :
    tau1 * reconstructState K L s * tau1 = compressedState s ↔ K = 0 := by
  rw [tau1_reconstructState_swap]
  have h_stiefel_swap : L ^ 2 + K ^ 2 = 1 := by linarith [h_stiefel]
  exact petz_stiefel_saturation_iff_zero_future L K s h_stiefel_swap hs

/-- The unreflected Petz state equals the pure future state if and only if $K = 0$. -/
theorem petz_saturates_future_iff_zero_past (K L s : ℝ)
    (h_stiefel : K ^ 2 + L ^ 2 = 1) (hs : s ≠ 0) :
    reconstructState K L s = pureFutureState s ↔ K = 0 := by
  constructor
  · intro h
    have h00 : (reconstructState K L s) 0 0 = (pureFutureState s) 0 0 := by rw [h]
    rw [reconstructState_explicit] at h00
    dsimp [pureFutureState] at h00
    have hK2 : K ^ 2 = 0 := by
      cases mul_eq_zero.mp h00 with
      | inl h_s => exact False.elim (hs h_s)
      | inr h_k2 => exact h_k2
    exact sq_eq_zero_iff.mp hK2
  · intro hK
    have hL2 : L ^ 2 = 1 := by
      calc
        L ^ 2 = (K ^ 2 + L ^ 2) - K ^ 2 := by ring
        _     = 1 - 0 ^ 2               := by rw [h_stiefel, hK]
        _     = 1                       := by ring
    rw [reconstructState_explicit, pureFutureState]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hK, hL2]

/-! ### 4. Swap Equilibrium Theorem -/

/-- Auxiliary lemma: $\tau_1 A = A \tau_1 \iff \tau_1 A \tau_1 = A$. -/
theorem tau1_commute_iff_conj_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    tau1 * A = A * tau1 ↔ tau1 * A * tau1 = A := by
  constructor
  · intro h
    calc
      tau1 * A * tau1 = (A * tau1) * tau1 := by rw [h]
      _               = A * (tau1 * tau1) := by simp only [Matrix.mul_assoc]
      _               = A * 1             := by rw [tau1_involutive]
      _               = A                 := Matrix.mul_one A
  · intro h
    calc
      tau1 * A = (tau1 * A) * 1             := (Matrix.mul_one (tau1 * A)).symm
      _        = (tau1 * A) * (tau1 * tau1) := by rw [tau1_involutive]
      _        = (tau1 * A * tau1) * tau1   := by simp only [Matrix.mul_assoc]
      _        = A * tau1                   := by rw [h]

/-- **Theorem (Swap Equilibrium Theorem)**:
    For $s \ne 0$, the reconstructed state commutes with the Andreev reflection $\tau_1$
    if and only if retention and dissipation are equally balanced ($K^2 = L^2$). -/
theorem tau1_commutes_iff_equal_squares (K L s : ℝ) (hs : s ≠ 0) :
    tau1 * reconstructState K L s = reconstructState K L s * tau1 ↔ K ^ 2 = L ^ 2 := by
  rw [tau1_commute_iff_conj_eq]
  rw [tau1_reconstructState_swap]
  constructor
  · intro h
    have h00 : (reconstructState L K s) 0 0 = (reconstructState K L s) 0 0 := by rw [h]
    rw [reconstructState_explicit, reconstructState_explicit] at h00
    dsimp at h00
    have hdiff : s * (L ^ 2 - K ^ 2) = 0 := by
      calc
        s * (L ^ 2 - K ^ 2) = s * L ^ 2 - s * K ^ 2 := by ring
        _                   = 0                     := sub_eq_zero.mpr h00
    cases mul_eq_zero.mp hdiff with
    | inl h_s => exact False.elim (hs h_s)
    | inr h_sub =>
      have hLK : L ^ 2 = K ^ 2 := sub_eq_zero.mp h_sub
      exact hLK.symm
  · intro h_eq
    rw [reconstructState_explicit, reconstructState_explicit]
    ext i j
    fin_cases i <;> fin_cases j
    · dsimp; rw [← h_eq]
    · dsimp; ring
    · dsimp; ring
    · dsimp; rw [h_eq]

/-! ### 5. Master Certification Conjunction -/

/-- Master compiler theorem ratifying Section 91 under OpenGauss QMS protocol. -/
theorem compile_moebius_petz_cpt_equivariance :
    (tau1 * tau1 = 1) ∧
    (tau1ᵀ = tau1) ∧
    (∀ (P X : Matrix (Fin 2) (Fin 2) ℝ),
      tau1 * causalChannel P X * tau1 = causalChannel (tau1 * P * tau1) (tau1 * X * tau1)) ∧
    (∀ (P sigma sigmaInv omega : Matrix (Fin 2) (Fin 2) ℝ),
      tau1 * petzRecoveryMap P sigma sigmaInv omega * tau1 =
        petzRecoveryMap (tau1 * P * tau1) (tau1 * sigma * tau1)
          (tau1 * sigmaInv * tau1) (tau1 * omega * tau1)) ∧
    (∀ (K L s : ℝ),
      tau1 * reconstructState K L s * tau1 = reconstructState L K s) ∧
    (∀ (K L : ℝ),
      (moebiusStiefelCPT K L).1 ^ 2 + (moebiusStiefelCPT K L).2 ^ 2 = K ^ 2 + L ^ 2) ∧
    (∀ (K L s : ℝ),
      trace (tau1 * reconstructState K L s * tau1) = trace (reconstructState K L s)) ∧
    (∀ (s : ℝ),
      tau1 * andreevSelfDualState s * tau1 = andreevSelfDualState s) ∧
    (∀ (s : ℝ),
      tau1 * compressedState s * tau1 = pureFutureState s) ∧
    (∀ (s : ℝ),
      tau1 * pureFutureState s * tau1 = compressedState s) ∧
    (∀ (K L s : ℝ),
      K ^ 2 + L ^ 2 = 1 → s ≠ 0 →
        (tau1 * reconstructState K L s * tau1 = compressedState s ↔ K = 0)) ∧
    (∀ (K L s : ℝ),
      s ≠ 0 → (tau1 * reconstructState K L s = reconstructState K L s * tau1 ↔ K ^ 2 = L ^ 2)) :=
  ⟨tau1_involutive, tau1_symmetric, tau1_pinching_covariance,
   tau1_petzRecoveryMap_covariance,
   tau1_reconstructState_swap, moebiusStiefelCPT_preserves_norm,
   tau1_reconstructState_trace_invariant, andreev_self_dual_is_fixed_point,
   andreev_flips_compressed_to_future, andreev_flips_future_to_compressed,
   tau1_petz_saturates_iff_zero_past, tau1_commutes_iff_equal_squares⟩

namespace MoebiusPetzCPT
/-- Re-export of compile theorem for interoperability across modules. -/
theorem compile_moebius_petz_cpt_equivariance :
    (tau1 * tau1 = 1) ∧
    (tau1ᵀ = tau1) ∧
    (∀ (P X : Matrix (Fin 2) (Fin 2) ℝ),
      tau1 * causalChannel P X * tau1 = causalChannel (tau1 * P * tau1) (tau1 * X * tau1)) ∧
    (∀ (P sigma sigmaInv omega : Matrix (Fin 2) (Fin 2) ℝ),
      tau1 * petzRecoveryMap P sigma sigmaInv omega * tau1 =
        petzRecoveryMap (tau1 * P * tau1) (tau1 * sigma * tau1)
          (tau1 * sigmaInv * tau1) (tau1 * omega * tau1)) ∧
    (∀ (K L s : ℝ),
      tau1 * reconstructState K L s * tau1 = reconstructState L K s) ∧
    (∀ (K L : ℝ),
      (moebiusStiefelCPT K L).1 ^ 2 + (moebiusStiefelCPT K L).2 ^ 2 = K ^ 2 + L ^ 2) ∧
    (∀ (K L s : ℝ),
      trace (tau1 * reconstructState K L s * tau1) = trace (reconstructState K L s)) ∧
    (∀ (s : ℝ),
      tau1 * andreevSelfDualState s * tau1 = andreevSelfDualState s) ∧
    (∀ (s : ℝ),
      tau1 * compressedState s * tau1 = pureFutureState s) ∧
    (∀ (s : ℝ),
      tau1 * pureFutureState s * tau1 = compressedState s) ∧
    (∀ (K L s : ℝ),
      K ^ 2 + L ^ 2 = 1 → s ≠ 0 →
        (tau1 * reconstructState K L s * tau1 = compressedState s ↔ K = 0)) ∧
    (∀ (K L s : ℝ),
      s ≠ 0 → (tau1 * reconstructState K L s = reconstructState K L s * tau1 ↔ K ^ 2 = L ^ 2)) :=
  InfoGeometry.QuantumContext.compile_moebius_petz_cpt_equivariance
end MoebiusPetzCPT

end InfoGeometry.QuantumContext
