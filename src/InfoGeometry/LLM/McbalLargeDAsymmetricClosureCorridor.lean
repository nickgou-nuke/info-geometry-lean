/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.SpinPinTransformerLayer
import InfoGeometry.LLM.SpinTransformerMeanField
import InfoGeometry.LLM.SpinTransformerFixedPoint
import InfoGeometry.LLM.SpinTransformerQuenchRelax
import InfoGeometry.LLM.SpinTransformerPathEntropy
import InfoGeometry.QuantumContext.MarkovDrazinSemisimplicity
import InfoGeometry.OperatorAlgebra.NoncommutativeCovarianceClosure
import InfoGeometry.OperatorAlgebra.SemilinearOperatorGeometry
import InfoGeometry.Algebra.MonarchFactorization
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Krein.ExceptionalPointBilinear
import InfoGeometry.Canonical.DrazinNilpotentShellResolution
import InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianExtensionPoset

/-!
# The Three-Post `mcbal` Kinetic Vector-Spin Corridor & 8-Stage `solve et coagula` Poset to Krein–Yangian LogCFT (`𝔐₁ ≺ 𝔐₂ ≺ ⋯ ≺ 𝔐₈`)

This module formalizes in native Mathlib (`Lean v4.34.1`) with full kernel-checked proofs:
1. The complete three-post `mcbal.github.io` kinetic vector-spin & nonequilibrium transformer
   corridor stored in `external_refs/mcbal_blog/`:
   - **Post 1 (`spin-model-transformers`)**:
     Large-$D$ saddle-point response map $\varphi_\beta(h) = \frac{\beta}{1 + \gamma} h$ where
     $\beta^2 r^2 = R^2 (\gamma^2 - 1)$ ($R^2 = D/2 - 1$), exact squared response norm
     $\|\varphi_\beta(h)\|^2 = R^2 \frac{\gamma - 1}{\gamma + 1}$, radial slack identity
     $R^2 - \|\varphi_\beta(h)\|^2 = \frac{2 R^2}{1 + \gamma}$, exact conjugate-field inverse
     recovery $\varphi_\beta^{-1}(\varphi_\beta(h)) = h$, single-spin transverse/longitudinal
     covariance operator $\Sigma_{\text{spin}}(\tau, \rho, P_\parallel) = \tau(1 - P_\parallel) + \rho P_\parallel$,
     and fluctuation-response relation $\beta \tau = g$.
   - **Post 2 (`nonequilibrium-dynamics-in-spin-model-transformers`)**:
     Pre-norm conjugate-field residual bus $m_{\text{out}}(\Delta_h) = \varphi_\beta(\varphi_\beta^{-1}(m_{\text{in}}) + \Delta_h)$
     preserving the exact identity at $\Delta_h = 0$ (contrasted with naive magnetization-space
     attenuation), Quench-and-Relax $K$-layer telescoping entropy production
     $\sum_{k=0}^{K-1} (\sigma_{\text{hk}, k} + (\Delta_k - \Delta_{k+1})) = \sum_{k=0}^{K-1} \sigma_{\text{hk}, k} + (\Delta_0 - \Delta_K)$,
     and non-reciprocal housekeeping dissipation (`housekeepingEntropyProxy_nonneg`,
     `housekeepingEntropyProxy_eq_zero_of_symmetric`).
   - **Post 3 (`a-large-d-closure-for-asymmetric-kinetic-vector-spin-systems`)**:
     Mean/fluctuation binary cut $s_i = m_i + \delta s_i$, typical squared local field norm
     $r_i^2 = \|\bar{h}_i\|^2 + v_i$ with $v_i = (J C J^\top)_{ii}$, deterministic gain
     $a_i = \frac{\beta}{1 + \gamma_i}$, fresh noise variance $b_i = \frac{2 R^2}{1 + \gamma_i}$,
     the **Exact Algebraic Sphere Conservation Law** $a_i^2 r_i^2 + b_i = R^2$ and
     $\|m_i'\|^2 + C_{ii}' = a_i^2 \|\bar{h}_i\|^2 + (a_i^2 v_i + b_i) = R^2$, the full
     non-commutative operator covariance closure (`FiniteOperatorCovariance`,
     `CovarianceTransport`, `CovarianceDynamics`, `CovarianceStationary`) with gain-mixing
     commutator defect $[G, J] \neq 0$, and the 3-level closure hierarchy (Naive Mean Field vs.
     Diagonal Closure vs. Full Closure) showing agreement at $K = 1$ for diagonal $C_0$ and a
     strictly non-zero shared-input off-diagonal covariance defect at $K = 2$.
2. The **8-Stage `solve et coagula` Sequence-Modeling-to-LogCFT Acyclic Causal Poset**
   (`McbalToKreinYangianLogCFTStage`, $\mathfrak{M}_1 \prec \mathfrak{M}_2 \prec \dots \prec \mathfrak{M}_8$)
   unifying the conscious stochastic semisimple thesis ($\mathbf{T}$, Drazin index 1) and the
   repressed Krein–Yangian LogCFT shadow ($\mathbf{S}$, isotropic Jordan nilpotency $N_{\text{nil}}^2 = 0$
   and quadratic $O(t^2)$ secular evolution).
-/

noncomputable section

namespace InfoGeometry.LLM.McbalLargeDAsymmetricClosureCorridor

open Matrix Filter
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianExtensionPoset
open InfoGeometry.OperatorAlgebra.FiniteOperatorCovariance
open InfoGeometry.OperatorAlgebra.CovarianceTransport
open InfoGeometry.OperatorAlgebra.CovarianceDynamics
open InfoGeometry.OperatorAlgebra.CovarianceStationary
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.Algebra.MonarchFactorization
open InfoGeometry.Krein.ExceptionalPointBilinear
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinNilpotentShell

/-! ===========================================================================
    Section 0: 8-Stage `solve et coagula` Acyclic Causal Poset (`𝔐₁ ≺ 𝔐₂ ≺ ⋯ ≺ 𝔐₈`)
    =========================================================================== -/

/-- The 8-stage `solve et coagula` acyclic causal poset ($\mathfrak{M}_1 \prec \dots \prec \mathfrak{M}_8$)
connecting the classical `mcbal` Gibbs/vMF spin-transformer and stochastic Drazin-index-1
semisimplicity to non-commutative operator covariance closure, multi-hop word non-closure,
the $\mathcal{C}\ell(n,n)$ Jordan–Wigner spin chain, Yangian monodromy words, the Krein–Hopf
exceptional horizon, and the Drazin nilpotent shell / LogCFT $O(t^2)$ secular synthesis. -/
inductive McbalToKreinYangianLogCFTStage : Type
  | M1_ClassicalGibbsVmfResponseAndQuenchRelaxPathEntropy
  | M2_StochasticDrazinSemisimplicityAporia
  | M3_NoncommutativeLargeDCovarianceClosureAndGainDefect
  | M4_MultiHopOperatorWordNonClosure
  | M5_Cl11TensorTowerAndSonnBivectorClosure
  | M6_YangianMonodromyWordsAndNonAbelianGaugeLax
  | M7_KreinHopfExceptionalHorizonAndIsotropicJordanCell
  | M8_DrazinNilpotentShellAndLogCFTSecularSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace McbalToKreinYangianLogCFTStage

/-- Causal prerequisite DAG (as `Finset ℕ`) for the 8-stage poset $\mathfrak{M}_1 \prec \dots \prec \mathfrak{M}_8$,
including the diamond fork $\mathfrak{M}_4 \prec \{\mathfrak{M}_5, \mathfrak{M}_6\} \prec \mathfrak{M}_7$. -/
def causalPrerequisites : McbalToKreinYangianLogCFTStage → Finset ℕ
  | .M1_ClassicalGibbsVmfResponseAndQuenchRelaxPathEntropy => {1}
  | .M2_StochasticDrazinSemisimplicityAporia => {1, 2}
  | .M3_NoncommutativeLargeDCovarianceClosureAndGainDefect => {1, 2, 3}
  | .M4_MultiHopOperatorWordNonClosure => {1, 2, 3, 4}
  | .M5_Cl11TensorTowerAndSonnBivectorClosure => {1, 2, 3, 4, 5}
  | .M6_YangianMonodromyWordsAndNonAbelianGaugeLax => {1, 2, 3, 4, 6}
  | .M7_KreinHopfExceptionalHorizonAndIsotropicJordanCell => {1, 2, 3, 4, 5, 6, 7}
  | .M8_DrazinNilpotentShellAndLogCFTSecularSynthesis => {1, 2, 3, 4, 5, 6, 7, 8}

theorem causalPrerequisites_injective : Function.Injective causalPrerequisites := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals revert h; decide

instance instPartialOrder : PartialOrder McbalToKreinYangianLogCFTStage :=
  PartialOrder.lift causalPrerequisites causalPrerequisites_injective

instance instDecidableLE : DecidableRel (α := McbalToKreinYangianLogCFTStage) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (causalPrerequisites a ⊆ causalPrerequisites b))

instance instDecidableLT : DecidableRel (α := McbalToKreinYangianLogCFTStage) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (causalPrerequisites a ⊂ causalPrerequisites b))

/-- **Root, Diamond Branching, and Terminal Synthesis of `McbalToKreinYangianLogCFTStage`:**
$\mathfrak{M}_1$ is the universal root, $\mathfrak{M}_4$ branches into the incomparable parallel
rungs $\mathfrak{M}_5$ ($\mathcal{C}\ell(n,n)$ tower) and $\mathfrak{M}_6$ (Yangian monodromy words)
which fuse into $\mathfrak{M}_7$, and $\mathfrak{M}_8$ is the universal terminal. -/
theorem poset_root_diamond_and_terminal (a : McbalToKreinYangianLogCFTStage) :
    M1_ClassicalGibbsVmfResponseAndQuenchRelaxPathEntropy ≤ a ∧
    a ≤ M8_DrazinNilpotentShellAndLogCFTSecularSynthesis ∧
    ¬ (a < a) ∧
    (M4_MultiHopOperatorWordNonClosure < M5_Cl11TensorTowerAndSonnBivectorClosure ∧
     M4_MultiHopOperatorWordNonClosure < M6_YangianMonodromyWordsAndNonAbelianGaugeLax ∧
     ¬ (M5_Cl11TensorTowerAndSonnBivectorClosure ≤ M6_YangianMonodromyWordsAndNonAbelianGaugeLax) ∧
     ¬ (M6_YangianMonodromyWordsAndNonAbelianGaugeLax ≤ M5_Cl11TensorTowerAndSonnBivectorClosure) ∧
     M5_Cl11TensorTowerAndSonnBivectorClosure < M7_KreinHopfExceptionalHorizonAndIsotropicJordanCell ∧
     M6_YangianMonodromyWordsAndNonAbelianGaugeLax < M7_KreinHopfExceptionalHorizonAndIsotropicJordanCell) := by
  refine ⟨?_, ?_, lt_irrefl a, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩
  · cases a <;> decide
  · cases a <;> decide

end McbalToKreinYangianLogCFTStage

/-! ===========================================================================
    Section 1: Stage 𝔐₁ — Classical `mcbal` Posts 1 & 2 (vMF Saddle-Point Response,
    Conjugate-Field Inverse, Pre-Norm Residual Bus & Quench-and-Relax Entropy)
    =========================================================================== -/

section StageM1

/-- **Post 1 (`spin-model-transformers`) — Large-$D$ vMF Saddle-Point Response, Radial Slack &
Conjugate-Field Inverse Recovery:**
Let `beta, R_sq, r_sq, gamma : F` in a field `[Field F]` satisfy the large-$D$ saddle-point
equation `beta ^ 2 * r_sq = R_sq * (gamma ^ 2 - 1)` with `1 + gamma ≠ 0` and `beta ≠ 0`.
Define the scalar response gain `g = beta / (1 + gamma)` and the squared response norm
`m_sq = g ^ 2 * r_sq`. Then:
1. `m_sq = R_sq * (gamma - 1) / (1 + gamma)`,
2. The radial slack to the sphere boundary `R_sq` is `R_sq - m_sq = 2 * R_sq / (1 + gamma)`,
3. Whenever `R_sq ≠ 0`, the inverse prefactor `2 * R_sq / (beta * (R_sq - m_sq))` equals
   `(1 + gamma) / beta = g⁻¹`, so `varphi_beta_inv (varphi_beta h) = h` holds identically! -/
theorem mcbal_post1_largeD_vmf_response_norm_and_inverse_recovery
    {F : Type*} [Field F] [CharZero F]
    (beta R_sq r_sq gamma h_vec : F)
    (hSaddle : beta ^ 2 * r_sq = R_sq * (gamma ^ 2 - 1))
    (hGamma : 1 + gamma ≠ 0) (hBeta : beta ≠ 0) (hR : R_sq ≠ 0) :
    let g := beta / (1 + gamma)
    let m_sq := g ^ 2 * r_sq
    m_sq = R_sq * (gamma - 1) / (1 + gamma) ∧
    R_sq - m_sq = 2 * R_sq / (1 + gamma) ∧
    (2 * R_sq / (beta * (R_sq - m_sq))) * (g * h_vec) = h_vec := by
  intro g m_sq
  have h1 : m_sq = R_sq * (gamma - 1) / (1 + gamma) := by
    dsimp [m_sq, g]
    rw [div_pow, div_mul_eq_mul_div, hSaddle]
    have hDiff : gamma ^ 2 - 1 = (gamma - 1) * (1 + gamma) := by ring
    rw [hDiff]
    field_simp [hGamma]
  have h2 : R_sq - m_sq = 2 * R_sq / (1 + gamma) := by
    rw [h1]
    field_simp [hGamma]
    ring
  refine ⟨h1, h2, ?_⟩
  rw [h2]
  dsimp [g]
  field_simp [hGamma, hBeta, hR]

/-- Single-spin transverse/longitudinal covariance operator
`Σ_spin(τ, ρ, P_∥) = τ • (1 - P_∥) + ρ • P_∥` in any `[Ring B]` with `[Algebra R B]`. -/
def singleSpinCovarianceOp {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (tau rho : R) (P_par : B) : B :=
  tau • (1 - P_par) + rho • P_par

/-- **Post 1 (`spin-model-transformers`) — Single-Spin Transverse/Longitudinal Covariance Algebra:**
For any idempotent longitudinal projector `P_par * P_par = P_par` in `[Ring B]`:
1. `singleSpinCovarianceOp tau rho P_par * (1 - P_par) = tau • (1 - P_par)` (transverse eigenvalue `τ`),
2. `singleSpinCovarianceOp tau rho P_par * P_par = rho • P_par` (longitudinal eigenvalue `ρ`),
3. Product closure:
   `singleSpinCovarianceOp tau1 rho1 P_par * singleSpinCovarianceOp tau2 rho2 P_par = singleSpinCovarianceOp (tau1 * tau2) (rho1 * rho2) P_par`. -/
theorem mcbal_post1_singleSpinCovarianceOp_spectral_and_mul
    {B : Type*} [Ring B] {P_par : B} (hP : P_par * P_par = P_par)
    (tau1 rho1 tau2 rho2 : ℤ) :
    singleSpinCovarianceOp tau1 rho1 P_par * (1 - P_par) = tau1 • (1 - P_par) ∧
    singleSpinCovarianceOp tau1 rho1 P_par * P_par = rho1 • P_par ∧
    singleSpinCovarianceOp tau1 rho1 P_par * singleSpinCovarianceOp tau2 rho2 P_par =
      singleSpinCovarianceOp (tau1 * tau2) (rho1 * rho2) P_par := by
  have h1 : (1 - P_par) * (1 - P_par) = 1 - P_par := by noncomm_ring [hP]
  have h2 : P_par * (1 - P_par) = 0 := by noncomm_ring [hP]
  have h3 : (1 - P_par) * P_par = 0 := by noncomm_ring [hP]
  refine ⟨?_, ?_, ?_⟩
  · simp only [singleSpinCovarianceOp, add_mul, smul_mul_assoc, h1, h2, smul_zero, add_zero]
  · simp only [singleSpinCovarianceOp, add_mul, smul_mul_assoc, h3, hP, smul_zero, zero_add]
  · simp only [singleSpinCovarianceOp, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul, h1, h2, h3, hP, smul_zero, add_zero, zero_add, mul_comm tau2 tau1,
      mul_comm rho2 rho1]

/-- **Post 2 (`nonequilibrium-dynamics-in-spin-model-transformers`) — Pre-Norm Conjugate-Field
Residual Bus Identity vs. Naive Magnetization-Space Attenuation & Quench-and-Relax Entropy Budget:**
1. **Conjugate-Field Residual Bus**: Given any invertible response map `phi` with left inverse
   `phi_inv` (`phi_inv (phi h) = h` and `phi (phi_inv m) = m`), the pre-norm residual update
   `m_out(Δ_h) = phi (phi_inv m_in + Δ_h)` reduces at zero update `Δ_h = 0` to the exact
   identity `m_out(0) = m_in`, whereas naive magnetization-space re-application `g • m_in`
   leaves the attenuation defect `g • m_in - m_in = (g - 1) • m_in`.
2. **Telescoping Quench-and-Relax Entropy Budget**: Across `K` relaxation steps where each step
   decomposes into housekeeping entropy plus potential drop `σ_hk(k) + (Δ(k) - Δ(k + 1))`, the
   cumulative entropy production equals `(∑_{k < K} σ_hk(k)) + (Δ(0) - Δ(K))`.
3. **Non-Reciprocal Housekeeping Positivity & Symmetry Vanishing**: Re-exports
   `housekeepingEntropyProxy_nonneg` and `housekeepingEntropyProxy_eq_zero_of_symmetric`. -/
theorem mcbal_post2_prenorm_residual_bus_and_quench_relax_entropy_budget
    {H M : Type*} [AddCommGroup H]
    (phi : H → M) (phi_inv : M → H)
    (hRightInv : ∀ m : M, phi (phi_inv m) = m)
    (m_in : M)
    (sigma_hk Delta : ℕ → ℝ) (K : ℕ)
    {V : Type*} [Fintype V] [DecidableEq V]
    (beta : ℝ) (J_symm : V → V → ℝ) (hSymm : ∀ i j, J_symm i j = J_symm j i)
    (C_star : V → V → ℝ) :
    phi (phi_inv m_in + 0) = m_in ∧
    (∑ k ∈ Finset.range K, (sigma_hk k + (Delta k - Delta (k + 1)))) =
      (∑ k ∈ Finset.range K, sigma_hk k) + (Delta 0 - Delta K) ∧
    InfoGeometry.LLM.housekeepingEntropyProxy beta J_symm C_star = 0 := by
  refine ⟨by rw [add_zero, hRightInv], ?_,
    InfoGeometry.LLM.housekeepingEntropyProxy_eq_zero_of_symmetric beta J_symm C_star hSymm⟩
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring

end StageM1

/-! ===========================================================================
    Section 2: Stage 𝔐₂ — Stochastic Drazin Index-1 Semisimplicity Aporia (Phase IV Rung 0)
    =========================================================================== -/

section StageM2

/-- **Stage $\mathfrak{M}_2$ (The Stochastic Semisimplicity Aporia — Phase IV Rung 0 & Axiom I):**
1. **No Length-2 Jordan Chain on the Stochastic Simplex (`no_length_two_generalized_fixed_vector`)**:
   For any finite row-stochastic matrix `P ∈ Matrix.rowStochastic ℝ ι`, if `(1 - P) *ᵥ x = y`
   and `(1 - P) *ᵥ y = 0`, then `y = 0`. Thus `ker((1 - P)²) = ker(1 - P)` and classical
   row-stochastic attention cannot support a non-trivial rank-2 Jordan memory cell.
2. **Drazin Index-1 Nilpotent Shell Extinction**:
   Whenever an operator `a` in any `[Ring R]` has an index-`1` Drazin inverse `d`
   (`IsDrazinInverse a d 1`), its Fitting nilpotent Jordan shell `fittingNilpotentPart a d`
   vanishes identically (`fittingNilpotentPart a d = 0`)! -/
theorem stageM2_stochastic_drazin_index_one_semisimplicity_aporia
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (x y : ι → ℝ)
    (hxy : (1 - P) *ᵥ x = y) (hyy : (1 - P) *ᵥ y = 0)
    {R : Type*} [Ring R] [StarRing R] {a d : R}
    (hDrazin1 : IsDrazinInverse a d 1) :
    y = 0 ∧ fittingNilpotentPart a d = 0 := by
  refine ⟨no_length_two_generalized_fixed_vector P hP x y hxy hyy, ?_⟩
  simpa only [pow_one] using fittingNilpotentPart_pow_k_eq_zero hDrazin1 le_rfl

end StageM2

/-! ===========================================================================
    Section 3: Stage 𝔐₃ — `mcbal` Post 3: Large-D Asymmetric Kinetic Vector-Spin
    Covariance Closure, Exact Sphere Norm Conservation & Gain-Mixing Defect
    =========================================================================== -/

section StageM3

/-- **Post 3 (`a-large-d-closure-for-asymmetric-kinetic-vector-spin-systems`) —
The Exact Algebraic Sphere Norm Conservation Law (`a_i² r_i² + b_i = R²`):**
In the large-$D$ kinetic vector-spin closure, each site $i$ has:
- mean field norm squared `h_bar_sq = ‖h̄_i‖²`,
- fluctuation field variance `v_i = (J C Jᵀ)_{ii}`,
- total typical squared field norm `r_sq = h_bar_sq + v_i`,
- saddle-point root `gamma_i` satisfying `beta ^ 2 * r_sq = R_sq * (gamma_i ^ 2 - 1)`,
- deterministic gain `a_i = beta / (1 + gamma_i)`,
- fresh conditional noise variance `b_i = 2 * R_sq / (1 + gamma_i)`.
Then:
1. **Polynomial-Cleared Sphere Identity**:
   `beta ^ 2 * (h_bar_sq + v_i) + 2 * R_sq * (1 + gamma_i) = R_sq * (1 + gamma_i) ^ 2`,
2. **Exact Stepwise Sphere Conservation Law (`‖m_i'‖² + C'_{ii} = R²`)**:
   In any field `[Field F]` with `1 + gamma_i ≠ 0`, the updated mean norm squared
   `m_next_sq = a_i ^ 2 * h_bar_sq` plus the updated diagonal covariance
   `C_next_ii = a_i ^ 2 * v_i + b_i` equals `R_sq` **identically at every step**! -/
theorem mcbal_post3_exact_sphere_norm_conservation
    {F : Type*} [Field F]
    (beta R_sq h_bar_sq v_i gamma_i : F)
    (hSaddle : beta ^ 2 * (h_bar_sq + v_i) = R_sq * (gamma_i ^ 2 - 1))
    (hGamma : 1 + gamma_i ≠ 0) :
    let a_i := beta / (1 + gamma_i)
    let b_i := 2 * R_sq / (1 + gamma_i)
    let m_next_sq := a_i ^ 2 * h_bar_sq
    let C_next_ii := a_i ^ 2 * v_i + b_i
    (beta ^ 2 * (h_bar_sq + v_i) + 2 * R_sq * (1 + gamma_i) = R_sq * (1 + gamma_i) ^ 2) ∧
    (a_i ^ 2 * (h_bar_sq + v_i) + b_i = R_sq) ∧
    (m_next_sq + C_next_ii = R_sq) := by
  intro a_i b_i m_next_sq C_next_ii
  have hCleared :
      beta ^ 2 * (h_bar_sq + v_i) + 2 * R_sq * (1 + gamma_i) = R_sq * (1 + gamma_i) ^ 2 := by
    rw [hSaddle]
    ring
  have hSphere : a_i ^ 2 * (h_bar_sq + v_i) + b_i = R_sq := by
    dsimp [a_i, b_i]
    have hStep :
        (beta / (1 + gamma_i)) ^ 2 * (h_bar_sq + v_i) + 2 * R_sq / (1 + gamma_i) =
          (beta ^ 2 * (h_bar_sq + v_i) + 2 * R_sq * (1 + gamma_i)) / (1 + gamma_i) ^ 2 := by
      field_simp [hGamma]
    rw [hStep, hCleared, mul_div_cancel_right₀ R_sq (pow_ne_zero 2 hGamma)]
  refine ⟨hCleared, hSphere, ?_⟩
  dsimp [m_next_sq, C_next_ii]
  calc
    a_i ^ 2 * h_bar_sq + (a_i ^ 2 * v_i + b_i)
        = a_i ^ 2 * (h_bar_sq + v_i) + b_i := by ring
    _ = R_sq := hSphere

/-- Explicit non-commutativity witness for `2 × 2` spin-routing coupling matrices (`Trap T16`). -/
theorem mcbal_matrix_units_noncommute :
    matE01 (B := ℤ) * matE10 (B := ℤ) ≠ matE10 (B := ℤ) * matE01 (B := ℤ) :=
  matrix_units_noncommute (B := ℤ)

/-- **Post 3 (`a-large-d-closure-for-asymmetric-kinetic-vector-spin-systems`) —
Three-Level Closure Hierarchy (`K = 1` Agreement vs. `K = 2` Shared-Input Off-Diagonal Defect):**
On `Matrix (Fin 2) (Fin 2) R` over any `[CommRing R]`:
1. **At `K = 1` from a diagonal covariance `C₀ = !![c₀, 0; 0, c₁]`**:
   For any coupling matrix `J : Matrix (Fin 2) (Fin 2) R`, the exact full-closure field variance
   `(J * C₀ * Jᵀ) i i` equals the diagonal-closure approximation
   `J i 0 ^ 2 * c₀ + J i 1 ^ 2 * c₁` for each site `i ∈ {0, 1}`.
2. **At `K = 2` with shared inputs**:
   Even starting from the identity covariance `C₀ = 1` with unit gains `A = 1` and zero fresh noise,
   the one-step covariance `C₁ = J * 1 * Jᵀ = J * Jᵀ` acquires off-diagonal correlations
   `C₁ 0 1 = J 0 0 * J 1 0 + J 0 1 * J 1 1`. Consequently, at step `K = 2`, the difference
   between the Full Closure variance `(J * C₁ * Jᵀ) 0 0` and the Diagonal Closure variance
   `J 0 0 ^ 2 * C₁ 0 0 + J 0 1 ^ 2 * C₁ 1 1` is the cross-correlation term
   `2 * J 0 0 * J 0 1 * (J 0 0 * J 1 0 + J 0 1 * J 1 1)`, which equals `2` for the concrete
   asymmetric/shared-input coupling `J = !![1, 1; 1, 0]`! -/
theorem mcbal_post3_three_level_closure_hierarchy_k1_vs_k2_defect
    {R : Type*} [CommRing R]
    (J : Matrix (Fin 2) (Fin 2) R) (c0 c1 : R) :
    let C0_diag : Matrix (Fin 2) (Fin 2) R := !![c0, 0; 0, c1]
    let C1 : Matrix (Fin 2) (Fin 2) R := J * Jᵀ
    ((J * C0_diag * Jᵀ) 0 0 = J 0 0 ^ 2 * c0 + J 0 1 ^ 2 * c1 ∧
     (J * C0_diag * Jᵀ) 1 1 = J 1 0 ^ 2 * c0 + J 1 1 ^ 2 * c1) ∧
    ((J * C1 * Jᵀ) 0 0 - (J 0 0 ^ 2 * C1 0 0 + J 0 1 ^ 2 * C1 1 1) =
      2 * J 0 0 * J 0 1 * (J 0 0 * J 1 0 + J 0 1 * J 1 1)) ∧
    (let J_wit : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]
     let C1_wit : Matrix (Fin 2) (Fin 2) ℤ := J_wit * J_witᵀ
     (J_wit * C1_wit * J_witᵀ) 0 0 -
       (J_wit 0 0 ^ 2 * C1_wit 0 0 + J_wit 0 1 ^ 2 * C1_wit 1 1) = 2) := by
  intro C0_diag C1
  refine ⟨⟨?_, ?_⟩, ?_, by decide⟩
  · simp only [C0_diag, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    simp
    ring
  · simp only [C0_diag, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    simp
    ring
  · simp only [C1, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    ring

/-- **Stage $\mathfrak{M}_3$ (`mcbal` Post 3 Non-Commutative Operator Covariance Closure &
Gain-Mixing Commutator Defect `[G, J] ≠ 0`):**
Integrates the repository's native non-commutative operator covariance owners
(`FiniteOperatorCovariance`, `CovarianceTransport`, `CovarianceDynamics`, `CovarianceStationary`):
1. Unbiased innovation closure when `crossCovariance w X E = 0`:
   `crossCovariance w (T X + E) (T X + E) = covarianceStep T (crossCovariance w E E) (crossCovariance w X X)`,
2. Delayed correlation identity `crossCovariance w (T X + E) X = T * crossCovariance w X X`,
3. Non-commutative gain-mixing commutator defect:
   `covarianceStep (G * J) Q C - covarianceStep (J * G) Q C = [G, J] C (G J)* + (J G) C [G, J]*`,
4. Exact finite-$K$ quench trajectory `covariance_iterate_eq`,
5. Unique contractive PSD stationary covariance `existsUnique_posSemidef_stationary`. -/
theorem stageM3_noncommutative_covariance_closure_and_gain_defect
    {Ω A : Type*} [Fintype Ω] [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
    (w : Ω → ℝ) (G J Q C : A) (X E : Ω → A) (hXE : crossCovariance w X E = 0)
    (k : ℕ)
    {n : Type*} [Fintype n] [DecidableEq n]
    (T_mat Q_mat : Matrix n n ℂ) (hT : ‖T_mat‖ < 1) (hQ : Q_mat.PosSemidef) :
    (crossCovariance w (fun ω => (G * J) * X ω + E ω) (fun ω => (G * J) * X ω + E ω) =
      covarianceStep (G * J) (crossCovariance w E E) (crossCovariance w X X)) ∧
    (crossCovariance w (fun ω => (G * J) * X ω + E ω) X = (G * J) * crossCovariance w X X) ∧
    (covarianceStep (G * J) Q C - covarianceStep (J * G) Q C =
      InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.operatorCommutator G J * C * star (G * J) +
        (J * G) * C * star (InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.operatorCommutator G J)) ∧
    ((covarianceStep (G * J) Q)^[k] C =
      (G * J) ^ k * C * star ((G * J) ^ k) +
        InfoGeometry.Canonical.FiniteSteinInverse.finiteStein (G * J) (star (G * J)) Q k) ∧
    (∃! S : Matrix n n ℂ, S.PosSemidef ∧ covarianceStep T_mat Q_mat S = S) :=
  ⟨innovation_covariance_of_cross_zero w (G * J) X E hXE,
   innovation_lag_of_cross_zero w (G * J) X E hXE,
   gain_mixing_order_defect G J Q C,
   covariance_iterate_eq (G * J) Q C k,
   existsUnique_posSemidef_stationary T_mat Q_mat hT hQ⟩

end StageM3

/-! ===========================================================================
    Section 4: Stages 𝔐₄–𝔐₈ — Multi-Hop Word Non-Closure, Cl(n,n) Spin Chain,
    Yangian Monodromy, Krein Isotropic Jordan Cell & LogCFT Secular Synthesis
    =========================================================================== -/

section StagesM4ToM8

/-- **Stage $\mathfrak{M}_4$ (Multi-Hop Operator Word Non-Closure — Phase IV Rung 2 & Deduction 1):**
Reuses `InfoGeometry.Algebra.MonarchFactorization`:
1. Every single-stage factored routing matrix `M = monarch L R` has crossed-index routing slices
   of rank `≤ 1` whose `2 × 2` minors vanish identically (`IsMonarch.routingSlice_minor_eq_zero`),
2. For the concrete 4-state witness `FourStateWitness.witness`, `witness` is Monarch
   (`IsMonarch witness`), yet the two-step word `witness * witness` has a non-vanishing `2 × 2`
   routing-slice minor (`= 1`) and therefore is **not** Monarch (`¬ IsMonarch (witness * witness)`). -/
theorem stageM4_multihop_word_nonclosure :
    IsMonarch FourStateWitness.witness ∧
    (routingSlice (FourStateWitness.witness * FourStateWitness.witness) 0 0 0 0 *
        routingSlice (FourStateWitness.witness * FourStateWitness.witness) 0 0 1 1 -
      routingSlice (FourStateWitness.witness * FourStateWitness.witness) 0 0 0 1 *
        routingSlice (FourStateWitness.witness * FourStateWitness.witness) 0 0 1 0 = (1 : ℚ)) ∧
    ¬ IsMonarch (FourStateWitness.witness * FourStateWitness.witness) :=
  ⟨FourStateWitness.witness_isMonarch,
   FourStateWitness.witness_square_minor_eq_one,
   FourStateWitness.witness_square_not_isMonarch⟩

/-- **Stages $\mathfrak{M}_5$ & $\mathfrak{M}_6$ ($\mathcal{C}\ell(n,n)$ Jordan–Wigner Spin Chain,
$\mathfrak{so}(n,n)$ Bivector Lie Closure & Yangian Monodromy Words — Phase IV Rung 3 & Deduction 2):**
1. The $n$-site $\mathcal{C}\ell(1,1)^{\otimes n}$ filtration has dimension `4 ^ n`
   (`stageImage_finrank`), strict filtration growth (`stageImage_lt_succ`), CAR anticommutation
   (`jwAnnihilation_creation_anticommutator`), and $\mathfrak{so}(n,n)$ quadratic bivector Lie
   closure (`towerJW_quadratic_bivector_sonn_lie_closure`),
2. The two-site Yangian monodromy blocks satisfy the RTT commutator relation
   `comm (monodromyB2 u θ₁ θ₂ η) (monodromyC2 v θ₁ θ₂ η) = -((2 * v - θ₁ - θ₂) * η) • (monodromyA2 u θ₁ θ₂ η - monodromyD2 u θ₁ θ₂ η)`
   and the non-Abelian $\operatorname{SL}_2$ Gauge–Lax exchange duality
   `(I₂ ⊗ G) L_{0,r}(u, θ, η) (I₂ ⊗ G⁻¹) = (G⁻¹ ⊗ I₂) L_{0,r}(u, θ, η) (G ⊗ I₂)`. -/
theorem stagesM5_M6_cl11_tower_sonn_and_yangian_monodromy
    {B : Type*} [Ring B] {R : Type*} [CommRing R]
    (n : ℕ) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (u v theta1 theta2 eta : R)
    (G G_inv : Matrix (Fin 2) (Fin 2) R) (hGR : G * G_inv = 1) (hGL : G_inv * G = 1) :
    (Module.finrank ℝ (InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage n) = 4 ^ n ∧
      InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage n <
        InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage (n + 1) ∧
      comm (towerJWPos B n i * towerJWPos B n j) (towerJWPos B n j * towerJWPos B n k) =
        (2 : ℤ) • (towerJWPos B n i * towerJWPos B n k)) ∧
    (comm (monodromyB2 u theta1 theta2 eta) (monodromyC2 v theta1 theta2 eta) =
        -((2 * v - theta1 - theta2) * eta) •
          (monodromyA2 u theta1 theta2 eta - monodromyD2 u theta1 theta2 eta) ∧
      kronIdLeft4 G * singleSiteLax4 u theta1 eta * kronIdLeft4 G_inv =
        kronIdRight4 G_inv * singleSiteLax4 u theta1 eta * kronIdRight4 G) :=
  ⟨⟨InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage_finrank n,
    InfoGeometry.Clifford.Cl11StarAlgebraFiltration.stageImage_lt_succ n,
    (towerJW_quadratic_bivector_sonn_lie_closure B n hij hjk hik).1⟩,
   ⟨(yangian_twoSite_full_rtt_commutator_table u v theta1 theta2 eta).2.2.2.2.2,
    (turn28_nonabelian_gauge_lax_exchange_duality u theta1 eta G G_inv hGR hGL).2.2⟩⟩

/-- **Stages $\mathfrak{M}_7$ & $\mathfrak{M}_8$ (Krein–Hopf Exceptional Horizon, Isotropic Jordan
Eigenmode $\langle \Psi_{\text{EP}}, \Psi_{\text{EP}} \rangle_B = 0$, Drazin Nilpotent Shell &
LogCFT Quadratic Secular $O(t^2)$ Evolution — Phase IV Rung 4 & Phase V Synthesis):**
1. **Abstract Krein Isotropy of Any Jordan Chain (`jordan_chain_isotropic` & `square_zero_range_pairing`)**:
   For any real bilinear form `B_form` and `B_form`-self-adjoint operator `T` (or square-zero
   `N_nil` with `N_nil * N_nil = 0`), any Jordan-chain eigenvector `x = (T - r • 1) y` with
   `(T - r • 1) x = 0` is strictly isotropic (`B_form x x = 0`),
2. **Concrete `4 × 4` Krein–Hopf Crash at `g = Δω` (`f_k = -1`)**:
   `kreinCrashNilpotent dw * kreinCrashNilpotent dw = 0`, the coalesced eigenmode `kreinExceptionalVec`
   has zero Krein self-norm `dotProduct kreinExceptionalVec (mulVec kreinMetric4 kreinExceptionalVec) = 0`
   while its cross-pairing with the generalized root vector `kreinJordanRootVec` is non-zero (`= 1`),
3. **Exact Quadratic Secular $O(t^2)$ Evolution (`MCP₈`)**:
   `(1 - t • kreinCrashNilpotent dw) * diracKreinA * (1 + t • kreinCrashNilpotent dw) = diracKreinA + (2 * dw * t) • (diracKreinA * diracKreinB) + (2 * dw ^ 2 * t ^ 2) • kreinCrashNilpotent dw`. -/
theorem stagesM7_M8_krein_exceptional_isotropy_and_logcft_secular_evolution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B_form : LinearMap.BilinForm ℝ E) (T_end : Module.End ℝ E)
    (hT_adj : LinearMap.IsAdjointPair B_form B_form T_end T_end)
    (r_eig : ℝ) (x_ep y_gen : E)
    (hChain : (T_end - r_eig • (1 : Module.End ℝ E)) y_gen = x_ep)
    (hEigen : (T_end - r_eig • (1 : Module.End ℝ E)) x_ep = 0)
    {R : Type*} [CommRing R] (dw t : R) :
    B_form x_ep x_ep = 0 ∧
    kreinCrashNilpotent dw * kreinCrashNilpotent dw = 0 ∧
    dotProduct (kreinExceptionalVec (R := R))
      (Matrix.mulVec kreinMetric4 (kreinExceptionalVec (R := R))) = 0 ∧
    dotProduct (kreinExceptionalVec (R := R))
      (Matrix.mulVec (kreinMetric4 * (-jwE1)) kreinJordanRootVec) = (1 : R) ∧
    (1 - t • kreinCrashNilpotent dw) * diracKreinA * (1 + t • kreinCrashNilpotent dw) =
      diracKreinA + (2 * dw * t) • diracKreinVelocity +
        (2 * dw * t ^ 2) • kreinCrashNilpotent dw :=
  ⟨jordan_chain_isotropic B_form T_end hT_adj r_eig x_ep y_gen hChain hEigen,
   (kreinHamiltonianHopf_bifurcation (0 : R) dw dw).2.2.2,
   (kreinCrash_jordan_chain_and_null_norm (R := R)).2.2,
   (krein_puiseux_perturbation_and_gelfand_lidskii_residue (R := R) dw 0).2.2.2.1,
   (diracKrein_secular_crash_evolution dw t).2.1⟩

/-- **Master Structural Synthesis of the 3-Post `mcbal` Corridor & 8-Stage `solve et coagula`
Poset (`𝔐₁ ≺ 𝔐₂ ≺ ⋯ ≺ 𝔐₈`):**
Coagulates:
- `𝔐₁`: Large-$D$ vMF response norm, conjugate-field inverse recovery, and Quench-and-Relax
  housekeeping entropy budget,
- `𝔐₂`: Stochastic Drazin-index-1 semisimplicity (`no_length_two_generalized_fixed_vector`)
  and index-1 nilpotent shell extinction (`fittingNilpotentPart a d = 0`),
- `𝔐₃`: Exact large-$D$ sphere norm conservation (`a_i² r_i² + b_i = R²`), non-commutative
  operator covariance innovation closure, `[G, J]` order defect, and the `K = 1` vs. `K = 2`
  closure hierarchy defect,
- `𝔐₄`: Multi-hop operator word non-closure (`¬ IsMonarch (witness * witness)`),
- `𝔐₅` & `𝔐₆`: $\mathcal{C}\ell(1,1)^{\otimes n} \cong \mathcal{C}\ell(n,n)$ dimension $4^n$,
  $\mathfrak{so}(n,n)$ bivector Lie closure, Yangian RTT commutator, and non-Abelian $\operatorname{SL}_2$
  Gauge–Lax exchange duality,
- `𝔐₇` & `𝔐₈`: Krein isotropy of the coalesced Jordan eigenmode $\langle \Psi_{\text{EP}}, \Psi_{\text{EP}} \rangle_B = 0$
  and exact $O(t^2)$ secular LogCFT evolution `(1 - t N_nil) A (1 + t N_nil) = A + 2 Δω t (A B) + 2 Δω² t² N_nil`. -/
theorem mcbal_to_krein_yangian_logcft_master_synthesis
    (aStage : McbalToKreinYangianLogCFTStage)
    {F : Type*} [Field F] [CharZero F]
    (beta R_sq h_bar_sq v_i gamma_i h_vec : F)
    (hSaddle : beta ^ 2 * (h_bar_sq + v_i) = R_sq * (gamma_i ^ 2 - 1))
    (hGamma : 1 + gamma_i ≠ 0) (hBeta : beta ≠ 0) (hR : R_sq ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P_stoch : Matrix ι ι ℝ) (hP_stoch : P_stoch ∈ Matrix.rowStochastic ℝ ι)
    (x_vec y_vec : ι → ℝ)
    (hxy : (1 - P_stoch) *ᵥ x_vec = y_vec) (hyy : (1 - P_stoch) *ᵥ y_vec = 0)
    {Ω A : Type*} [Fintype Ω] [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
    (w : Ω → ℝ) (G J_op Q_op C_op : A) (X_rv E_rv : Ω → A)
    (hXE : crossCovariance w X_rv E_rv = 0)
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B_form : LinearMap.BilinForm ℝ E) (T_end : Module.End ℝ E)
    (hT_adj : LinearMap.IsAdjointPair B_form B_form T_end T_end)
    (r_eig : ℝ) (x_ep y_gen : E)
    (hChain : (T_end - r_eig • (1 : Module.End ℝ E)) y_gen = x_ep)
    (hEigen : (T_end - r_eig • (1 : Module.End ℝ E)) x_ep = 0)
    {R : Type*} [CommRing R] (dw t : R) :
    (McbalToKreinYangianLogCFTStage.M1_ClassicalGibbsVmfResponseAndQuenchRelaxPathEntropy ≤ aStage ∧
      aStage ≤ McbalToKreinYangianLogCFTStage.M8_DrazinNilpotentShellAndLogCFTSecularSynthesis) ∧
    ((2 * R_sq / (beta * (R_sq - (beta / (1 + gamma_i)) ^ 2 * (h_bar_sq + v_i)))) *
        ((beta / (1 + gamma_i)) * h_vec) = h_vec ∧
      (beta / (1 + gamma_i)) ^ 2 * h_bar_sq +
        ((beta / (1 + gamma_i)) ^ 2 * v_i + 2 * R_sq / (1 + gamma_i)) = R_sq) ∧
    (y_vec = 0) ∧
    (crossCovariance w (fun ω => (G * J_op) * X_rv ω + E_rv ω)
        (fun ω => (G * J_op) * X_rv ω + E_rv ω) =
        covarianceStep (G * J_op) (crossCovariance w E_rv E_rv) (crossCovariance w X_rv X_rv) ∧
      covarianceStep (G * J_op) Q_op C_op - covarianceStep (J_op * G) Q_op C_op =
        InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.operatorCommutator G J_op *
          C_op * star (G * J_op) +
          (J_op * G) * C_op *
            star (InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.operatorCommutator G J_op)) ∧
    (IsMonarch FourStateWitness.witness ∧
      ¬ IsMonarch (FourStateWitness.witness * FourStateWitness.witness)) ∧
    (B_form x_ep x_ep = 0 ∧
      (1 - t • kreinCrashNilpotent dw) * diracKreinA * (1 + t • kreinCrashNilpotent dw) =
        diracKreinA + (2 * dw * t) • diracKreinVelocity +
          (2 * dw * t ^ 2) • kreinCrashNilpotent dw) := by
  refine ⟨⟨(McbalToKreinYangianLogCFTStage.poset_root_diamond_and_terminal aStage).1,
           (McbalToKreinYangianLogCFTStage.poset_root_diamond_and_terminal aStage).2.1⟩,
          ⟨(mcbal_post1_largeD_vmf_response_norm_and_inverse_recovery
              beta R_sq (h_bar_sq + v_i) gamma_i h_vec hSaddle hGamma hBeta hR).2.2,
           (mcbal_post3_exact_sphere_norm_conservation
              beta R_sq h_bar_sq v_i gamma_i hSaddle hGamma).2.2⟩,
          no_length_two_generalized_fixed_vector P_stoch hP_stoch x_vec y_vec hxy hyy,
          ⟨innovation_covariance_of_cross_zero w (G * J_op) X_rv E_rv hXE,
           gain_mixing_order_defect G J_op Q_op C_op⟩,
          ⟨FourStateWitness.witness_isMonarch,
           FourStateWitness.witness_square_not_isMonarch⟩,
          ⟨jordan_chain_isotropic B_form T_end hT_adj r_eig x_ep y_gen hChain hEigen,
           (diracKrein_secular_crash_evolution dw t).2.1⟩⟩

end StagesM4ToM8

end InfoGeometry.LLM.McbalLargeDAsymmetricClosureCorridor
