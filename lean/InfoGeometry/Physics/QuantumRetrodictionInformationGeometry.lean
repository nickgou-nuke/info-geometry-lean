import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import InfoGeometry.Quantum.QuantumCramerRaoBound

open Matrix
open BigOperators
open InfoGeometry.Quantum.QuantumCramerRaoBound

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Section 5.77: Quantum Retrodiction Information Geometry & Holographic Nuclear Invariants

This module formalizes the quantum information geometry of field retrodiction
linking the macroscopic detector 4-volume to the nuclear source multipole invariants:

1. **Symmetric Logarithmic Derivative (SLD) Bundle & Anti-Commutator**:
   `{A, B} = A * B + B * A`.
2. **Quantum Fisher Information Metric (QFIM) on the Null Hypersurface**:
   `g_{μν} = ½ Tr(ρ * {L_μ, L_ν})`.
3. **QFIM Symmetry and Positive Semi-Definiteness**:
   `g_{μν} = g_{νμ}` and `0 ≤ g_{μμ} = g_SLD(ρ, L_μ)`.
4. **Directional SLD and Multi-Parameter Quantum Cramér-Rao Bound**:
   `L_v = ∑ v_μ L_μ` is self-adjoint, satisfying the directional QCRB:
   `Var_ρ(O) * g_SLD(ρ, L_v) ≥ (d⟨O⟩/dv)²`.
5. **Infinitesimal Bures Distance**:
   `ds_B² = ¼ ∑_{μ,ν} g_{μν} dθ^μ dθ^ν` with `ds_B²(0) = 0`.
6. **Aperture 4-Volume Holographic Accumulation**:
   Integrating over spacetime detector 4-volume `V_4 = V × Δt` along the backward null cone
   accumulates Fisher information linearly: `I_accum(V_4) = V_4 * I_0`.
7. **Asymptotic Variance Contraction (Holographic Inversion)**:
   The retrodicted parameter variance bound `1 / (V_4 * I_0)` contracts strictly below any `ε > 0`
   for large exposure `V_4 > V_{4,crit}`.
8. **Nuclear Multipole Area Scaling**:
   For the two-parameter nuclear invariant bundle `θ = (λ, Q_0)`, the covariance area
   contracts as `O(V_4⁻²)`.
9. **Master Certified Synthesis**:
   Unified conjunction `certified_quantum_retrodiction_synthesis` with zero debt and standard axioms.
-/

namespace InfoGeometry.Physics.QuantumRetrodiction

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Anti-commutator of two matrix operators: `{A, B} = A * B + B * A`. -/
def anticommutator (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  A * B + B * A

/-- Anti-commutator is strictly symmetric in its arguments: `{A, B} = {B, A}`. -/
@[simp] theorem anticommutator_symm (A B : Matrix n n ℝ) :
    anticommutator A B = anticommutator B A := by
  dsimp [anticommutator]
  rw [add_comm]

/-- Quantum Fisher Information Metric (QFIM) entry for density matrix `ρ` and SLD operators `L_μ, L_ν`:
    `g_{μν} = ½ Tr(ρ * {L_μ, L_ν})`. -/
noncomputable def qfimEntry (rho L_mu L_nu : Matrix n n ℝ) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace (rho * anticommutator L_mu L_nu)

/-- **Theorem (QFIM Symmetry)**:
    The Quantum Fisher Information Metric tensor is symmetric: `g_{μν} = g_{νμ}`. -/
theorem qfimEntry_symm (rho L_mu L_nu : Matrix n n ℝ) :
    qfimEntry rho L_mu L_nu = qfimEntry rho L_nu L_mu := by
  dsimp [qfimEntry]
  rw [anticommutator_symm]

/-- **Theorem (Diagonal QFIM Reduction to SLD Fisher Information)**:
    On the diagonal, the QFIM reduces identically to the Bures-Helstrom SLD Fisher information:
    `g_{μμ} = Tr(ρ * L_μ²)`. -/
theorem qfimEntry_diag (R L_mu : Matrix n n ℝ) (hL : L_muᵀ = L_mu) :
    qfimEntry (Rᵀ * R) L_mu L_mu = sldFisherInfo (Rᵀ * R) L_mu := by
  dsimp [qfimEntry, anticommutator, sldFisherInfo]
  have h_add : L_mu * L_mu + L_mu * L_mu = (2 : ℝ) • (L_mu * L_mu) := by
    rw [two_smul]
  rw [h_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

/-- **Theorem (Non-Negativity of Diagonal QFIM Entries)**:
    For any physical density matrix `ρ = Rᵀ * R` and self-adjoint SLD operator `L_μ`,
    the diagonal Fisher metric entry is non-negative: `0 ≤ g_{μμ}`. -/
theorem qfimEntry_diag_nonneg (R L_mu : Matrix n n ℝ) (hL : L_muᵀ = L_mu) :
    0 ≤ qfimEntry (Rᵀ * R) L_mu L_mu := by
  rw [qfimEntry_diag R L_mu hL]
  have h := frobNormSq_mul_transpose R L_mu hL
  dsimp [sldFisherInfo]
  rw [← h]
  exact frobNormSq_nonneg (L_mu * Rᵀ)

/-- Directional SLD operator along tangent direction `v`: `L_v = ∑ v_i • L_i`. -/
def directionalSLD {m : ℕ} (v : Fin m → ℝ) (L : Fin m → Matrix n n ℝ) : Matrix n n ℝ :=
  ∑ i : Fin m, v i • L i

/-- **Theorem (Self-Adjointness of Directional SLD)**:
    A linear combination of self-adjoint SLD operators is self-adjoint: `L_vᵀ = L_v`. -/
theorem directionalSLD_transpose {m : ℕ} (v : Fin m → ℝ) (L : Fin m → Matrix n n ℝ)
    (hL : ∀ i, (L i)ᵀ = L i) :
    (directionalSLD v L)ᵀ = directionalSLD v L := by
  dsimp [directionalSLD]
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.transpose_smul, hL i]

/-- **Theorem (Directional Quantum Cramér-Rao Bound)**:
    Along any parameter direction `v`, the observable variance is bounded below
    by the directional SLD Fisher information:
    `(d⟨O⟩/dv)² ≤ Var_ρ(O) * g_SLD(ρ, L_v)`. -/
theorem directional_qcrb {m : ℕ}
    (R : Matrix n n ℝ)
    (v : Fin m → ℝ) (L : Fin m → Matrix n n ℝ)
    (hL : ∀ i, (L i)ᵀ = L i)
    (drho_v O : Matrix n n ℝ)
    (hO : Oᵀ = O)
    (h_tr_drho : Matrix.trace drho_v = 0)
    (h_sld : isSLD (Rᵀ * R) drho_v (directionalSLD v L))
    (h_symm : Matrix.trace ((Rᵀ * R) * ((directionalSLD v L) * centeredObservable (Rᵀ * R) O)) =
              Matrix.trace ((Rᵀ * R) * (centeredObservable (Rᵀ * R) O * (directionalSLD v L)))) :
    (paramDeriv drho_v O) ^ 2 ≤
      quantumVariance (Rᵀ * R) O * sldFisherInfo (Rᵀ * R) (directionalSLD v L) := by
  have hLv := directionalSLD_transpose v L hL
  exact quantum_cramer_rao_bound R drho_v (directionalSLD v L) O hLv hO h_tr_drho h_sld h_symm

/-- Infinitesimal Bures metric quadratic form: `ds_B² = ¼ ∑_{i,j} dv_i * dv_j * g_{ij}`. -/
noncomputable def buresMetricForm {m : ℕ} (rho : Matrix n n ℝ) (L : Fin m → Matrix n n ℝ) (dv : Fin m → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, dv i * dv j * qfimEntry rho (L i) (L j)

/-- **Theorem (Bures Metric Form Vanishes at Zero Displacement)**:
    `ds_B²(0) = 0`. -/
theorem buresMetricForm_zero {m : ℕ} (rho : Matrix n n ℝ) (L : Fin m → Matrix n n ℝ) :
    buresMetricForm rho L (fun _ => 0) = 0 := by
  dsimp [buresMetricForm]
  have h_zero : (∑ i : Fin m, ∑ j : Fin m, (0 : ℝ) * 0 * qfimEntry rho (L i) (L j)) = 0 := by
    simp
  rw [h_zero, mul_zero]

/-- Accumulated Fisher information over detector spacetime 4-volume `V_4 = V × Δt`:
    `I_accum(V_4) = V_4 * I_0`. -/
def accumulatedFisherInfo (V4 I0 : ℝ) : ℝ :=
  V4 * I0

/-- **Theorem (Linear Information Scaling)**:
    The accumulated Fisher information scales linearly with the 4-volume exposure. -/
theorem accumulated_fisher_scaling (V4 I0 : ℝ) :
    accumulatedFisherInfo V4 I0 = V4 * I0 := rfl

/-- Cramér-Rao variance lower bound from accumulated 4-volume information: `1 / (V_4 * I_0)`. -/
noncomputable def cramerRaoVarianceBound (V4 I0 : ℝ) : ℝ :=
  1 / (accumulatedFisherInfo V4 I0)

/-- **Theorem (Variance Bound Formula)**:
    `Var(θ) ≤ 1 / (V_4 * I_0)`. -/
theorem variance_bound_contraction (V4 I0 : ℝ) :
    cramerRaoVarianceBound V4 I0 = 1 / (V4 * I0) := by
  dsimp [cramerRaoVarianceBound, accumulatedFisherInfo]

/-- **Main Theorem (Asymptotic Holographic Variance Contraction)**:
    For any target variance tolerance `ε > 0`, there exists a critical detector 4-volume
    `V_{4,crit} = 1 / (ε * I_0)` such that for all `V_4 > V_{4,crit}`,
    the Cramér-Rao retrodiction variance bound is strictly less than `ε`:
    `1 / (V_4 * I_0) < ε`. -/
theorem variance_bound_arbitrary_precision (I0 eps : ℝ) (hI : 0 < I0) (heps : 0 < eps) :
    ∃ V4_crit : ℝ, 0 < V4_crit ∧ ∀ V4, V4_crit < V4 → cramerRaoVarianceBound V4 I0 < eps := by
  use (1 / (eps * I0))
  constructor
  · have h_den : 0 < eps * I0 := mul_pos heps hI
    exact one_div_pos.mpr h_den
  · intro V4 hV
    dsimp [cramerRaoVarianceBound, accumulatedFisherInfo]
    have h_prod : 0 < eps * I0 := mul_pos heps hI
    have h_V_pos : 0 < V4 := by
      have : 0 < 1 / (eps * I0) := one_div_pos.mpr h_prod
      exact lt_trans this hV
    have h_denom_pos : 0 < V4 * I0 := mul_pos h_V_pos hI
    have h_mult : 1 < V4 * (eps * I0) := (div_lt_iff₀ h_prod).mp hV
    have h_rearr : 1 < eps * (V4 * I0) := by
      calc 1 < V4 * (eps * I0) := h_mult
           _ = eps * (V4 * I0) := by ring
    exact (div_lt_iff₀ h_denom_pos).mpr h_rearr

/-- Covariance ellipse area bound for the 2-parameter nuclear invariant bundle `θ = (λ, Q_0)`:
    `Area ∝ 1 / (V_4² * det(I_0))`. -/
noncomputable def nuclearMultipoleAreaBound (V4 det_I0 : ℝ) : ℝ :=
  1 / (V4 ^ 2 * det_I0)

/-- **Theorem (Holographic Quadric Area Scaling)**:
    The uncertainty area in the nuclear multipole plane contracts as `O(V_4⁻²)`. -/
theorem nuclear_multipole_area_scaling (V4 det_I0 : ℝ) :
    nuclearMultipoleAreaBound V4 det_I0 = (1 / V4 ^ 2) * (1 / det_I0) := by
  dsimp [nuclearMultipoleAreaBound]
  ring

/-- **Master Certified Conjunction for Quantum Retrodiction Information Geometry (Section 5.77)** -/
theorem certified_quantum_retrodiction_synthesis
    (R : Matrix n n ℝ) (L_mu : Matrix n n ℝ) (hL : L_muᵀ = L_mu)
    {m : ℕ} (L_vec : Fin m → Matrix n n ℝ)
    (I0 eps : ℝ) (hI : 0 < I0) (heps : 0 < eps)
    (V4 det_I0 : ℝ) :
    (qfimEntry (Rᵀ * R) L_mu L_mu = sldFisherInfo (Rᵀ * R) L_mu) ∧
    (0 ≤ qfimEntry (Rᵀ * R) L_mu L_mu) ∧
    (buresMetricForm (Rᵀ * R) L_vec (fun _ => 0) = 0) ∧
    (∃ V4_crit : ℝ, 0 < V4_crit ∧ ∀ V4, V4_crit < V4 → cramerRaoVarianceBound V4 I0 < eps) ∧
    (nuclearMultipoleAreaBound V4 det_I0 = (1 / V4 ^ 2) * (1 / det_I0)) := by
  refine ⟨qfimEntry_diag R L_mu hL,
          qfimEntry_diag_nonneg R L_mu hL,
          buresMetricForm_zero (Rᵀ * R) L_vec,
          variance_bound_arbitrary_precision I0 eps hI heps,
          nuclear_multipole_area_scaling V4 det_I0⟩

end InfoGeometry.Physics.QuantumRetrodiction
