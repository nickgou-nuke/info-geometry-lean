/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionKMSState
import InfoGeometry.QuantumContext.AttentionGNSBridge
import InfoGeometry.QuantumContext.AttentionStageColimitState

/-!
# Finite-Stage Attention Modular Flow, Quantitative Sink Bounds, and Selected-Stage Colimit Readout

This module formalizes four coupled extensions of the finite and stage-selected colimit
attention state architecture. No global colimit automorphism `Carrier → Carrier` across
incompatible logit vectors at different stages is claimed; `modularFlow` is a finite-stage
1-parameter `*`-automorphism group on `Matrix ι ι ℂ` (and `MatrixStage k`), and the colimit
results hold for the stage-`k`-selected colimit functional `selectedStageColimitFunctional k`
on injected stage-`k` observables and their cross-stage tower embeddings (`k ≤ n`):

1. **Archetype I — Quantitative Attention Sink Energy Bound & Anchor-Column Positivity**:
   - Quadratic evaluation identity `prunedState pw (Aᵀ A) = ∑ i, w_i ∑ j, (A_{j,i})²`.
   - Quantitative lower bounds `w_anchor * ∑ j, (A_{j,anchor})² ≤ prunedState pw (Aᵀ A)` and
     `w_anchor * (A_{j,anchor})² ≤ prunedState pw (Aᵀ A)`.
   - Exact anchor-column evaluation on `canonicalPrunedWeights`, together with the explicit
     `M_2(ℝ)` non-commutativity witness `matE01 * matE10 ≠ matE10 * matE01`; the anchor-supported
     unit `matE10` has energy `1`, while the evicted-column unit `matE01` has energy `0`.

2. **Archetype II — Real-Time 1-Parameter Diagonal Unitary Group & Finite-Stage Modular Flow**:
   - Diagonal unitary group `U_t = diag(exp(i t β logits_j))` on `M_ι(ℂ)`.
   - Finite-stage 1-parameter `*`-automorphism group `σ_t(A) = U_t A U_{-t}` preserving unit,
     multiplication, and involution (`star`), with group law `σ_{t+s} = σ_t ∘ σ_s` and entrywise
     oscillatory phase-difference formula `modularFlow_apply_eq_exp_sub`.

3. **Archetype III — Boltzmann Weight Ratio Identity & Diagonal State Modular Invariance**:
   - Exact Boltzmann weight ratio `ρ_i / ρ_j = exp(β (logits_i - logits_j))` and entrywise
     action of `attentionModularDelta`.
   - Commutation of arbitrary diagonal matrices with `modularUnitary` and trace invariance
     `Tr(diag(d) σ_t(A)) = Tr(diag(d) A)`.

4. **Archetype IV — Selected-Stage Colimit Modular Invariance, Cross-Stage Propagation & Pruned Colimit State**:
   - Invariance of `selectedStageColimitFunctional k` under `modularFlow` at stage `k` and
     under cross-stage Cuntz matrix tower bonding maps `rawMap h` for `k ≤ n`.
   - Selected-stage colimit KMS boundary trace-cycling identity for complexified real observables.
   - Stage-`k` pruned density `prunedStageDensity`, normalized trace one, exact real-seed readout,
     and a colimit lower bound giving positivity for operators with nonzero anchor-column support;
     this is not faithfulness on the full matrix algebra.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

open BigOperators
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionGNSBridge
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges

variable {ι : Type*}

/-! ### Archetype I: Quantitative Attention Sink Energy Bound & Anchor-Column Positivity -/

/-- The pruned state evaluates to the weighted diagonal sum `∑ i, w_i A_{i,i}`. -/
theorem prunedState_eq_sum [Fintype ι] [DecidableEq ι]
    (pw : PrunedWeights ι) (A : Matrix ι ι ℝ) :
    prunedState pw A = ∑ i, pw.weights i * A i i :=
  InfoGeometry.QuantumContext.MatrixGNS.diagonal_trace_mul pw.weights A

/-- Quadratic evaluation of the pruned state expands as the weighted sum of column squared norms. -/
theorem prunedState_quadratic_eq_sum [Fintype ι] [DecidableEq ι]
    (pw : PrunedWeights ι) (A : Matrix ι ι ℝ) :
    prunedState pw (A.transpose * A) =
      ∑ i, pw.weights i * (∑ j, (A j i) ^ 2) := by
  rw [prunedState_quadratic_eq_gnsInner]
  exact InfoGeometry.QuantumContext.MatrixGNS.gnsInner_self_diagonal pw.weights A

/-- **Quantitative Attention Sink Column Lower Bound**:
The pruned state energy `ω_pruned(Aᵀ A)` is bounded below by the anchor weight times the
squared Euclidean norm of the anchor column of `A`. -/
theorem prunedState_ge_anchor_column_normSq [Fintype ι] [DecidableEq ι]
    (pw : PrunedWeights ι) (anchor : ι) (A : Matrix ι ι ℝ) :
    pw.weights anchor * (∑ j, (A j anchor) ^ 2) ≤
      prunedState pw (A.transpose * A) := by
  rw [prunedState_quadratic_eq_sum]
  refine Finset.single_le_sum (f := fun i => pw.weights i * (∑ j, (A j i) ^ 2))
    (fun i _ => ?_) (Finset.mem_univ anchor)
  exact mul_nonneg (pw.nonneg i) (Finset.sum_nonneg (fun j _ => sq_nonneg (A j i)))

/-- **Quantitative Attention Sink Entrywise Lower Bound**:
For any row index `j` and token `anchor`, `w_anchor * (A_{j,anchor})² ≤ ω_pruned(Aᵀ A)`. -/
theorem prunedState_ge_anchor_entry_sq [Fintype ι] [DecidableEq ι]
    (pw : PrunedWeights ι) (anchor j : ι) (A : Matrix ι ι ℝ) :
    pw.weights anchor * (A j anchor) ^ 2 ≤
      prunedState pw (A.transpose * A) := by
  refine le_trans ?_ (prunedState_ge_anchor_column_normSq pw anchor A)
  apply mul_le_mul_of_nonneg_left _ (pw.nonneg anchor)
  exact Finset.single_le_sum (f := fun k => (A k anchor) ^ 2)
    (fun k _ => sq_nonneg (A k anchor)) (Finset.mem_univ j)

/-- On the canonical two-token pruned weight witness (`w_0 = 1`, `w_1 = 0`), the quadratic
state evaluates to the exact squared norm of column `0`. -/
theorem canonicalPrunedWeights_state_eq_anchor_column_normSq
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    prunedState canonicalPrunedWeights (A.transpose * A) =
      ∑ j : Fin 2, (A j 0) ^ 2 := by
  rw [prunedState_quadratic_eq_sum, Fin.sum_univ_two]
  have h0 : canonicalPrunedWeights.weights 0 = 1 := rfl
  have h1 : canonicalPrunedWeights.weights 1 = 0 := rfl
  rw [h0, h1, one_mul, zero_mul, add_zero]

/-- Elementary off-diagonal matrix unit `E_{0,1}` on the two-token carrier `Fin 2`. -/
def matE01 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- Elementary off-diagonal matrix unit `E_{1,0}` on the two-token carrier `Fin 2`. -/
def matE10 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- Explicit non-commutativity witness for the two-token matrix algebra `M_2(ℝ)`:
`matE01 * matE10 ≠ matE10 * matE01`. -/
theorem matE01_mul_matE10_ne_matE10_mul_matE01 :
    matE01 * matE10 ≠ matE10 * matE01 := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  dsimp [matE01, matE10, Matrix.mul_apply] at h00
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h00
  norm_num at h00

/-- The elementary matrix unit `matE10` (supported on anchor column `0`) has strictly
positive quadratic state energy `1` under `canonicalPrunedWeights`. -/
theorem canonicalPrunedWeights_matE10_state_eq_one :
    prunedState canonicalPrunedWeights (matE10.transpose * matE10) = 1 := by
  rw [canonicalPrunedWeights_state_eq_anchor_column_normSq, Fin.sum_univ_two]
  dsimp [matE10]
  norm_num

/-- The elementary matrix unit `matE01` (supported on evicted column `1`) lies in the
GNS null ideal of `canonicalPrunedWeights` with quadratic state energy `0`. -/
theorem canonicalPrunedWeights_matE01_state_eq_zero :
    prunedState canonicalPrunedWeights (matE01.transpose * matE01) = 0 := by
  rw [canonicalPrunedWeights_state_eq_anchor_column_normSq, Fin.sum_univ_two]
  dsimp [matE01]
  norm_num

/-! ### Archetype II: Real-Time 1-Parameter Diagonal Unitary Group & Finite-Stage Modular Flow -/

private theorem modularPhase_exp_arg_add (x t s β : ℝ) :
    Complex.I * ((t + s : ℝ) : ℂ) * (β : ℂ) * (x : ℂ) =
      Complex.I * (t : ℂ) * (β : ℂ) * (x : ℂ) +
        Complex.I * (s : ℂ) * (β : ℂ) * (x : ℂ) := by
  push_cast
  ring

private theorem modularPhase_exp_arg_conj (x t β : ℝ) :
    (starRingEnd ℂ) (Complex.I * (t : ℂ) * (β : ℂ) * (x : ℂ)) =
      Complex.I * ((-t : ℝ) : ℂ) * (β : ℂ) * (x : ℂ) := by
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

private theorem exp_phase_mul_entry_mul_neg (li lj β t : ℝ) (z : ℂ) :
    Complex.exp (Complex.I * (t : ℂ) * (β : ℂ) * (li : ℂ)) * z *
        Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (β : ℂ) * (lj : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ) * (β : ℂ) * ((li - lj : ℝ) : ℂ)) * z := by
  have h_comm :
      Complex.exp (Complex.I * (t : ℂ) * (β : ℂ) * (li : ℂ)) * z *
          Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (β : ℂ) * (lj : ℂ)) =
        (Complex.exp (Complex.I * (t : ℂ) * (β : ℂ) * (li : ℂ)) *
          Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (β : ℂ) * (lj : ℂ))) * z := by
    ring
  rw [h_comm, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- The oscillating phase factor `exp(i t β logits_j)` of token `j` under the real-time
modular group associated with inverse temperature `β` and logit vector `logits`. -/
def modularPhase (logits : ι → ℝ) (β t : ℝ) (j : ι) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (β : ℂ) * (logits j : ℂ))

/-- At `t = 0`, every modular phase factor is `1`. -/
theorem modularPhase_zero (logits : ι → ℝ) (β : ℝ) (j : ι) :
    modularPhase logits β 0 j = 1 := by
  dsimp [modularPhase]
  simp

/-- Additive parameter law for the modular phase factor:
`modularPhase logits β (t + s) j = modularPhase logits β t j * modularPhase logits β s j`. -/
theorem modularPhase_add (logits : ι → ℝ) (β t s : ℝ) (j : ι) :
    modularPhase logits β (t + s) j =
      modularPhase logits β t j * modularPhase logits β s j := by
  dsimp [modularPhase]
  rw [modularPhase_exp_arg_add (logits j) t s β, Complex.exp_add]

/-- Right inverse phase cancellation: `modularPhase t * modularPhase (-t) = 1`. -/
theorem modularPhase_neg_mul (logits : ι → ℝ) (β t : ℝ) (j : ι) :
    modularPhase logits β t j * modularPhase logits β (-t) j = 1 := by
  rw [← modularPhase_add, add_neg_cancel, modularPhase_zero]

/-- Left inverse phase cancellation: `modularPhase (-t) * modularPhase t = 1`. -/
theorem modularPhase_mul_neg (logits : ι → ℝ) (β t : ℝ) (j : ι) :
    modularPhase logits β (-t) j * modularPhase logits β t j = 1 := by
  rw [← modularPhase_add, neg_add_cancel, modularPhase_zero]

/-- Complex conjugation inverts the time parameter of the modular phase:
`star (modularPhase logits β t j) = modularPhase logits β (-t) j`. -/
theorem star_modularPhase (logits : ι → ℝ) (β t : ℝ) (j : ι) :
    star (modularPhase logits β t j) = modularPhase logits β (-t) j := by
  dsimp [modularPhase]
  rw [← Complex.exp_conj, modularPhase_exp_arg_conj]

/-- The diagonal unitary matrix `U_t = diag(exp(i t β logits_j))` generating the finite-stage
real-time modular flow on `M_ι(ℂ)`. -/
def modularUnitary [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (modularPhase logits β t)

/-- At `t = 0`, the modular unitary matrix is the identity matrix. -/
theorem modularUnitary_zero [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) :
    modularUnitary logits β 0 = 1 := by
  dsimp [modularUnitary]
  have h0 : modularPhase logits β 0 = fun _ => 1 := by
    funext j
    exact modularPhase_zero logits β j
  rw [h0, Matrix.diagonal_one]

/-- One-parameter group homomorphism law for `modularUnitary`:
`U_{t + s} = U_t * U_s`. -/
theorem modularUnitary_add [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t s : ℝ) :
    modularUnitary logits β (t + s) =
      modularUnitary logits β t * modularUnitary logits β s := by
  dsimp [modularUnitary]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  exact modularPhase_add logits β t s j

/-- Right unitarity identity: `U_t * U_{-t} = 1`. -/
theorem modularUnitary_mul_neg [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) :
    modularUnitary logits β t * modularUnitary logits β (-t) = 1 := by
  rw [← modularUnitary_add, add_neg_cancel, modularUnitary_zero]

/-- Left unitarity identity: `U_{-t} * U_t = 1`. -/
theorem modularUnitary_neg_mul [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) :
    modularUnitary logits β (-t) * modularUnitary logits β t = 1 := by
  rw [← modularUnitary_add, neg_add_cancel, modularUnitary_zero]

/-- Conjugate-transpose of `modularUnitary` reverses the time parameter:
`star (U_t) = U_{-t}`. -/
theorem modularUnitary_star [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) :
    star (modularUnitary logits β t) = modularUnitary logits β (-t) := by
  dsimp [modularUnitary]
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  exact star_modularPhase logits β t j

/-- The finite-stage 1-parameter dynamical Tomita modular automorphism group on `M_ι(ℂ)`:
`σ_t(A) = U_t A U_{-t}`. As shown in `modularFlow_apply_eq_exp_sub`, conjugating by `U_t`
multiplies the `(i, j)` entry by `exp(i t β (logits_i - logits_j))`, because the scalar
partition-function phase `Z^{-i t}` cancels between `ρ^{i t}` and `ρ^{-i t}` in direct
parallel to `attentionModularDelta_apply_eq_exp_sub`. -/
def modularFlow [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  modularUnitary logits β t * A * modularUnitary logits β (-t)

/-- Entrywise oscillatory phase-difference action of the finite-stage modular flow:
the `(i, j)` entry of `σ_t(A)` is multiplied by `exp(i t β (logits_i - logits_j))`,
paralleling the real Boltzmann ratio identity `attentionModularDelta_apply_eq_exp_sub`. -/
theorem modularFlow_apply_eq_exp_sub [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) (A : Matrix ι ι ℂ) (i j : ι) :
    modularFlow logits β t A i j =
      Complex.exp (Complex.I * (t : ℂ) * (β : ℂ) * ((logits i - logits j : ℝ) : ℂ)) *
        A i j := by
  dsimp [modularFlow, modularUnitary]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  dsimp [modularPhase]
  exact exp_phase_mul_entry_mul_neg (logits i) (logits j) β t (A i j)

/-- Identity flow at `t = 0`: `σ_0(A) = A`. -/
theorem modularFlow_zero [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (A : Matrix ι ι ℂ) :
    modularFlow logits β 0 A = A := by
  dsimp [modularFlow]
  rw [neg_zero, modularUnitary_zero, Matrix.one_mul, Matrix.mul_one]

/-- One-parameter group composition law: `σ_{t + s}(A) = σ_t(σ_s(A))`. -/
theorem modularFlow_add [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t s : ℝ) (A : Matrix ι ι ℂ) :
    modularFlow logits β (t + s) A =
      modularFlow logits β t (modularFlow logits β s A) := by
  dsimp [modularFlow]
  have hneg : -(t + s) = -s + -t := by
    rw [neg_add_rev]
  rw [modularUnitary_add, hneg, modularUnitary_add]
  simp only [Matrix.mul_assoc]

/-- The modular flow preserves the identity matrix: `σ_t(1) = 1`. -/
theorem modularFlow_one [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) :
    modularFlow logits β t 1 = 1 := by
  dsimp [modularFlow]
  rw [Matrix.mul_one, modularUnitary_mul_neg]

/-- The modular flow is multiplicative: `σ_t(A * B) = σ_t(A) * σ_t(B)`. -/
theorem modularFlow_mul [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) (A B : Matrix ι ι ℂ) :
    modularFlow logits β t (A * B) =
      modularFlow logits β t A * modularFlow logits β t B := by
  dsimp [modularFlow]
  calc
    modularUnitary logits β t * (A * B) * modularUnitary logits β (-t)
      = modularUnitary logits β t * A * 1 * B * modularUnitary logits β (-t) := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = modularUnitary logits β t * A *
          (modularUnitary logits β (-t) * modularUnitary logits β t) *
          B * modularUnitary logits β (-t) := by
          rw [modularUnitary_neg_mul]
    _ = (modularUnitary logits β t * A * modularUnitary logits β (-t)) *
          (modularUnitary logits β t * B * modularUnitary logits β (-t)) := by
          simp only [Matrix.mul_assoc]

/-- The modular flow commutes with the `star` involution: `σ_t(star A) = star (σ_t(A))`. -/
theorem modularFlow_star [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) (A : Matrix ι ι ℂ) :
    modularFlow logits β t (star A) =
      star (modularFlow logits β t A) := by
  dsimp [modularFlow]
  rw [star_mul, star_mul, modularUnitary_star, modularUnitary_star, neg_neg]
  simp only [Matrix.mul_assoc]

/-! ### Archetype III: Boltzmann Weight Ratio Identity & Diagonal State Modular Invariance -/

private theorem exp_div_same_denom (a b c : ℝ) (hc : c ≠ 0) :
    (Real.exp a / c) / (Real.exp b / c) = Real.exp (a - b) := by
  rw [Real.exp_sub]
  rw [div_eq_mul_inv (Real.exp a / c), inv_div, div_eq_mul_inv (Real.exp a)]
  calc
    Real.exp a * c⁻¹ * (c / Real.exp b)
      = Real.exp a * (c⁻¹ * c) / Real.exp b := by ring
    _ = Real.exp a * 1 / Real.exp b := by rw [inv_mul_cancel₀ hc]
    _ = Real.exp a / Real.exp b := by ring

/-- The ratio of two softmax weights cancels the partition function and equals the
Boltzmann factor `exp(β (logits_i - logits_j))`. -/
theorem softmaxWeight_div_eq_exp_sub [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (i j : ι) :
    softmaxWeight logits β i / softmaxWeight logits β j =
      Real.exp (β * (logits i - logits j)) := by
  dsimp [softmaxWeight]
  have hZ_pos : 0 < ∑ k, Real.exp (β * logits k) :=
    Finset.sum_pos' (fun k _ => le_of_lt (Real.exp_pos _))
      ⟨Classical.arbitrary ι, Finset.mem_univ _, Real.exp_pos _⟩
  rw [exp_div_same_denom (β * logits i) (β * logits j) _ (ne_of_gt hZ_pos)]
  rw [mul_sub]

/-- Entrywise action of the modular operator `Δ_ρ(X) = ρ X ρ⁻¹`: the `(i, j)` matrix entry
is scaled by `exp(β (logits_i - logits_j))`. -/
theorem attentionModularDelta_apply_eq_exp_sub [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (X : Matrix ι ι ℝ) (i j : ι) :
    attentionModularDelta logits β X i j =
      Real.exp (β * (logits i - logits j)) * X i j := by
  dsimp [attentionModularDelta, InfoGeometry.QuantumContext.MatrixGNS.modularDelta]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [mul_right_comm, ← div_eq_mul_inv, softmaxWeight_div_eq_exp_sub]

/-- Every diagonal matrix commutes with `modularUnitary`. -/
theorem diagonal_comm_modularUnitary [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (logits : ι → ℝ) (β t : ℝ) :
    Matrix.diagonal d * modularUnitary logits β t =
      modularUnitary logits β t * Matrix.diagonal d := by
  dsimp [modularUnitary]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm (d i) (modularPhase logits β t i)

/-- Any diagonal weighted trace functional `Tr(diag(d) ·)` is invariant under the
real-time modular automorphism group `modularFlow`. -/
theorem trace_diagonal_mul_modularFlow [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (logits : ι → ℝ) (β t : ℝ) (A : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.diagonal d * modularFlow logits β t A) =
      Matrix.trace (Matrix.diagonal d * A) := by
  dsimp [modularFlow]
  calc
    Matrix.trace (Matrix.diagonal d *
        (modularUnitary logits β t * A * modularUnitary logits β (-t)))
      = Matrix.trace (((Matrix.diagonal d * modularUnitary logits β t) * A) *
          modularUnitary logits β (-t)) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (modularUnitary logits β (-t) *
          ((Matrix.diagonal d * modularUnitary logits β t) * A)) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (modularUnitary logits β (-t) *
          ((modularUnitary logits β t * Matrix.diagonal d) * A)) := by
          rw [diagonal_comm_modularUnitary]
    _ = Matrix.trace ((modularUnitary logits β (-t) * modularUnitary logits β t) *
          (Matrix.diagonal d * A)) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (1 * (Matrix.diagonal d * A)) := by
          rw [modularUnitary_neg_mul]
    _ = Matrix.trace (Matrix.diagonal d * A) := by
          rw [Matrix.one_mul]

/-! ### Archetype IV: Selected-Stage Colimit Modular Invariance, Cross-Stage Propagation & Pruned Colimit State -/

/-- The stage-`k` attention density matrix commutes with the stage-`k` modular unitary group. -/
theorem attentionStageDensity_comm_modularUnitary
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) :
    attentionStageDensity k logits β * modularUnitary logits β t =
      modularUnitary logits β t * attentionStageDensity k logits β := by
  dsimp [attentionStageDensity]
  exact diagonal_comm_modularUnitary _ logits β t

/-- **Selected-Stage Colimit Modular Flow State Invariance**:
The stage-`k`-selected colimit functional `selectedStageColimitFunctional k` is invariant
under the stage-`k` real-time modular flow `modularFlow` on observables injected from `MatrixStage k`. -/
theorem attentionColimitFunctional_modularFlow_invariant
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (A : MatrixStage k) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k (modularFlow logits β t A)) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k A) := by
  rw [attentionColimitFunctional_seed_readout, attentionColimitFunctional_seed_readout]
  rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply]
  congr 1
  rw [Matrix.trace_mul_comm (modularFlow logits β t A),
    Matrix.trace_mul_comm A]
  dsimp [attentionStageDensity]
  exact trace_diagonal_mul_modularFlow _ logits β t A

/-- Cross-stage Cuntz matrix tower bonding homomorphism compatibility (`k ≤ n`) for the
finite-stage modular flow: pushing a modular-evolved stage-`k` observable across `rawMap h`
conjugates the pushed observable by the pushed modular unitaries at stage `n`. -/
theorem rawMap_modularFlow {k n : ℕ} (h : k ≤ n)
    (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (A : MatrixStage k) :
    rawMap h (modularFlow logits β t A) =
      rawMap h (modularUnitary logits β t) *
        rawMap h A *
        rawMap h (modularUnitary logits β (-t)) := by
  dsimp [modularFlow]
  rw [map_mul (rawMap h), map_mul (rawMap h)]

/-- **Cross-Stage Tower Propagation of Modular Flow State Invariance (`k ≤ n`)**:
Evaluating the stage-`k`-selected colimit functional on a modular-evolved stage-`k`
observable pushed forward to any higher stage `n` (`k ≤ n`) via `rawMap h` and injected
into `Carrier` equals the stage-`k` expectation of `A`. -/
theorem attentionColimitFunctional_rawMap_modularFlow_invariant
    {k n : ℕ} (h : k ≤ n) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (A : MatrixStage k) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection n (rawMap h (modularFlow logits β t A))) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k A) := by
  rw [stageInjection_transition h]
  exact attentionColimitFunctional_modularFlow_invariant k logits β t A

/-- Entrywise complexification preserves matrix multiplication. -/
theorem complexifyRealMatrix_mul [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    complexifyRealMatrix (A * B) =
      complexifyRealMatrix A * complexifyRealMatrix B := by
  ext i j
  dsimp [complexifyRealMatrix, Matrix.mul_apply]
  push_cast
  rfl

/-- **Selected-Stage Colimit KMS Boundary Trace-Cycling Identity**:
For any real matrix observables `A, B` at stage `k`, the stage-`k`-selected colimit
attention functional satisfies the algebraic KMS boundary relation
`ω_colim(stageInjection(A (ρ B ρ⁻¹))) = ω_colim(stageInjection(B A))`. -/
theorem attentionColimitFunctional_kms_boundary
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k
          (complexifyRealMatrix A *
            complexifyRealMatrix
              (attentionDensityMatrix logits β * B *
                attentionDensityMatrixInv logits β))) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k (complexifyRealMatrix (B * A))) := by
  rw [← complexifyRealMatrix_mul]
  rw [attentionColimitFunctional_real_seed_readout,
    attentionColimitFunctional_real_seed_readout]
  congr 1
  exact attentionState_kms logits β A B

/-- The pruned attention density at tower stage `k`, scaled by `2^k` to match the
normalized trace `(2^k)⁻¹ Tr` of the Cuntz matrix tower. -/
def prunedStageDensity (k : ℕ)
    (pw : PrunedWeights (Fin (2 ^ k))) : MatrixStage k :=
  Matrix.diagonal (fun i => (2 ^ k : ℂ) * (pw.weights i : ℂ))

@[simp]
theorem prunedStageDensity_apply (k : ℕ)
    (pw : PrunedWeights (Fin (2 ^ k))) (i j : Fin (2 ^ k)) :
    prunedStageDensity k pw i j =
      if i = j then (2 ^ k : ℂ) * (pw.weights i : ℂ) else 0 := by
  rw [prunedStageDensity, Matrix.diagonal_apply]

/-- The stage-`k` pruned density matrix has normalized trace `1`. -/
theorem prunedStageDensity_normalizedTrace (k : ℕ)
    (pw : PrunedWeights (Fin (2 ^ k))) :
    matrixTraceFunctional k (prunedStageDensity k pw) = 1 := by
  rw [matrixTraceFunctional_apply]
  have htrace : Matrix.trace (prunedStageDensity k pw) = (2 ^ k : ℂ) := by
    rw [prunedStageDensity, Matrix.trace_diagonal]
    calc
      (∑ i : Fin (2 ^ k), (2 ^ k : ℂ) * (pw.weights i : ℂ)) =
          (2 ^ k : ℂ) * ∑ i : Fin (2 ^ k), (pw.weights i : ℂ) := by
            rw [← Finset.mul_sum]
      _ = (2 ^ k : ℂ) * ((∑ i : Fin (2 ^ k), pw.weights i : ℝ) : ℂ) := by
            congr 1
            exact (map_sum (algebraMap ℝ ℂ)
              (fun i : Fin (2 ^ k) => pw.weights i) Finset.univ).symm
      _ = (2 ^ k : ℂ) := by
            rw [pw.sum_one]
            simp
  rw [htrace]
  have hne : (2 ^ k : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero k (by norm_num)
  exact one_div_mul_cancel hne

/-- The stage-`k` pruned density induces a unital functional on the algebraic
direct-limit carrier. -/
theorem prunedColimitFunctional_unital (k : ℕ)
    (pw : PrunedWeights (Fin (2 ^ k))) :
    selectedStageColimitFunctional k (prunedStageDensity k pw)
      (1 : Carrier) = 1 := by
  apply selectedStageColimitFunctional_one
  exact prunedStageDensity_normalizedTrace k pw

/-- Exact readout of complexified real matrix observables under the pruned colimit
functional at stage `k`. -/
theorem prunedColimitFunctional_real_seed_readout (k : ℕ)
    (pw : PrunedWeights (Fin (2 ^ k)))
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    selectedStageColimitFunctional k (prunedStageDensity k pw)
        (stageInjection k (complexifyRealMatrix A)) =
      (prunedState pw A : ℂ) := by
  rw [selectedStageColimitFunctional_stage, matrixTraceFunctional_apply]
  have htrace :
      Matrix.trace (complexifyRealMatrix A * prunedStageDensity k pw) =
        (2 ^ k : ℂ) * (prunedState pw A : ℂ) := by
    have hstate :
        (prunedState pw A : ℂ) =
          ∑ i : Fin (2 ^ k), ((pw.weights i * A i i : ℝ) : ℂ) := by
      rw [prunedState_eq_sum]
      exact map_sum (algebraMap ℝ ℂ)
        (fun i : Fin (2 ^ k) => pw.weights i * A i i) Finset.univ
    calc
      Matrix.trace (complexifyRealMatrix A * prunedStageDensity k pw) =
          ∑ i : Fin (2 ^ k),
            (A i i : ℂ) * ((2 ^ k : ℂ) * (pw.weights i : ℂ)) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          complexifyRealMatrix, prunedStageDensity_apply]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [hji]
        · simp
      _ = (2 ^ k : ℂ) *
            ∑ i : Fin (2 ^ k), ((pw.weights i * A i i : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        ac_rfl
      _ = (2 ^ k : ℂ) * (prunedState pw A : ℂ) := by
        rw [hstate]
  rw [htrace]
  have hne : (2 ^ k : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero k (by norm_num)
  calc
    (1 / (2 ^ k : ℂ)) * ((2 ^ k : ℂ) * (prunedState pw A : ℂ)) =
        ((1 / (2 ^ k : ℂ)) * (2 ^ k : ℂ)) * (prunedState pw A : ℂ) := by
      rw [← mul_assoc]
    _ = (prunedState pw A : ℂ) := by
      rw [one_div_mul_cancel hne, one_mul]

/-- **Colimit Attention Sink Quantitative Lower Bound**:
At any stage `k`, the real part of the stage-`k`-selected pruned colimit functional on
`Aᵀ A` is bounded below by `w_anchor * ∑ j, (A_{j,anchor})²`. -/
theorem prunedColimitFunctional_ge_anchor_column_normSq (k : ℕ)
    (pw : PrunedWeights (Fin (2 ^ k))) (anchor : Fin (2 ^ k))
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    pw.weights anchor * (∑ j : Fin (2 ^ k), (A j anchor) ^ 2) ≤
      (selectedStageColimitFunctional k (prunedStageDensity k pw)
        (stageInjection k (complexifyRealMatrix (A.transpose * A)))).re := by
  rw [prunedColimitFunctional_real_seed_readout, Complex.ofReal_re]
  exact prunedState_ge_anchor_column_normSq pw anchor A

/-- **Colimit Anchor-Column Positivity**:
If token `anchor` has strictly positive weight `w_anchor > 0` and `A_{j,anchor} ≠ 0`,
then the stage-`k`-selected pruned colimit functional assigns strictly positive
expectation to `Aᵀ A`. This does not assert faithfulness on the full matrix algebra. -/
theorem prunedColimitFunctional_anchor_column_positive (k : ℕ)
    (pw : PrunedWeights (Fin (2 ^ k))) (anchor j : Fin (2 ^ k))
    (h_anchor : 0 < pw.weights anchor)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ)
    (h_nz : A j anchor ≠ 0) :
    0 < (selectedStageColimitFunctional k (prunedStageDensity k pw)
      (stageInjection k (complexifyRealMatrix (A.transpose * A)))).re := by
  rw [prunedColimitFunctional_real_seed_readout, Complex.ofReal_re]
  exact sink_anchor_column_positive pw anchor h_anchor A j h_nz

end InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

end
