import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The Hidden Conservation Law: Causal Petz Stiefel/Gram Constraint

Module: `InfoGeometry.QuantumContext.CausalPetzStiefelConservation`

This module formalizes:
1. **The Stiefel / Gram Operator**:
   $V^\top V = \begin{pmatrix} K^2 + L^2 & 0 \\ 0 & 0 \end{pmatrix}$.
2. **CPTP Stiefel Isometry Condition**:
   $V^\top V = P_{\mathrm{supp}} \iff K^2 + L^2 = 1$.
3. **Trace Preservation Theorem**:
   Under $K^2 + L^2 = 1$, the total trace of the reconstructed density matrix
   strictly matches the input trace: $\operatorname{Tr}(\mathcal{R}(\sigma)) = s$.
4. **Zero-Sum Generation Trade-Off**:
   - Exact past preservation ($K^2 = 1$) forces future generation to zero ($L^2 = 0$).
   - Future dominance ($L^2 = 1$) forces prompt retention to zero ($K^2 = 0$).

All proofs are native Mathlib with 0 sorry, 0 admit, and 0 custom axioms.
-/

namespace InfoGeometry.QuantumContext.CausalPetz

open Matrix

variable {R : Type*} [CommRing R]

/-- The $2 \times 2$ block intertwiner $V = \begin{pmatrix} K & 0 \\ L & 0 \end{pmatrix}$. -/
def blockIntertwiner (K L : R) : Matrix (Fin 2) (Fin 2) R :=
  !![K, 0;
     L, 0]

/-- The causal state on the retained past subspace $\sigma = \begin{pmatrix} s & 0 \\ 0 & 0 \end{pmatrix}$. -/
def blockCausalState (s : R) : Matrix (Fin 2) (Fin 2) R :=
  !![s, 0;
     0, 0]

/-- The Petz block reconstruction map $\mathcal{R}(\sigma) = V \sigma V^\top$. -/
def petzBlockReconstruct (K L s : R) : Matrix (Fin 2) (Fin 2) R :=
  blockIntertwiner K L * blockCausalState s * (blockIntertwiner K L)ᵀ

/-- The 2×2 matrix trace. -/
def trace2 (M : Matrix (Fin 2) (Fin 2) R) : R :=
  M 0 0 + M 1 1

/-! ### 1. Gram Partial Isometry Constraint -/

/-- **Theorem**: The Gram operator $V^\top V$ has diagonal entry $K^2 + L^2$ on support. -/
theorem blockIntertwiner_gram (K L : R) :
    (blockIntertwiner K L)ᵀ * blockIntertwiner K L =
    !![K^2 + L^2, 0;
       0,         0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [blockIntertwiner]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    ring
  · dsimp [blockIntertwiner]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  · dsimp [blockIntertwiner]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  · dsimp [blockIntertwiner]
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

/-- **Theorem**: The CPTP Stiefel condition: $V^\top V = P_{\mathrm{supp}} \iff K^2 + L^2 = 1$. -/
theorem gram_isometry_iff_stiefel (K L : R) :
    (blockIntertwiner K L)ᵀ * blockIntertwiner K L = !![1, 0; 0, 0] ↔
    K^2 + L^2 = 1 := by
  rw [blockIntertwiner_gram]
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    exact h00
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]

/-! ### 2. Trace Conservation Law -/

/-- 
**Trace Preservation Theorem**:
Under the Stiefel constraint $K^2 + L^2 = 1$, the total trace of the 
reconstructed density matrix strictly equals the input scalar $s$:
$\operatorname{Tr}(\mathcal{R}(\sigma)) = s$.
-/
theorem petz_trace_preservation (K L s : R) (h_stiefel : K^2 + L^2 = 1) :
    trace2 (petzBlockReconstruct K L s) = s := by
  dsimp [trace2, petzBlockReconstruct, blockIntertwiner, blockCausalState]
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  calc
    K * s * K + L * s * L = s * (K^2 + L^2) := by ring
    _ = s * 1 := by rw [h_stiefel]
    _ = s := mul_one s

/-- 
**The Zero-Sum Generation Trade-Off**:
If the past is perfectly preserved ($K^2 = 1$) in a trace-preserving channel, 
the future generation capacity is strictly ZERO ($L^2 = 0$).
-/
theorem past_preservation_forces_future_quiescence (K L : R)
    (h_stiefel : K^2 + L^2 = 1) (h_past : K^2 = 1) :
    L^2 = 0 := by
  calc
    L^2 = (K^2 + L^2) - K^2 := by ring
    _ = 1 - 1 := by rw [h_stiefel, h_past]
    _ = 0 := sub_self 1

/-- 
**Future Dominance Forces Past Annihilation**:
Conversely, if future generation is 100% ($L^2 = 1$), past prompt retention
is strictly ZERO ($K^2 = 0$), representing unconditioned generation / hallucination.
-/
theorem future_dominance_forces_past_annihilation (K L : R)
    (h_stiefel : K^2 + L^2 = 1) (h_future : L^2 = 1) :
    K^2 = 0 := by
  calc
    K^2 = (K^2 + L^2) - L^2 := by ring
    _ = 1 - 1 := by rw [h_stiefel, h_future]
    _ = 0 := sub_self 1

/-! ### 3. Master Verification Certificate -/

/-- Certificate bundling the proved Stiefel conservation theorems with Prop fields. -/
structure CausalPetzStiefelCertificate where
  gram_operator : ∀ {R : Type*} [CommRing R] (K L : R),
    (blockIntertwiner K L)ᵀ * blockIntertwiner K L = !![K^2 + L^2, 0; 0, 0]
  stiefel_iff : ∀ {R : Type*} [CommRing R] (K L : R),
    (blockIntertwiner K L)ᵀ * blockIntertwiner K L = !![1, 0; 0, 0] ↔ K^2 + L^2 = 1
  trace_preservation : ∀ {R : Type*} [CommRing R] (K L s : R) (h : K^2 + L^2 = 1),
    trace2 (petzBlockReconstruct K L s) = s
  past_forces_future_zero : ∀ {R : Type*} [CommRing R] (K L : R) (h1 : K^2 + L^2 = 1) (h2 : K^2 = 1),
    L^2 = 0
  future_forces_past_zero : ∀ {R : Type*} [CommRing R] (K L : R) (h1 : K^2 + L^2 = 1) (h2 : L^2 = 1),
    K^2 = 0

/-- Instantiation of the master certificate with zero open assumptions. -/
theorem compile_causal_petz_stiefel : CausalPetzStiefelCertificate :=
  { gram_operator := blockIntertwiner_gram
    stiefel_iff := gram_isometry_iff_stiefel
    trace_preservation := petz_trace_preservation
    past_forces_future_zero := past_preservation_forces_future_quiescence
    future_forces_past_zero := future_dominance_forces_past_annihilation }

end InfoGeometry.QuantumContext.CausalPetz
