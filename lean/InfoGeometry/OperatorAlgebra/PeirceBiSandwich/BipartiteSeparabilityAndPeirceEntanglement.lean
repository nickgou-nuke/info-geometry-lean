/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Core
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.PinchedSuperExtension
import InfoGeometry.Clifford.GradedTensorCutRank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Bipartite Separability, Reduced Idempotency Defect, & Peirce Entanglement

This module formalizes:
1. Two-rebit pure state vectors $\psi : \mathrm{Fin}\ 2 \times \mathrm{Fin}\ 2 \to \mathbb{R}$ with amplitude
   matrix $C_\psi$, density projector $\Pi_\psi = \mathrm{pureProj}\ \psi$, and partial trace $\mathrm{Tr}_B$.
2. Exact algebraic identity $\mathrm{Tr}_B(\Pi_\psi) = C_\psi C_\psi^T$ and reduced state trace 1.
3. $2 \times 2$ Cayley–Hamilton trace-determinant reduction proving
   $\delta(\mathrm{Tr}_B(\Pi_\psi)) = -(C_\psi.\det ^ 2) \bullet 1$.
4. Exact three-way separability equivalence:
   $\mathrm{IsProductState}\ \psi \leftrightarrow C_\psi.\det = 0 \leftrightarrow \delta(\mathrm{Tr}_B(\Pi_\psi)) = 0$.
5. Decisive separation of tensor entanglement from single-cut Peirce Casimir defect $\mathrm{genV}$:
   - `productSuperpos` ($|+\rangle \otimes |0\rangle$): separable ($\delta(\mathrm{Tr}_B) = 0$), yet $\mathrm{genV}\ P_{\mathrm{loc}} \ne 0$.
   - `bellPhiPlus` ($(|00\rangle + |11\rangle)/\sqrt{2}$): entangled ($\delta(\mathrm{Tr}_B) \ne 0$), and $\mathrm{genV}\ P_{\mathrm{loc}} \ne 0$.
   Closes `docs/TWO_SHEETED_YANG_MILLS_FRAMEWORK_PROGRESS.md` lines 232–234.
6. OpenGauss T16 non-commutativity witness on `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich.BipartiteSeparabilityAndPeirceEntanglement

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceBiSandwich

/-! ### Part I: Two-Rebit State Space, Amplitude Matrix, & Partial Trace -/

def IsUnitState (ψ : Fin 2 × Fin 2 → ℝ) : Prop :=
  ∑ p : Fin 2 × Fin 2, ψ p ^ 2 = 1

def amplMat (ψ : Fin 2 × Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a b => ψ (a, b)

def pureProj (ψ : Fin 2 × Fin 2 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.of fun p q => ψ p * ψ q

def partialTraceB (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a a' => ∑ b : Fin 2, M (a, b) (a', b)

theorem partialTraceB_pureProj (ψ : Fin 2 × Fin 2 → ℝ) :
    partialTraceB (pureProj ψ) = (amplMat ψ) * (amplMat ψ)ᵀ := by
  ext a a'
  dsimp [partialTraceB, pureProj, amplMat, Matrix.mul_apply, Matrix.transpose_apply]

theorem trace_partialTraceB_pureProj (ψ : Fin 2 × Fin 2 → ℝ) (hψ : IsUnitState ψ) :
    (partialTraceB (pureProj ψ)).trace = 1 := by
  rw [partialTraceB_pureProj]
  dsimp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply, amplMat]
  simp_rw [Fin.sum_univ_two]
  dsimp [IsUnitState] at hψ
  rw [Fintype.sum_prod_type] at hψ
  simp_rw [Fin.sum_univ_two] at hψ
  linear_combination hψ

/-! ### Part II: Cayley–Hamilton & Reduced Idempotency Defect -/

lemma matrix2_cayley_hamilton (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M ^ 2 - M.trace • M + M.det • 1 = 0 := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    dsimp [Matrix.mul_apply, Matrix.trace,
           Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply]
    simp_rw [Fin.sum_univ_two]
    rw [Matrix.det_fin_two]
    ring

theorem idempotencyDefect_partialTraceB_pureProj (ψ : Fin 2 × Fin 2 → ℝ) (hψ : IsUnitState ψ) :
    delta (partialTraceB (pureProj ψ)) = -((amplMat ψ).det ^ 2) • 1 := by
  have h_rho : partialTraceB (pureProj ψ) = (amplMat ψ) * (amplMat ψ)ᵀ := by
    exact partialTraceB_pureProj ψ
  have h_tr : (partialTraceB (pureProj ψ)).trace = 1 := by
    exact trace_partialTraceB_pureProj ψ hψ
  have h_ch := matrix2_cayley_hamilton (partialTraceB (pureProj ψ))
  rw [h_tr, one_smul] at h_ch
  have h_delta : delta (partialTraceB (pureProj ψ)) = -((partialTraceB (pureProj ψ)).det • 1) := by
    dsimp [delta]
    calc (partialTraceB (pureProj ψ)) ^ 2 - (partialTraceB (pureProj ψ))
      _ = (partialTraceB (pureProj ψ)) ^ 2 - (partialTraceB (pureProj ψ)) +
          (partialTraceB (pureProj ψ)).det • 1 - (partialTraceB (pureProj ψ)).det • 1 := by
          rw [add_sub_cancel_right]
      _ = 0 - (partialTraceB (pureProj ψ)).det • 1 := by
          rw [h_ch]
      _ = -((partialTraceB (pureProj ψ)).det • 1) := by
          rw [zero_sub]
  have h_det : (partialTraceB (pureProj ψ)).det = (amplMat ψ).det ^ 2 := by
    rw [h_rho, Matrix.det_mul, Matrix.det_transpose, sq]
  rw [h_delta, h_det, neg_smul]

/-! ### Part III: Three-Way Separability Equivalence -/

def IsProductState (ψ : Fin 2 × Fin 2 → ℝ) : Prop :=
  ∃ (u v : Fin 2 → ℝ), ψ = fun (a, b) => u a * v b

theorem isProductState_iff_det_zero (ψ : Fin 2 × Fin 2 → ℝ) :
    IsProductState ψ ↔ (amplMat ψ).det = 0 := by
  constructor
  · rintro ⟨u, v, rfl⟩
    rw [Matrix.det_fin_two]
    dsimp [amplMat, of_apply]
    ring
  · intro hdet
    rw [Matrix.det_fin_two] at hdet
    dsimp [amplMat] at hdet
    by_cases h0 : (ψ (0, 0)) ^ 2 + (ψ (0, 1)) ^ 2 = 0
    · have h00 : ψ (0, 0) = 0 := by
        nlinarith
      have h01 : ψ (0, 1) = 0 := by
        nlinarith
      refine ⟨![0, 1], ![ψ (1, 0), ψ (1, 1)], ?_⟩
      ext ⟨a, b⟩
      fin_cases a <;> fin_cases b <;>
        { dsimp; simp [h00, h01] }
    · let s := (ψ (0, 0)) ^ 2 + (ψ (0, 1)) ^ 2
      let u : Fin 2 → ℝ := ![1, (ψ (0, 0) * ψ (1, 0) + ψ (0, 1) * ψ (1, 1)) / s]
      let v : Fin 2 → ℝ := ![ψ (0, 0), ψ (0, 1)]
      refine ⟨u, v, ?_⟩
      ext ⟨a, b⟩
      fin_cases a <;> fin_cases b
      · dsimp [u, v]
        ring
      · dsimp [u, v]
        ring
      · dsimp [u, v, s]
        have h_num : (ψ (0, 0) * ψ (1, 0) + ψ (0, 1) * ψ (1, 1)) * ψ (0, 0) =
            s * ψ (1, 0) := by
          dsimp [s]
          linear_combination (ψ (0, 1)) * hdet
        calc ψ (1, 0)
          _ = (s * ψ (1, 0)) / s := by
              rw [mul_div_cancel_left₀ (ψ (1, 0)) h0]
          _ = ((ψ (0, 0) * ψ (1, 0) + ψ (0, 1) * ψ (1, 1)) * ψ (0, 0)) / s := by
              rw [h_num]
          _ = ((ψ (0, 0) * ψ (1, 0) + ψ (0, 1) * ψ (1, 1)) / s) * ψ (0, 0) := by
              rw [div_mul_eq_mul_div₀]
      · dsimp [u, v, s]
        have h_num : (ψ (0, 0) * ψ (1, 0) + ψ (0, 1) * ψ (1, 1)) * ψ (0, 1) =
            s * ψ (1, 1) := by
          dsimp [s]
          linear_combination -(ψ (0, 0)) * hdet
        calc ψ (1, 1)
          _ = (s * ψ (1, 1)) / s := by
              rw [mul_div_cancel_left₀ (ψ (1, 1)) h0]
          _ = ((ψ (0, 0) * ψ (1, 0) + ψ (0, 1) * ψ (1, 1)) * ψ (0, 1)) / s := by
              rw [h_num]
          _ = ((ψ (0, 0) * ψ (1, 0) + ψ (0, 1) * ψ (1, 1)) / s) * ψ (0, 1) := by
              rw [div_mul_eq_mul_div₀]

theorem det_zero_iff_idempotencyDefect_zero (ψ : Fin 2 × Fin 2 → ℝ) (hψ : IsUnitState ψ) :
    (amplMat ψ).det = 0 ↔ delta (partialTraceB (pureProj ψ)) = 0 := by
  rw [idempotencyDefect_partialTraceB_pureProj ψ hψ]
  constructor
  · intro h
    rw [h, sq, mul_zero, neg_zero, zero_smul]
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num at h00
    exact h00

theorem isProductState_iff_idempotencyDefect_zero (ψ : Fin 2 × Fin 2 → ℝ) (hψ : IsUnitState ψ) :
    IsProductState ψ ↔ delta (partialTraceB (pureProj ψ)) = 0 := by
  rw [isProductState_iff_det_zero ψ, det_zero_iff_idempotencyDefect_zero ψ hψ]

/-! ### Part IV: Separation from Single-Cut Peirce Defect `genV` -/

def P_loc : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.of fun (a, b) (a', b') => if a = 0 ∧ a' = 0 ∧ b = b' then 1 else 0

lemma P_loc_idempotent : delta P_loc = 0 := by
  dsimp [delta]
  rw [sq]
  ext ⟨a, b⟩ ⟨a', b'⟩
  dsimp [Matrix.mul_apply, P_loc, Matrix.sub_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two]
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;>
    { simp }

noncomputable def productSuperpos : Fin 2 × Fin 2 → ℝ
  | (0, 0) => 1 / Real.sqrt 2
  | (1, 0) => 1 / Real.sqrt 2
  | (0, 1) => 0
  | (1, 1) => 0

noncomputable def bellPhiPlus : Fin 2 × Fin 2 → ℝ
  | (0, 0) => 1 / Real.sqrt 2
  | (1, 1) => 1 / Real.sqrt 2
  | (0, 1) => 0
  | (1, 0) => 0

lemma productSuperpos_isUnitState : IsUnitState productSuperpos := by
  dsimp [IsUnitState, productSuperpos]
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two]
  have h_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    exact Real.mul_self_sqrt (by norm_num)
  have h_div : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, one_pow, sq, h_sqrt2]
  rw [h_div]
  norm_num

lemma bellPhiPlus_isUnitState : IsUnitState bellPhiPlus := by
  dsimp [IsUnitState, bellPhiPlus]
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two]
  have h_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    exact Real.mul_self_sqrt (by norm_num)
  have h_div : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, one_pow, sq, h_sqrt2]
  rw [h_div]
  norm_num

theorem peirce_defect_differs_from_entanglement :
    (IsProductState productSuperpos ∧
     delta (partialTraceB (pureProj productSuperpos)) = 0 ∧
     casimirV P_loc (pureProj productSuperpos) (pureProj productSuperpos) ≠ 0) ∧
    (¬ IsProductState bellPhiPlus ∧
     delta (partialTraceB (pureProj bellPhiPlus)) = -(1/4 : ℝ) • 1 ∧
     delta (partialTraceB (pureProj bellPhiPlus)) ≠ 0 ∧
     casimirV P_loc (pureProj bellPhiPlus) (pureProj bellPhiPlus) ≠ 0) := by
  have h_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    exact Real.mul_self_sqrt (by norm_num)
  have h_div : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, one_pow, sq, h_sqrt2]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine ⟨![1 / Real.sqrt 2, 1 / Real.sqrt 2], ![1, 0], ?_⟩
    ext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> { dsimp [productSuperpos]; ring }
  · rw [← isProductState_iff_idempotencyDefect_zero _ productSuperpos_isUnitState]
    refine ⟨![1 / Real.sqrt 2, 1 / Real.sqrt 2], ![1, 0], ?_⟩
    ext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> { dsimp [productSuperpos]; ring }
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ => M (0, 0) (0, 0)) h
    dsimp [casimirV, Qplus, Qminus, Nplus, Nminus, P_loc, pureProj, productSuperpos] at h00
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, of_apply, Fintype.sum_prod_type] at h00
    simp_rw [Fin.sum_univ_two] at h00
    norm_num [h_div] at h00
  · intro h_prod
    have h_det := (isProductState_iff_det_zero bellPhiPlus).mp h_prod
    rw [Matrix.det_fin_two] at h_det
    dsimp [amplMat, of_apply, bellPhiPlus] at h_det
    have h_prod_div : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 : ℝ) / 2 := by
      rw [← sq, h_div]
    rw [h_prod_div] at h_det
    norm_num at h_det
  · rw [idempotencyDefect_partialTraceB_pureProj _ bellPhiPlus_isUnitState]
    have h_det : (amplMat bellPhiPlus).det = (1 : ℝ) / 2 := by
      rw [Matrix.det_fin_two]
      dsimp [amplMat, of_apply, bellPhiPlus]
      have h_prod_div : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 : ℝ) / 2 := by
        rw [← sq, h_div]
      rw [h_prod_div]
      ring
    rw [h_det]
    norm_num
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    rw [idempotencyDefect_partialTraceB_pureProj _ bellPhiPlus_isUnitState] at h00
    have h_det : (amplMat bellPhiPlus).det = (1 : ℝ) / 2 := by
      rw [Matrix.det_fin_two]
      dsimp [amplMat, of_apply, bellPhiPlus]
      have h_prod_div : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 : ℝ) / 2 := by
        rw [← sq, h_div]
      rw [h_prod_div]
      ring
    rw [h_det] at h00
    norm_num at h00
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ => M (0, 0) (0, 0)) h
    dsimp [casimirV, Qplus, Qminus, Nplus, Nminus, P_loc, pureProj, bellPhiPlus] at h00
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, of_apply, Fintype.sum_prod_type] at h00
    simp_rw [Fin.sum_univ_two] at h00
    norm_num [h_div] at h00

/-! ### Part V: OpenGauss T16 Non-commutativity Witnesses -/

def matE01 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0

def matE10 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem mat2_noncommuting_witness :
    matE01 * matE10 ≠ matE10 * matE01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  dsimp [matE01, matE10, Matrix.mul_apply] at h00
  simp_rw [Fin.sum_univ_two] at h00
  norm_num at h00

theorem peirce_entanglement_noncommuting_witness :
    P_loc * pureProj productSuperpos ≠ pureProj productSuperpos * P_loc := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ => M (0, 0) (1, 0)) h
  dsimp [P_loc, pureProj, productSuperpos] at h01
  simp only [Matrix.mul_apply, of_apply, Fintype.sum_prod_type] at h01
  simp_rw [Fin.sum_univ_two] at h01
  have h_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    exact Real.mul_self_sqrt (by norm_num)
  have h_div : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 : ℝ) / 2 := by
    rw [← sq, div_pow, one_pow, sq, h_sqrt2]
  norm_num [h_div] at h01

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich.BipartiteSeparabilityAndPeirceEntanglement
