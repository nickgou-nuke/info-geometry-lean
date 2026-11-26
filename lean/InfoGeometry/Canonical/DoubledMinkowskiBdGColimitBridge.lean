/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Doubled Minkowski `(4,4)` Krein Metrics, Gapped BdG Hamiltonians, and Directed-Tower Colimit

Formalizes the finite-stage and directed-tower colimit structure coupling a doubled particle–hole
carrier with indefinite Minkowski Krein geometry and gapped Bogoliubov–de Gennes (BdG) dynamics:

1. **Signature-`(4,4)` Doubled Minkowski Krein Metrics**:
   The diagonal Bogoliubov–Krein metric `𝒦_diag = Z ⊗ η_{1,3}` and off-diagonal para-Kähler null
   metric `𝒦_null = X ⊗ η_{1,3}` are symmetric, trace-zero involutions intertwined by the
   Hadamard sheet rotation `hadamardDoubled = H₂ ⊗ I₄`, render both sheets `N₊` and `N₋`
   maximally isotropic under `𝒦_null`, and restore the Euclidean norm under `J = 𝒦`.
2. **Gapped `2n × 2n` BdG Hamiltonian & Particle–Hole Symmetry**:
   For any symmetric real operator `ξ ∈ Mₙ(ℝ)` (`ξᵀ = ξ`) and pairing gap `m : ℝ`,
   `bdgHamiltonian ξ m = [[ξ, m I], [m I, -ξ]]` satisfies `Hᵀ = H`, anticommutation with
   `bdgChargeConj n`, exact block diagonalization `H² = diag(ξ² + m² I, ξ² + m² I)`, uniform
   spectral gap `m² ‖ψ‖² ≤ ⟨ψ, H² ψ⟩`, and trivial kernel for `m ≠ 0`.
3. **Directed-Tower Inductive Colimit**:
   For any lattice refinement tower `(Vₙ, ιₙ)` preserving `kreinPair` and `normSq` with summable
   renormalization-step errors `εₙ` (`Summable ε`), `seqPair ι kreinPair` is strictly invariant
   and `seqVal ι bdgQuad` converges to a projectively compatible continuum quadratic form `Q_inf`
   retaining both `0 ≤ Q_inf n u` and the uniform mass gap `m_gap² * normSq n u ≤ Q_inf n u`.

Scope boundary: This module establishes finite-matrix operator identities and abstract
directed-tower Cauchy convergence under summable step-stability bounds; it does not claim
4D continuum quantum Yang–Mills Wightman/PDE existence in the `a → 0` limit.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open scoped Kronecker
open Matrix Filter

namespace InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge

/-! ### Part 1: Indefinite Doubled Minkowski Metrics (Signature `(4,4)`) & Hadamard Intertwining -/

/-- `4 × 4` Minkowski signature `(1,3)` metric tensor `diag(1, -1, -1, -1)`. -/
def minkowski4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,  0,  0,  0;
     0, -1,  0,  0;
     0,  0, -1,  0;
     0,  0,  0, -1]

/-- Pauli `Z`-grading `diag(1, -1)` across the two sheets. -/
def zCut2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Sheet-exchange involution `X = [[0, 1], [1, 0]]`. -/
def xMir2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Symmetric `2 × 2` orthogonal Hadamard rotation `H₂ = (1 / √2) [[1, 1], [1, -1]]`. -/
def hadamard2 : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / Real.sqrt 2) • !![1, 1; 1, -1]

/-- Diagonal Bogoliubov–Krein doubled Minkowski metric `𝒦_diag = Z ⊗ η_{1,3}`. -/
def doubledMinkowskiDiag : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  zCut2 ⊗ₖ minkowski4

/-- Off-diagonal para-Kähler doubled Minkowski metric `𝒦_null = X ⊗ η_{1,3}`. -/
def doubledMinkowskiNull : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  xMir2 ⊗ₖ minkowski4

/-- Hadamard sheet rotation lifted to `Fin 2 × Fin 4`: `H₂ ⊗ I₄`. -/
def hadamardDoubled : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  hadamard2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)

private lemma transpose_kronecker_real {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rfl

/-- Explicit non-commutativity witness in `M₂(ℝ)`: `Z * X ≠ X * Z`. -/
theorem zCut2_xMir2_noncomm : zCut2 * xMir2 ≠ xMir2 * zCut2 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp [zCut2, xMir2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

theorem exists_noncomm_mat2_real :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨zCut2, xMir2, zCut2_xMir2_noncomm⟩

/-- Explicit non-commutativity witness in `M₄(ℝ)`. -/
theorem exists_noncomm_mat4_real :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  let S : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0, 1, 0, 0;
       1, 0, 0, 0;
       0, 0, 1, 0;
       0, 0, 0, 1]
  refine ⟨minkowski4, S, fun h => ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
  simp [minkowski4, S, Matrix.mul_apply, Fin.sum_univ_four] at h01
  norm_num at h01

/-- Anticommutation `𝒦_diag * 𝒦_null = -(𝒦_null * 𝒦_diag)` and non-commutativity in
`M_{2×4}(ℝ)`. -/
theorem doubledMinkowski_anticomm :
    doubledMinkowskiDiag * doubledMinkowskiNull =
      -(doubledMinkowskiNull * doubledMinkowskiDiag) := by
  have hAnti2 : zCut2 * xMir2 = -(xMir2 * zCut2) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [zCut2, xMir2, Matrix.mul_apply, Fin.sum_univ_two]
  have hSq4 : minkowski4 * minkowski4 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [minkowski4, Matrix.mul_apply, Fin.sum_univ_four]
  unfold doubledMinkowskiDiag doubledMinkowskiNull
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hAnti2, hSq4]
  ext ⟨a, i⟩ ⟨b, j⟩
  simp

theorem exists_noncomm_mat2x4_real :
    ∃ A B : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨doubledMinkowskiDiag, doubledMinkowskiNull, fun h => ?_⟩
  rw [doubledMinkowski_anticomm] at h
  have h00 := congrArg
    (fun M : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ => M (0, 0) (1, 0)) h
  simp [doubledMinkowskiDiag, doubledMinkowskiNull, zCut2, xMir2, minkowski4,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]
    at h00
  norm_num at h00

/-- Orthogonal Hadamard sheet rotation intertwines the diagonal Bogoliubov–Krein metric with the
off-diagonal para-Kähler null metric: `H * 𝒦_diag * H = 𝒦_null`. -/
theorem hadamardDoubled_intertwines_diag_null :
    hadamardDoubledᵀ = hadamardDoubled ∧
    hadamardDoubled * hadamardDoubled = 1 ∧
    hadamardDoubled * doubledMinkowskiDiag * hadamardDoubled = doubledMinkowskiNull := by
  have hH_sym : hadamard2ᵀ = hadamard2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hadamard2]
  have hScaleSq : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [one_div_mul_one_div, ← sq, Real.sq_sqrt (by norm_num)]
  have hH_sq : hadamard2 * hadamard2 = 1 := by
    unfold hadamard2
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hScaleSq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp <;> norm_num
  have hH_rot : hadamard2 * zCut2 * hadamard2 = xMir2 := by
    unfold hadamard2
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hScaleSq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [zCut2, xMir2] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold hadamardDoubled
    rw [transpose_kronecker_real, hH_sym, Matrix.transpose_one]
  · unfold hadamardDoubled
    rw [← Matrix.mul_kronecker_mul, hH_sq, mul_one, Matrix.one_kronecker_one]
  · unfold hadamardDoubled doubledMinkowskiDiag doubledMinkowskiNull
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hH_rot, one_mul, mul_one]

/-- **Signature-`(4,4)` Doubled Minkowski Krein Metrics & Fundamental Symmetry Positivity**:
1. Both `doubledMinkowskiDiag` and `doubledMinkowskiNull` are symmetric, trace-zero involutions.
2. Both sheets `N₊ = {(0, μ)}` and `N₋ = {(1, μ)}` are maximally isotropic under `doubledMinkowskiNull`.
3. Applying the fundamental symmetry `J = 𝒦` restores the Euclidean norm `⟨v, 𝒦² v⟩ = ⟨v, v⟩`. -/
theorem doubled_minkowski_krein_metrics_spec (v : Fin 2 × Fin 4 → ℝ) (u₁ u₂ : Fin 4 → ℝ) :
    (doubledMinkowskiDiagᵀ = doubledMinkowskiDiag ∧
     doubledMinkowskiDiag * doubledMinkowskiDiag = 1 ∧
     Matrix.trace doubledMinkowskiDiag = 0) ∧
    (doubledMinkowskiNullᵀ = doubledMinkowskiNull ∧
     doubledMinkowskiNull * doubledMinkowskiNull = 1 ∧
     Matrix.trace doubledMinkowskiNull = 0) ∧
    (dotProduct (fun p : Fin 2 × Fin 4 => if p.1 = 0 then u₁ p.2 else 0)
      (doubledMinkowskiNull.mulVec (fun p : Fin 2 × Fin 4 => if p.1 = 0 then u₂ p.2 else 0)) = 0) ∧
    (dotProduct (fun p : Fin 2 × Fin 4 => if p.1 = 1 then u₁ p.2 else 0)
      (doubledMinkowskiNull.mulVec (fun p : Fin 2 × Fin 4 => if p.1 = 1 then u₂ p.2 else 0)) = 0) ∧
    (dotProduct v ((doubledMinkowskiDiag * doubledMinkowskiDiag).mulVec v) = dotProduct v v) := by
  have hM_sym : minkowski4ᵀ = minkowski4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [minkowski4]
  have hZ_sym : zCut2ᵀ = zCut2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [zCut2]
  have hX_sym : xMir2ᵀ = xMir2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [xMir2]
  have hM2 : minkowski4 * minkowski4 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [minkowski4, Matrix.mul_apply, Fin.sum_univ_four]
  have hZ2 : zCut2 * zCut2 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [zCut2, Matrix.mul_apply, Fin.sum_univ_two]
  have hX2 : xMir2 * xMir2 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [xMir2, Matrix.mul_apply, Fin.sum_univ_two]
  have hDiagSq : doubledMinkowskiDiag * doubledMinkowskiDiag = 1 := by
    unfold doubledMinkowskiDiag
    rw [← Matrix.mul_kronecker_mul, hZ2, hM2, Matrix.one_kronecker_one]
  have hNullSq : doubledMinkowskiNull * doubledMinkowskiNull = 1 := by
    unfold doubledMinkowskiNull
    rw [← Matrix.mul_kronecker_mul, hX2, hM2, Matrix.one_kronecker_one]
  refine ⟨⟨?_, hDiagSq, ?_⟩, ⟨?_, hNullSq, ?_⟩, ?_, ?_, ?_⟩
  · unfold doubledMinkowskiDiag; rw [transpose_kronecker_real, hZ_sym, hM_sym]
  · simp [doubledMinkowskiDiag, zCut2, minkowski4, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]
  · unfold doubledMinkowskiNull; rw [transpose_kronecker_real, hX_sym, hM_sym]
  · simp [doubledMinkowskiNull, xMir2, minkowski4, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]
  · simp [doubledMinkowskiNull, xMir2, minkowski4,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_four]
  · simp [doubledMinkowskiNull, xMir2, minkowski4,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_four]
  · rw [hDiagSq, Matrix.one_mulVec]

/-! ### Part 2: Gapped Bogoliubov–de Gennes (BdG) Hamiltonian on the Doubled Carrier -/

/-- `2n × 2n` Bogoliubov–de Gennes Hamiltonian `H_BdG(ξ, m) = [[ξ, m Iₙ], [m Iₙ, -ξ]]`
coupling the particle sheet `ℋ₊` and hole sheet `ℋ₋` with pairing mass gap `m`. -/
def bdgHamiltonian {n : ℕ} (ξ : Matrix (Fin n) (Fin n) ℝ) (m : ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks ξ (m • (1 : Matrix (Fin n) (Fin n) ℝ))
    (m • (1 : Matrix (Fin n) (Fin n) ℝ)) (-ξ)

/-- Particle–hole conjugation operator `𝒞 = [[0, Iₙ], [-Iₙ, 0]]` (`𝒞² = -I_{2n}`). -/
def bdgChargeConj (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- Explicit matrix non-commutativity witness on the doubled BdG block carrier
`Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ`. -/
theorem exists_noncomm_bdg_mat :
    ∃ A B : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ, A * B ≠ B * A := by
  refine ⟨bdgChargeConj 1, bdgHamiltonian 1 1, fun h => ?_⟩
  have h10 := congrArg
    (fun M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ => M (Sum.inr 0) (Sum.inl 0)) h
  simp [bdgChargeConj, bdgHamiltonian, Matrix.fromBlocks_multiply] at h10
  norm_num at h10

private lemma dotProduct_fromBlocks_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (ψ : Fin n ⊕ Fin n → ℝ) :
    dotProduct ψ ((Matrix.fromBlocks A 0 0 B).mulVec ψ) =
      dotProduct (fun i => ψ (Sum.inl i)) (A.mulVec (fun i => ψ (Sum.inl i))) +
      dotProduct (fun i => ψ (Sum.inr i)) (B.mulVec (fun i => ψ (Sum.inr i))) := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type]

private lemma dotProduct_sum_self {n : ℕ} (ψ : Fin n ⊕ Fin n → ℝ) :
    dotProduct ψ ψ =
      dotProduct (fun i => ψ (Sum.inl i)) (fun i => ψ (Sum.inl i)) +
      dotProduct (fun i => ψ (Sum.inr i)) (fun i => ψ (Sum.inr i)) := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- **Gapped BdG Particle–Hole Symmetry, Diagonalized Square, & Uniform Spectral Gap**:
For any symmetric kinetic/Yang–Mills matrix `ξ ∈ Mₙ(ℝ)` (`ξᵀ = ξ`) and pairing gap `m : ℝ`:
1. `H_BdG(ξ, m)ᵀ = H_BdG(ξ, m)` and `𝒞 * H_BdG(ξ, m) + H_BdG(ξ, m) * 𝒞 = 0`.
2. `H_BdG(ξ, m)² = fromBlocks (ξ² + m² Iₙ) 0 0 (ξ² + m² Iₙ)`.
3. For every doubled state `ψ`, `⟨ψ, H_BdG² ψ⟩ = ⟨H_BdG ψ, H_BdG ψ⟩ ≥ m² ⟨ψ, ψ⟩`, and
   `m ≠ 0 → H_BdG ψ = 0 → ψ = 0`. -/
theorem bdg_gapped_spectrum_and_particle_hole_symmetry {n : ℕ}
    (ξ : Matrix (Fin n) (Fin n) ℝ) (hξ : ξᵀ = ξ) (m : ℝ)
    (ψ : Fin n ⊕ Fin n → ℝ) :
    let H := bdgHamiltonian ξ m
    let C := bdgChargeConj n
    (Hᵀ = H) ∧
    (C * H + H * C = 0) ∧
    (H * H = Matrix.fromBlocks (ξ * ξ + (m ^ 2) • 1) 0 0 (ξ * ξ + (m ^ 2) • 1)) ∧
    (dotProduct ψ ((H * H).mulVec ψ) =
      dotProduct (H.mulVec ψ) (H.mulVec ψ)) ∧
    (m ^ 2 * dotProduct ψ ψ ≤ dotProduct ψ ((H * H).mulVec ψ)) ∧
    (m ≠ 0 → H.mulVec ψ = 0 → ψ = 0) := by
  dsimp
  have hSym : (bdgHamiltonian ξ m)ᵀ = bdgHamiltonian ξ m := by
    unfold bdgHamiltonian
    rw [Matrix.fromBlocks_transpose, hξ, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_neg, hξ]
  have hPH : bdgChargeConj n * bdgHamiltonian ξ m + bdgHamiltonian ξ m * bdgChargeConj n = 0 := by
    unfold bdgChargeConj bdgHamiltonian
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp
  have hSq : bdgHamiltonian ξ m * bdgHamiltonian ξ m =
      Matrix.fromBlocks (ξ * ξ + (m ^ 2) • 1) 0 0 (ξ * ξ + (m ^ 2) • 1) := by
    unfold bdgHamiltonian
    rw [Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;> simp [Matrix.mul_apply, sq] <;> ring
  have hNormSq : dotProduct ψ ((bdgHamiltonian ξ m * bdgHamiltonian ξ m).mulVec ψ) =
      dotProduct ((bdgHamiltonian ξ m).mulVec ψ) ((bdgHamiltonian ξ m).mulVec ψ) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSym]
  have hGap : m ^ 2 * dotProduct ψ ψ ≤
      dotProduct ψ ((bdgHamiltonian ξ m * bdgHamiltonian ξ m).mulVec ψ) := by
    let ψ₁ : Fin n → ℝ := fun i => ψ (Sum.inl i)
    let ψ₂ : Fin n → ℝ := fun i => ψ (Sum.inr i)
    have hξSq_nn : ∀ u : Fin n → ℝ, 0 ≤ dotProduct u ((ξ * ξ).mulVec u) := fun u => by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hξ]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hQuad : ∀ u : Fin n → ℝ,
        dotProduct u ((ξ * ξ + (m ^ 2) • 1).mulVec u) =
          dotProduct u ((ξ * ξ).mulVec u) + m ^ 2 * dotProduct u u := fun u => by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
    have hEqSum :
        dotProduct ψ ((bdgHamiltonian ξ m * bdgHamiltonian ξ m).mulVec ψ) =
          m ^ 2 * dotProduct ψ ψ +
            (dotProduct ψ₁ ((ξ * ξ).mulVec ψ₁) + dotProduct ψ₂ ((ξ * ξ).mulVec ψ₂)) := by
      rw [hSq, dotProduct_fromBlocks_diag, hQuad ψ₁, hQuad ψ₂, dotProduct_sum_self ψ, mul_add,
        add_add_add_comm, add_comm]
    rw [hEqSum]
    exact le_add_of_nonneg_right (add_nonneg (hξSq_nn ψ₁) (hξSq_nn ψ₂))
  refine ⟨hSym, hPH, hSq, hNormSq, hGap, ?_⟩
  intro hm hH0
  have h0 : dotProduct ψ ((bdgHamiltonian ξ m * bdgHamiltonian ξ m).mulVec ψ) = 0 := by
    rw [hNormSq, hH0, dotProduct_zero]
  have hLe : m ^ 2 * dotProduct ψ ψ ≤ 0 := h0 ▸ hGap
  have hNN : 0 ≤ dotProduct ψ ψ :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (ψ i)
  have hm2_pos : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  have hDot_le : dotProduct ψ ψ ≤ 0 := nonpos_of_mul_nonpos_right hLe hm2_pos
  have hDot0 : dotProduct ψ ψ = 0 := le_antisymm hDot_le hNN
  ext i
  have hAll := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (ψ j))).mp hDot0
  exact mul_self_eq_zero.mp (hAll i (Finset.mem_univ i))

/-! ### Part 3: Directed-Tower Inductive Colimit Preserving Doubled Minkowski & BdG Gap -/

/-- Recursive multi-step evaluation `seqVal ι F n u m = F (n + m) (ι_{n, n+m} u)` along a
directed lattice refinement tower `ι : ∀ n, V n → V (n + 1)`. -/
def seqVal {V : ℕ → Type*} (ι : ∀ n, V n → V (n + 1)) (F : ∀ n, V n → ℝ) :
    (n : ℕ) → V n → ℕ → ℝ
  | n, u, 0 => F n u
  | n, u, m + 1 => seqVal ι F (n + 1) (ι n u) m

/-- Recursive two-argument evaluation `seqPair ι B n u v m = B (n + m) (ι_{n, n+m} u) (ι_{n, n+m} v)`. -/
def seqPair {V : ℕ → Type*} (ι : ∀ n, V n → V (n + 1)) (B : ∀ n, V n → V n → ℝ) :
    (n : ℕ) → V n → V n → ℕ → ℝ
  | n, u, v, 0 => B n u v
  | n, u, v, m + 1 => seqPair ι B (n + 1) (ι n u) (ι n v) m

/-- **Continuum Colimit Doubled Minkowski Metric & Persistent BdG Spectral Gap**:
Along any directed refinement tower `(Vₙ, ιₙ)` preserving `normSq` and `kreinPair` with stage
gap `m_gap² * normSq n u ≤ bdgQuad n u` and summable step error `εₙ` (`Summable ε`):
1. The indefinite doubled Minkowski pairing `seqPair ι kreinPair` is strictly scale-invariant.
2. `seqVal ι bdgQuad n u` converges to a continuum quadratic form `Q_inf n u ≥ 0` satisfying
   exact projective compatibility `Q_inf (n + 1) (ι n u) = Q_inf n u` and the uniform continuum
   mass gap `m_gap² * normSq n u ≤ Q_inf n u`. -/
theorem continuum_colimit_doubled_minkowski_and_bdg_mass_gap
    {V : ℕ → Type*}
    (ι : ∀ n, V n → V (n + 1))
    (normSq : ∀ n, V n → ℝ)
    (kreinPair : ∀ n, V n → V n → ℝ)
    (bdgQuad : ∀ n, V n → ℝ)
    (ε : ℕ → ℝ) (m_gap : ℝ)
    (hNorm_nn : ∀ n (u : V n), 0 ≤ normSq n u)
    (hNorm_iso : ∀ n (u : V n), normSq (n + 1) (ι n u) = normSq n u)
    (hKrein_iso : ∀ n (u v : V n), kreinPair (n + 1) (ι n u) (ι n v) = kreinPair n u v)
    (hGap_stage : ∀ n (u : V n), m_gap ^ 2 * normSq n u ≤ bdgQuad n u)
    (hSum : Summable ε)
    (hApprox : ∀ n (u : V n), |bdgQuad (n + 1) (ι n u) - bdgQuad n u| ≤ ε n * normSq n u) :
    (∀ n (u v : V n) (m : ℕ), seqPair ι kreinPair n u v m = kreinPair n u v) ∧
    ∃ Q_inf : ∀ n, V n → ℝ,
      (∀ n (u : V n), Tendsto (seqVal ι bdgQuad n u) atTop (nhds (Q_inf n u))) ∧
      (∀ n (u : V n), Q_inf (n + 1) (ι n u) = Q_inf n u) ∧
      (∀ n (u : V n), m_gap ^ 2 * normSq n u ≤ Q_inf n u) ∧
      (∀ n (u : V n), 0 ≤ Q_inf n u) := by
  have hKreinAll : ∀ (m n : ℕ) (u v : V n), seqPair ι kreinPair n u v m = kreinPair n u v := by
    intro m
    induction m with
    | zero => intros; rfl
    | succ k ih =>
      intro n u v
      change seqPair ι kreinPair (n + 1) (ι n u) (ι n v) k = kreinPair n u v
      rw [ih, hKrein_iso]
  have hNormAll : ∀ (m n : ℕ) (u : V n), seqVal ι normSq n u m = normSq n u := by
    intro m
    induction m with
    | zero => intros; rfl
    | succ k ih =>
      intro n u
      change seqVal ι normSq (n + 1) (ι n u) k = normSq n u
      rw [ih, hNorm_iso]
  have hGapAll : ∀ (m n : ℕ) (u : V n), m_gap ^ 2 * normSq n u ≤ seqVal ι bdgQuad n u m := by
    intro m
    induction m with
    | zero => intro n u; exact hGap_stage n u
    | succ k ih =>
      intro n u
      change m_gap ^ 2 * normSq n u ≤ seqVal ι bdgQuad (n + 1) (ι n u) k
      rw [← hNorm_iso n u]
      exact ih (n + 1) (ι n u)
  have hStepDiff : ∀ (m n : ℕ) (u : V n),
      |seqVal ι bdgQuad n u (m + 1) - seqVal ι bdgQuad n u m| ≤ ε (n + m) * normSq n u := by
    intro m
    induction m with
    | zero =>
      intro n u
      simpa [seqVal] using hApprox n u
    | succ k ih =>
      intro n u
      calc |seqVal ι bdgQuad n u (k + 2) - seqVal ι bdgQuad n u (k + 1)|
          = |seqVal ι bdgQuad (n + 1) (ι n u) (k + 1) -
             seqVal ι bdgQuad (n + 1) (ι n u) k| := rfl
        _ ≤ ε (n + 1 + k) * normSq (n + 1) (ι n u) := ih (n + 1) (ι n u)
        _ = ε (n + (k + 1)) * normSq n u := by rw [hNorm_iso]; congr 2; omega
  have hCauchy : ∀ n (u : V n), CauchySeq (seqVal ι bdgQuad n u) := by
    intro n u
    apply cauchySeq_of_summable_dist
    have hDist : ∀ m : ℕ,
        dist (seqVal ι bdgQuad n u m) (seqVal ι bdgQuad n u (m + 1)) ≤
        ε (n + m) * normSq n u := by
      intro m
      rw [dist_comm, Real.dist_eq]
      exact hStepDiff m n u
    have hSumShift : Summable (fun m : ℕ => ε (n + m) * normSq n u) := by
      have h1 : Summable (fun m : ℕ => ε (m + n)) := (summable_nat_add_iff n).mpr hSum
      have h2' : (fun m : ℕ => ε (n + m) * normSq n u) =
          (fun m => ε (m + n) * normSq n u) := by
        ext m; rw [add_comm]
      rw [h2']
      exact h1.mul_right (normSq n u)
    exact Summable.of_nonneg_of_le (fun _ => dist_nonneg) hDist hSumShift
  choose Q_inf hTendsto using fun n (u : V n) => cauchySeq_tendsto_of_complete (hCauchy n u)
  have hGapInf : ∀ n (u : V n), m_gap ^ 2 * normSq n u ≤ Q_inf n u := fun n u =>
    le_of_tendsto_of_tendsto tendsto_const_nhds (hTendsto n u)
      (Eventually.of_forall fun m => hGapAll m n u)
  refine ⟨fun n u v m => hKreinAll m n u v, Q_inf, hTendsto, ?_, hGapInf, ?_⟩
  · intro n u
    have hShift : Tendsto (fun m => seqVal ι bdgQuad n u (m + 1)) atTop (nhds (Q_inf n u)) :=
      (tendsto_add_atTop_iff_nat 1).mpr (hTendsto n u)
    exact tendsto_nhds_unique (hTendsto (n + 1) (ι n u)) hShift
  · intro n u
    exact le_trans (mul_nonneg (sq_nonneg m_gap) (hNorm_nn n u)) (hGapInf n u)

end InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
