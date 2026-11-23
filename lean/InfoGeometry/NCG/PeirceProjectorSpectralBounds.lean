/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.OppositePeirceRealMetric
import InfoGeometry.Core.PeirceStarCharges
import InfoGeometry.Core.PeirceCoupledCorners
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Peirce projector spectral bounds, adjoint regimes, and hyperbolic-plane separation

This module separates the positive Hilbert adjoint (`Fᵀ = F`, i.e., `Y = Xᵀ`),
the diagonal Krein adjoint (`Γ * Fᵀ * Γ = F`, i.e., `Y = -Xᵀ`), and the swap
Krein adjoint (`J * Fᵀ * J = F`, i.e., `Xᵀ = X ∧ Yᵀ = Y`) on both `2 × 2` block
matrices over `n ⊕ n` and general Hermitian Peirce cuts `P`.

It further establishes the orthogonal-projector `1/4` and `3/4` Loewner bounds
via the associative idempotency defect law
`(T - T²) + (G - G²) = F² - even P (Ω² - Ω)`, separates the unilateral nilpotent
regime (`X = 0, Y ≠ 0 ⇒ F² = 0`), and provides the concrete `2 × 2` hyperbolic
plane witness `F² = -1` bridged to `InfoGeometry.Krein.clockAxis`.
-/

namespace InfoGeometry.NCG.PeirceProjectorSpectralBounds

open Matrix
open InfoGeometry.Core.IdempotencyDefect
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.PeirceStarCharges
open InfoGeometry.Core.PeirceCoupledCorners
open InfoGeometry.NCG.OppositePeirceCoupling
open InfoGeometry.NCG.OppositePeirceTrace
open InfoGeometry.NCG.OppositePeirceRealMetric

section BlockOperators

variable {n : Type*}

/-- Odd block matrix `[[0, X], [Y, 0]]` with `X` in `(0, 1)` (`peirce10`) and
`Y` in `(1, 0)` (`peirce01`). -/
def blockOdd (X Y : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks 0 X Y 0

/-- Diagonal grading symmetry `Γ = diag(I, -I)` on `n ⊕ n`. -/
def blockGamma (n : Type*) [DecidableEq n] : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Cross-sheet swap fundamental symmetry `J = [[0, I], [I, 0]]` on `n ⊕ n`. -/
def blockSwap (n : Type*) [DecidableEq n] : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks 0 1 1 0

/-- Canonical top-left Peirce projector `P = diag(I, 0)` on `n ⊕ n`. -/
def blockCut (n : Type*) [DecidableEq n] : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks 1 0 0 0

section BlockBasic

theorem blockOdd_transpose (X Y : Matrix n n ℝ) :
    (blockOdd X Y)ᵀ = blockOdd Yᵀ Xᵀ := by
  simp [blockOdd, Matrix.fromBlocks_transpose]

theorem blockOdd_conjTranspose (X Y : Matrix n n ℝ) :
    (blockOdd X Y)ᴴ = blockOdd Yᵀ Xᵀ := by
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, blockOdd_transpose]

theorem blockOdd_transpose_eq_iff (X Y : Matrix n n ℝ) :
    (blockOdd X Y)ᵀ = blockOdd X Y ↔ Y = Xᵀ := by
  rw [blockOdd_transpose, blockOdd, blockOdd, Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨_, _, hY, _⟩
    exact hY.symm
  · intro h
    refine ⟨rfl, ?_, h.symm, rfl⟩
    rw [h, Matrix.transpose_transpose]

theorem blockOdd_isHermitian_iff (X Y : Matrix n n ℝ) :
    (blockOdd X Y).IsHermitian ↔ Y = Xᵀ := by
  change (blockOdd X Y)ᴴ = blockOdd X Y ↔ Y = Xᵀ
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact blockOdd_transpose_eq_iff X Y

variable [Fintype n] [DecidableEq n]

theorem blockCut_isIdempotent : IsIdempotentElem (blockCut n) := by
  change blockCut n * blockCut n = blockCut n
  simp [blockCut, Matrix.fromBlocks_multiply]

omit [Fintype n] in
theorem blockCut_isHermitian : (blockCut n).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [blockCut, Matrix.fromBlocks_transpose]

omit [Fintype n] in
theorem one_sub_blockCut :
    (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) - blockCut n = Matrix.fromBlocks 0 0 0 1 := by
  ext i j
  cases i <;> cases j <;> simp [blockCut, Matrix.one_apply]

theorem blockGamma_sq : blockGamma n * blockGamma n = 1 := by
  simp [blockGamma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem blockSwap_sq : blockSwap n * blockSwap n = 1 := by
  simp [blockSwap, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem blockOdd_sq (X Y : Matrix n n ℝ) :
    blockOdd X Y * blockOdd X Y = Matrix.fromBlocks (X * Y) 0 0 (Y * X) := by
  simp [blockOdd, Matrix.fromBlocks_multiply]

theorem blockGamma_kreinAdjoint_blockOdd (X Y : Matrix n n ℝ) :
    blockGamma n * (blockOdd X Y)ᵀ * blockGamma n = blockOdd (-Yᵀ) (-Xᵀ) := by
  rw [blockOdd_transpose]
  simp [blockGamma, blockOdd, Matrix.fromBlocks_multiply]

theorem blockOdd_gamma_kreinSelfAdjoint_iff (X Y : Matrix n n ℝ) :
    blockGamma n * (blockOdd X Y)ᵀ * blockGamma n = blockOdd X Y ↔ Y = -Xᵀ := by
  rw [blockGamma_kreinAdjoint_blockOdd, blockOdd, blockOdd, Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨_, _, hY, _⟩
    exact hY.symm
  · intro h
    refine ⟨rfl, ?_, h.symm, rfl⟩
    rw [h, Matrix.transpose_neg, Matrix.transpose_transpose, neg_neg]

theorem blockSwap_kreinAdjoint_blockOdd (X Y : Matrix n n ℝ) :
    blockSwap n * (blockOdd X Y)ᵀ * blockSwap n = blockOdd Xᵀ Yᵀ := by
  rw [blockOdd_transpose]
  simp [blockSwap, blockOdd, Matrix.fromBlocks_multiply]

theorem blockOdd_swap_kreinSelfAdjoint_iff (X Y : Matrix n n ℝ) :
    blockSwap n * (blockOdd X Y)ᵀ * blockSwap n = blockOdd X Y ↔ Xᵀ = X ∧ Yᵀ = Y := by
  rw [blockSwap_kreinAdjoint_blockOdd, blockOdd, blockOdd, Matrix.fromBlocks_inj]
  simp

theorem component10_blockCut_blockOdd (X Y : Matrix n n ℝ) :
    component10 (blockCut n) (blockOdd X Y) = blockOdd X 0 := by
  rw [component10, complementIdempotent, one_sub_blockCut]
  simp [blockCut, blockOdd, Matrix.fromBlocks_multiply]

theorem component01_blockCut_blockOdd (X Y : Matrix n n ℝ) :
    component01 (blockCut n) (blockOdd X Y) = blockOdd 0 Y := by
  rw [component01, complementIdempotent, one_sub_blockCut]
  simp [blockCut, blockOdd, Matrix.fromBlocks_multiply]

omit [DecidableEq n] in
theorem blockOdd_posAdjoint_sq_posSemidef (X : Matrix n n ℝ) :
    (blockOdd X Xᵀ * blockOdd X Xᵀ).PosSemidef := by
  have hH : (blockOdd X Xᵀ).IsHermitian := (blockOdd_isHermitian_iff X Xᵀ).mpr rfl
  nth_rw 2 [← hH.eq]
  exact Matrix.posSemidef_self_mul_conjTranspose (blockOdd X Xᵀ)

theorem blockOdd_posAdjoint_sq_posDef_iff (X : Matrix n n ℝ) :
    (blockOdd X Xᵀ * blockOdd X Xᵀ).PosDef ↔
      (∀ v : n → ℝ, X *ᵥ v = 0 → v = 0) ∧ (∀ v : n → ℝ, Xᵀ *ᵥ v = 0 → v = 0) := by
  have hpeirce :
      component10 (blockCut n) (blockOdd X 0) +
          component01 (blockCut n) (blockOdd X 0)ᴴ = blockOdd X Xᵀ := by
    rw [component10_blockCut_blockOdd, blockOdd_conjTranspose, component01_blockCut_blockOdd]
    simp [blockOdd, Matrix.fromBlocks_add]
  have hiff := OppositePeirceRealMetric.square_posDef_iff
    (blockCut_isIdempotent (n := n)) (blockCut_isHermitian (n := n)) (blockOdd X 0)
  rw [hpeirce, component10_blockCut_blockOdd, blockOdd_conjTranspose, Matrix.transpose_zero] at hiff
  rw [hiff]
  have hmulX (v₁ v₂ : n → ℝ) :
      blockOdd X 0 *ᵥ Sum.elim v₁ v₂ = Sum.elim (X *ᵥ v₂) (0 : n → ℝ) := by
    simp [blockOdd, Matrix.fromBlocks_mulVec]
  have hmulXT (v₁ v₂ : n → ℝ) :
      blockOdd 0 Xᵀ *ᵥ Sum.elim v₁ v₂ = Sum.elim (0 : n → ℝ) (Xᵀ *ᵥ v₁) := by
    simp [blockOdd, Matrix.fromBlocks_mulVec]
  constructor
  · intro h
    constructor
    · intro v₂ hv₂
      have hsum : Sum.elim (0 : n → ℝ) v₂ = 0 := by
        apply h (Sum.elim 0 v₂)
        · rw [hmulX, hv₂, Sum.elim_zero_zero]
        · rw [hmulXT, Matrix.mulVec_zero, Sum.elim_zero_zero]
      exact funext fun i => congrFun hsum (Sum.inr i)
    · intro v₁ hv₁
      have hsum : Sum.elim v₁ (0 : n → ℝ) = 0 := by
        apply h (Sum.elim v₁ 0)
        · rw [hmulX, Matrix.mulVec_zero, Sum.elim_zero_zero]
        · rw [hmulXT, hv₁, Sum.elim_zero_zero]
      exact funext fun i => congrFun hsum (Sum.inl i)
  · rintro ⟨hX, hXT⟩ v hv₁ hv₂
    have hv : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := (Sum.elim_comp_inl_inr v).symm
    rw [hv] at hv₁ hv₂ ⊢
    rw [hmulX] at hv₁
    rw [hmulXT] at hv₂
    have hXinr : X *ᵥ (v ∘ Sum.inr) = 0 :=
      funext fun i => congrFun hv₁ (Sum.inl i)
    have hXTinl : Xᵀ *ᵥ (v ∘ Sum.inl) = 0 :=
      funext fun i => congrFun hv₂ (Sum.inr i)
    rw [hX _ hXinr, hXT _ hXTinl, Sum.elim_zero_zero]

theorem blockOdd_neg_posAdjoint_sq_eq (X : Matrix n n ℝ) :
    -(blockOdd X (-Xᵀ) * blockOdd X (-Xᵀ)) = blockOdd X Xᵀ * blockOdd X Xᵀ := by
  rw [blockOdd_sq, blockOdd_sq, Matrix.fromBlocks_neg]
  simp

theorem blockOdd_gamma_kreinSelfAdjoint_neg_sq_posSemidef (X : Matrix n n ℝ) :
    (-(blockOdd X (-Xᵀ) * blockOdd X (-Xᵀ))).PosSemidef := by
  rw [blockOdd_neg_posAdjoint_sq_eq]
  exact blockOdd_posAdjoint_sq_posSemidef X

omit [DecidableEq n] in
theorem trace_fromBlocks_sum (A B C D : Matrix n n ℝ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem blockOdd_gamma_kreinSelfAdjoint_sq_not_posSemidef {X : Matrix n n ℝ} (hX : X ≠ 0) :
    ¬ (blockOdd X (-Xᵀ) * blockOdd X (-Xᵀ)).PosSemidef := by
  intro hps
  have htr : 0 ≤ Matrix.trace (blockOdd X (-Xᵀ) * blockOdd X (-Xᵀ)) := hps.trace_nonneg
  have hneg : Matrix.trace (blockOdd X (-Xᵀ) * blockOdd X (-Xᵀ)) =
      -(Matrix.trace (X * Xᵀ) + Matrix.trace (Xᵀ * X)) := by
    rw [blockOdd_sq, trace_fromBlocks_sum]
    simp [Matrix.trace_neg]
    abel
  have hpos1 : 0 < Matrix.trace (X * Xᴴ) := by
    have hnn : 0 ≤ Matrix.trace (X * Xᴴ) := (Matrix.posSemidef_self_mul_conjTranspose X).trace_nonneg
    have hne : Matrix.trace (X * Xᴴ) ≠ 0 := fun hz =>
      hX (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hz)
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  have hnn2 : 0 ≤ Matrix.trace (Xᴴ * X) := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpos1 hnn2
  have hsum_pos : 0 < Matrix.trace (X * Xᵀ) + Matrix.trace (Xᵀ * X) :=
    add_pos_of_pos_of_nonneg hpos1 hnn2
  rw [hneg] at htr
  exact (not_le_of_gt (neg_lt_zero.mpr hsum_pos)) htr

end BlockBasic

end BlockOperators

section AdjointRegimes

/-- F2: Complete `2 × 2` block comparison separating:
1. Positive adjoint `Fᵀ = F` (`Y = Xᵀ`), yielding `(F * F).PosSemidef` and trivial-kernel `PosDef` iff;
2. Diagonal Krein adjoint `Γ * Fᵀ * Γ = F` (`Γ = diag(I, -I)`), yielding `Y = -Xᵀ`, `(-(F * F)).PosSemidef`, and `X ≠ 0 → ¬ (F * F).PosSemidef`;
3. Swap Krein adjoint `J * Fᵀ * J = F` (`J = [[0, I], [I, 0]]`), yielding `Xᵀ = X ∧ Yᵀ = Y` and permitting unilateral nilpotent `X = 0, Y = Yᵀ ≠ 0`. -/
theorem indefinite_vs_positive_adjoint_blocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℝ) :
    (((blockOdd X Y)ᵀ = blockOdd X Y ↔ Y = Xᵀ) ∧
      (blockOdd X Xᵀ * blockOdd X Xᵀ).PosSemidef ∧
      ((blockOdd X Xᵀ * blockOdd X Xᵀ).PosDef ↔
        (∀ v : n → ℝ, X *ᵥ v = 0 → v = 0) ∧ (∀ v : n → ℝ, Xᵀ *ᵥ v = 0 → v = 0))) ∧
    ((blockGamma n * (blockOdd X Y)ᵀ * blockGamma n = blockOdd X Y ↔ Y = -Xᵀ) ∧
      (-(blockOdd X (-Xᵀ) * blockOdd X (-Xᵀ))).PosSemidef ∧
      (X ≠ 0 → ¬ (blockOdd X (-Xᵀ) * blockOdd X (-Xᵀ)).PosSemidef)) ∧
    ((blockSwap n * (blockOdd X Y)ᵀ * blockSwap n = blockOdd X Y ↔ Xᵀ = X ∧ Yᵀ = Y) ∧
      (Yᵀ = Y → Y ≠ 0 →
        blockSwap n * (blockOdd (0 : Matrix n n ℝ) Y)ᵀ * blockSwap n = blockOdd 0 Y ∧
        blockOdd (0 : Matrix n n ℝ) Y ≠ 0 ∧
        blockOdd (0 : Matrix n n ℝ) Y * blockOdd (0 : Matrix n n ℝ) Y = 0)) := by
  refine ⟨⟨blockOdd_transpose_eq_iff X Y, blockOdd_posAdjoint_sq_posSemidef X,
      blockOdd_posAdjoint_sq_posDef_iff X⟩,
    ⟨blockOdd_gamma_kreinSelfAdjoint_iff X Y, blockOdd_gamma_kreinSelfAdjoint_neg_sq_posSemidef X,
      fun hX => blockOdd_gamma_kreinSelfAdjoint_sq_not_posSemidef hX⟩,
    ⟨blockOdd_swap_kreinSelfAdjoint_iff X Y, fun hYT hYne => ?_⟩⟩
  refine ⟨(blockOdd_swap_kreinSelfAdjoint_iff 0 Y).mpr ⟨Matrix.transpose_zero, hYT⟩, ?_, ?_⟩
  · intro h0
    apply hYne
    have h0' : blockOdd (0 : Matrix n n ℝ) Y = blockOdd (0 : Matrix n n ℝ) 0 := by
      simpa [blockOdd] using h0
    exact (Matrix.fromBlocks_inj.mp h0').2.2.1
  · rw [blockOdd_sq]
    simp

/-- Companion F2 theorem for a general Hermitian Peirce cut `P` (`P² = P`, `P.IsHermitian`),
covering both the `OppositePeirceRealMetric` parameterization `F = component10 P A + component01 P Aᴴ`
and arbitrary independent corners `X ∈ peirce10 P`, `Y ∈ peirce01 P`. -/
theorem peirce_indefinite_vs_positive_adjoint
    {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix m m ℝ} (hP : IsIdempotentElem P) (hPs : P.IsHermitian) :
    (∀ (A : Matrix m m ℝ),
      let F : Matrix m m ℝ := component10 P A + component01 P Aᴴ
      F.IsHermitian ∧
      (F * F).PosSemidef ∧
      ((F * F).PosDef ↔
        ∀ v : m → ℝ, component10 P A *ᵥ v = 0 → (component10 P A)ᴴ *ᵥ v = 0 → v = 0) ∧
      (reflection P * (reflection P * F)ᵀ * reflection P = reflection P * F) ∧
      (-((reflection P * F) * (reflection P * F))).PosSemidef ∧
      (component10 P A ≠ 0 → ¬ ((reflection P * F) * (reflection P * F)).PosSemidef)) ∧
    (∀ {X Y : Matrix m m ℝ}, X ∈ peirce10 P → Y ∈ peirce01 P →
      (((X + Y)ᵀ = X + Y ↔ Y = Xᵀ) ∧
        ((X + Xᵀ) * (X + Xᵀ)).PosSemidef ∧
        (((X + Xᵀ) * (X + Xᵀ)).PosDef ↔
          ∀ v : m → ℝ, X *ᵥ v = 0 → Xᵀ *ᵥ v = 0 → v = 0)) ∧
      ((reflection P * (X + Y)ᵀ * reflection P = X + Y ↔ Y = -Xᵀ) ∧
        (-((X + (-Xᵀ)) * (X + (-Xᵀ)))).PosSemidef ∧
        (X ≠ 0 → ¬ ((X + (-Xᵀ)) * (X + (-Xᵀ))).PosSemidef))) := by
  constructor
  · intro A
    dsimp only
    refine ⟨adjoint_sum_isHermitian hPs A, adjoint_sum_sq_posSemidef hP hPs A,
      square_posDef_iff hP hPs A, ?_, ?_, fun hX => graded_square_not_posSemidef hP hPs A hX⟩
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        graded_krein_selfadjoint hP hPs A
    · rw [graded_square hP A Aᴴ, neg_neg]
      exact adjoint_sum_sq_posSemidef hP hPs A
  · intro X Y hX hY
    have hXT01 : Xᵀ ∈ peirce01 P := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact star_mem_peirce01 hPs.isSelfAdjoint hX
    have hYT10 : Yᵀ ∈ peirce10 P := by
      rcases hY with ⟨b, rfl⟩
      refine ⟨bᵀ, ?_⟩
      change ((1 - P) * b * P)ᵀ = P * bᵀ * (1 - P)
      have hPT : Pᵀ = P := by
        rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hPs.eq]
      simp only [Matrix.transpose_mul, Matrix.transpose_sub,
        Matrix.transpose_one, hPT, mul_assoc]
    have hcomp10X : component10 P X = X := component10_fixed hP hX
    have hcomp01XT : component01 P Xᴴ = Xᵀ := by
      rw [component01_conjTranspose hPs X, hcomp10X,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    have hpos_iff : (X + Y)ᵀ = X + Y ↔ Y = Xᵀ := by
      constructor
      · intro h
        have h10 := congrArg (component10 P) h
        rw [Matrix.transpose_add, add_comm Xᵀ Yᵀ, component10_coupled hP hYT10 hXT01,
          component10_coupled hP hX hY] at h10
        have h' := congrArg Matrix.transpose h10
        simpa [Matrix.transpose_transpose] using h'
      · rintro rfl
        rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
    have hpos_psd : ((X + Xᵀ) * (X + Xᵀ)).PosSemidef := by
      have h := adjoint_sum_sq_posSemidef hP hPs X
      rwa [hcomp10X, hcomp01XT] at h
    have hpos_pd :
        ((X + Xᵀ) * (X + Xᵀ)).PosDef ↔
          ∀ v : m → ℝ, X *ᵥ v = 0 → Xᵀ *ᵥ v = 0 → v = 0 := by
      have h := square_posDef_iff hP hPs X
      rwa [hcomp10X, hcomp01XT, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have hkrein_iff : reflection P * (X + Y)ᵀ * reflection P = X + Y ↔ Y = -Xᵀ := by
      rw [Matrix.transpose_add, add_comm Xᵀ Yᵀ, coupled_conjugation hP hYT10 hXT01]
      constructor
      · intro h
        have hneg : -(Yᵀ + Xᵀ) = X + Y := h
        have h10 := congrArg (component10 P) hneg
        have hcomp_neg : component10 P (-(Yᵀ + Xᵀ)) = -component10 P (Yᵀ + Xᵀ) := by
          simp only [component10]
          noncomm_ring
        rw [hcomp_neg, component10_coupled hP hYT10 hXT01, component10_coupled hP hX hY] at h10
        have h' := congrArg Matrix.transpose h10
        rw [Matrix.transpose_neg, Matrix.transpose_transpose] at h'
        exact neg_eq_iff_eq_neg.mp h'
      · rintro rfl
        rw [Matrix.transpose_neg, Matrix.transpose_transpose]
        abel
    have hneg_eq : -((X + (-Xᵀ)) * (X + (-Xᵀ))) = (X + Xᵀ) * (X + Xᵀ) := by
      have hXX : X * X = 0 := peirce10_mul_peirce10_eq_zero P hP.eq hX hX
      have hXTXT : Xᵀ * Xᵀ = 0 := peirce01_mul_peirce01_eq_zero P hP.eq hXT01 hXT01
      have hpos_expand : (X + Xᵀ) * (X + Xᵀ) = X * Xᵀ + Xᵀ * X := by
        calc
          (X + Xᵀ) * (X + Xᵀ) = X * X + X * Xᵀ + Xᵀ * X + Xᵀ * Xᵀ := by noncomm_ring
          _ = X * Xᵀ + Xᵀ * X := by rw [hXX, hXTXT]; abel
      calc
        -((X + (-Xᵀ)) * (X + (-Xᵀ))) =
            -(X * X - X * Xᵀ - Xᵀ * X + Xᵀ * Xᵀ) := by noncomm_ring
        _ = X * Xᵀ + Xᵀ * X := by rw [hXX, hXTXT]; noncomm_ring
        _ = (X + Xᵀ) * (X + Xᵀ) := hpos_expand.symm
    have hkrein_psd : (-((X + (-Xᵀ)) * (X + (-Xᵀ)))).PosSemidef := by
      rw [hneg_eq]
      exact hpos_psd
    have hkrein_not_psd : X ≠ 0 → ¬ ((X + (-Xᵀ)) * (X + (-Xᵀ))).PosSemidef := by
      intro hXne hps
      have htr : 0 ≤ Matrix.trace ((X + (-Xᵀ)) * (X + (-Xᵀ))) := hps.trace_nonneg
      have hneg_tr : Matrix.trace ((X + (-Xᵀ)) * (X + (-Xᵀ))) =
          -Matrix.trace ((X + Xᵀ) * (X + Xᵀ)) := by
        calc
          Matrix.trace ((X + (-Xᵀ)) * (X + (-Xᵀ))) =
              Matrix.trace (-(-((X + (-Xᵀ)) * (X + (-Xᵀ))))) := by rw [neg_neg]
          _ = -Matrix.trace ((X + Xᵀ) * (X + Xᵀ)) := by rw [Matrix.trace_neg, hneg_eq]
      have htr_pos : 0 < Matrix.trace ((X + Xᵀ) * (X + Xᵀ)) := by
        have h := trace_square_pos_iff hP hPs X
        rw [hcomp10X, hcomp01XT] at h
        exact h.mpr hXne
      rw [hneg_tr] at htr
      exact (not_le_of_gt (neg_lt_zero.mpr htr_pos)) htr
    exact ⟨⟨hpos_iff, hpos_psd, hpos_pd⟩, ⟨hkrein_iff, hkrein_psd, hkrein_not_psd⟩⟩

end AdjointRegimes

section ProjectorSpectralBounds

/-- Ring-generic Peirce idempotency defect law:
`(T - T²) + (G - G²) = F² - even P (Ω² - Ω)` where `T = component11 P Ω`,
`G = component00 P Ω`, and `F = odd P Ω`. -/
theorem peirce_idempotencyDefect_law {A : Type*} [Ring A] {P : A}
    (hP : IsIdempotentElem P) (Ω : A) :
    let T := component11 P Ω
    let G := component00 P Ω
    let F := odd P Ω
    (T - T * T) + (G - G * G) = F * F - even P (Ω * Ω - Ω) := by
  dsimp only
  have hcomp := idempotencyDefect_peirce_components P Ω hP.eq
  have hodd : odd P Ω * odd P Ω =
      component10 P Ω * component01 P Ω + component01 P Ω * component10 P Ω := by
    simpa [pow_two] using odd_square hP Ω
  have hev : even P (Ω * Ω - Ω) =
      component11 P (Ω * Ω - Ω) + component00 P (Ω * Ω - Ω) := rfl
  rw [hev, hcomp.1, hcomp.2.2.2, hodd]
  abel

/-- Algebra-generic quarter-square identity for two idempotents `P, Ω`:
`(1/4 : ℝ) • 1 - odd P Ω * odd P Ω = (even P Ω - (1/2 : ℝ) • 1)²`. -/
theorem peirce_projector_quarter_sq_identity {A : Type*} [Ring A] [Algebra ℝ A]
    {P Ω : A} (hP : IsIdempotentElem P) (hΩ : IsIdempotentElem Ω) :
    (1 / 4 : ℝ) • (1 : A) - odd P Ω * odd P Ω =
      (even P Ω - (1 / 2 : ℝ) • (1 : A)) * (even P Ω - (1 / 2 : ℝ) • (1 : A)) := by
  have hdef := peirce_idempotencyDefect_law hP Ω
  dsimp only at hdef
  have hΩz : Ω * Ω - Ω = 0 := sub_eq_zero.mpr hΩ.eq
  rw [hΩz, map_zero, sub_zero] at hdef
  have hTG : component11 P Ω * component00 P Ω = 0 :=
    peirce11_mul_peirce00_eq_zero P hP.eq (component11_mem P Ω) (component00_mem P Ω)
  have hGT : component00 P Ω * component11 P Ω = 0 :=
    peirce00_mul_peirce11_eq_zero P hP.eq (component00_mem P Ω) (component11_mem P Ω)
  have hev_sq :
      even P Ω * even P Ω =
        component11 P Ω * component11 P Ω + component00 P Ω * component00 P Ω := by
    change (component11 P Ω + component00 P Ω) * (component11 P Ω + component00 P Ω) = _
    calc
      (component11 P Ω + component00 P Ω) * (component11 P Ω + component00 P Ω) =
          component11 P Ω * component11 P Ω + component11 P Ω * component00 P Ω +
            component00 P Ω * component11 P Ω + component00 P Ω * component00 P Ω := by
          noncomm_ring
      _ = component11 P Ω * component11 P Ω + component00 P Ω * component00 P Ω := by
          rw [hTG, hGT, add_zero, add_zero]
  have hF_sq : odd P Ω * odd P Ω = even P Ω - even P Ω * even P Ω := by
    rw [← hdef, hev_sq]
    change (component11 P Ω - component11 P Ω * component11 P Ω) +
        (component00 P Ω - component00 P Ω * component00 P Ω) =
      (component11 P Ω + component00 P Ω) -
        (component11 P Ω * component11 P Ω + component00 P Ω * component00 P Ω)
    abel
  have hhalf_add : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  have hhalf_mul : (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 := by norm_num
  have hE_expand :
      (even P Ω - (1 / 2 : ℝ) • (1 : A)) * (even P Ω - (1 / 2 : ℝ) • (1 : A)) =
        even P Ω * even P Ω - even P Ω + (1 / 4 : ℝ) • (1 : A) := by
    have hsmul : (1 / 2 : ℝ) • even P Ω + (1 / 2 : ℝ) • even P Ω = even P Ω := by
      rw [← add_smul, hhalf_add, one_smul]
    calc
      (even P Ω - (1 / 2 : ℝ) • (1 : A)) * (even P Ω - (1 / 2 : ℝ) • (1 : A)) =
          even P Ω * even P Ω - (1 / 2 : ℝ) • even P Ω -
            ((1 / 2 : ℝ) • even P Ω - (1 / 4 : ℝ) • (1 : A)) := by
          rw [sub_mul, mul_sub, mul_sub]
          simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, hhalf_mul]
      _ = even P Ω * even P Ω - ((1 / 2 : ℝ) • even P Ω + (1 / 2 : ℝ) • even P Ω) +
            (1 / 4 : ℝ) • (1 : A) := by abel
      _ = even P Ω * even P Ω - even P Ω + (1 / 4 : ℝ) • (1 : A) := by rw [hsmul]
  rw [hF_sq, hE_expand]
  abel

section MatrixBounds

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem even_isHermitian {P Ω : Matrix m m ℝ}
    (hPs : P.IsHermitian) (hΩs : Ω.IsHermitian) :
    (even P Ω).IsHermitian := by
  change (P * Ω * P + (1 - P) * Ω * (1 - P))ᴴ = P * Ω * P + (1 - P) * Ω * (1 - P)
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hPs.eq, hΩs.eq, mul_assoc]

theorem odd_isHermitian {P Ω : Matrix m m ℝ}
    (hPs : P.IsHermitian) (hΩs : Ω.IsHermitian) :
    (odd P Ω).IsHermitian := by
  exact odd_isSelfAdjoint hPs hΩs

/-- F3: Orthogonal-projector spectral bound `0 ≤ F² ≤ (1/4) I` in `Matrix.PosSemidef` order,
together with the explicit shifted square identity `(1/4) I - F² = (even P Ω - (1/2) I)²`. -/
theorem orthogonalProjector_F_sq_le_quarter
    {P Ω : Matrix m m ℝ}
    (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (hΩ : IsIdempotentElem Ω) (hΩs : Ω.IsHermitian) :
    let F : Matrix m m ℝ := odd P Ω
    (F * F).PosSemidef ∧
    ((1 / 4 : ℝ) • (1 : Matrix m m ℝ) - F * F).PosSemidef ∧
    ((1 / 4 : ℝ) • (1 : Matrix m m ℝ) - F * F =
      (even P Ω - (1 / 2 : ℝ) • (1 : Matrix m m ℝ)) *
        (even P Ω - (1 / 2 : ℝ) • (1 : Matrix m m ℝ))) := by
  dsimp only
  have hF_herm : (odd P Ω).IsHermitian := odd_isHermitian hPs hΩs
  have hF_psd : (odd P Ω * odd P Ω).PosSemidef := by
    nth_rw 2 [← hF_herm.eq]
    exact Matrix.posSemidef_self_mul_conjTranspose (odd P Ω)
  have hid := peirce_projector_quarter_sq_identity hP hΩ
  have hM_herm : (even P Ω - (1 / 2 : ℝ) • (1 : Matrix m m ℝ)).IsHermitian :=
    (even_isHermitian hPs hΩs).sub
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all (1 / 2 : ℝ)))
  have hM_psd :
      ((even P Ω - (1 / 2 : ℝ) • (1 : Matrix m m ℝ)) *
        (even P Ω - (1 / 2 : ℝ) • (1 : Matrix m m ℝ))).PosSemidef := by
    nth_rw 2 [← hM_herm.eq]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  refine ⟨hF_psd, ?_, hid⟩
  rw [hid]
  exact hM_psd

/-- F3: Complementary orthogonal-projector spectral bound `I - F² ≥ (3/4) I` and strict
positive definiteness `(I - F²).PosDef`. -/
theorem orthogonalProjector_one_sub_F_sq_ge_three_quarters
    {P Ω : Matrix m m ℝ}
    (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (hΩ : IsIdempotentElem Ω) (hΩs : Ω.IsHermitian) :
    let F : Matrix m m ℝ := odd P Ω
    (((1 : Matrix m m ℝ) - F * F) - (3 / 4 : ℝ) • (1 : Matrix m m ℝ)).PosSemidef ∧
    ((1 : Matrix m m ℝ) - F * F).PosDef := by
  dsimp only
  have hquarter := (orthogonalProjector_F_sq_le_quarter hP hPs hΩ hΩs).2.1
  have hsub_eq :
      ((1 : Matrix m m ℝ) - odd P Ω * odd P Ω) - (3 / 4 : ℝ) • (1 : Matrix m m ℝ) =
        (1 / 4 : ℝ) • (1 : Matrix m m ℝ) - odd P Ω * odd P Ω := by
    have hcoeff : (1 : ℝ) - (3 / 4 : ℝ) = 1 / 4 := by norm_num
    calc
      ((1 : Matrix m m ℝ) - odd P Ω * odd P Ω) - (3 / 4 : ℝ) • (1 : Matrix m m ℝ) =
          ((1 : ℝ) • (1 : Matrix m m ℝ) - (3 / 4 : ℝ) • (1 : Matrix m m ℝ)) -
            odd P Ω * odd P Ω := by
          rw [one_smul]; abel
      _ = (1 / 4 : ℝ) • (1 : Matrix m m ℝ) - odd P Ω * odd P Ω := by
          rw [← sub_smul, hcoeff]
  have hge : (((1 : Matrix m m ℝ) - odd P Ω * odd P Ω) -
      (3 / 4 : ℝ) • (1 : Matrix m m ℝ)).PosSemidef := by
    rw [hsub_eq]
    exact hquarter
  refine ⟨hge, ?_⟩
  have hdecomp :
      (1 : Matrix m m ℝ) - odd P Ω * odd P Ω =
        (3 / 4 : ℝ) • (1 : Matrix m m ℝ) +
          (((1 : Matrix m m ℝ) - odd P Ω * odd P Ω) - (3 / 4 : ℝ) • (1 : Matrix m m ℝ)) := by
    abel
  rw [hdecomp]
  exact ((Matrix.PosDef.one (R := ℝ) (n := m)).smul (by norm_num)).add_posSemidef hge

/-- Quadratic-form readout of the `1/4` and `3/4` bounds for arbitrary vectors `v : m → ℝ`. -/
theorem orthogonalProjector_quadForm_bounds
    {P Ω : Matrix m m ℝ}
    (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (hΩ : IsIdempotentElem Ω) (hΩs : Ω.IsHermitian)
    (v : m → ℝ) :
    0 ≤ v ⬝ᵥ (odd P Ω * odd P Ω) *ᵥ v ∧
    v ⬝ᵥ (odd P Ω * odd P Ω) *ᵥ v ≤ (1 / 4 : ℝ) * (v ⬝ᵥ v) ∧
    (3 / 4 : ℝ) * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((1 : Matrix m m ℝ) - odd P Ω * odd P Ω) *ᵥ v := by
  have hq := orthogonalProjector_F_sq_le_quarter hP hPs hΩ hΩs
  have h3q := orthogonalProjector_one_sub_F_sq_ge_three_quarters hP hPs hΩ hΩs
  have hv1 : 0 ≤ v ⬝ᵥ (odd P Ω * odd P Ω) *ᵥ v := by
    simpa using hq.1.dotProduct_mulVec_nonneg v
  have hv2 : 0 ≤ v ⬝ᵥ ((1 / 4 : ℝ) • (1 : Matrix m m ℝ) - odd P Ω * odd P Ω) *ᵥ v := by
    simpa using hq.2.1.dotProduct_mulVec_nonneg v
  have hv3 : 0 ≤ v ⬝ᵥ (((1 : Matrix m m ℝ) - odd P Ω * odd P Ω) -
      (3 / 4 : ℝ) • (1 : Matrix m m ℝ)) *ᵥ v := by
    simpa using h3q.1.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hv2 hv3
  refine ⟨hv1, sub_nonneg.mp hv2, sub_nonneg.mp hv3⟩

/-- `2 × 2` block specialization of the orthogonal-projector `1/4` and `3/4` bounds
for an orthogonal projection `Ω = Matrix.fromBlocks T X Y G`. -/
theorem orthogonalProjector_block_bounds
    {n : Type*} [Fintype n] [DecidableEq n]
    {T X Y G : Matrix n n ℝ}
    (hΩ : IsIdempotentElem (Matrix.fromBlocks T X Y G))
    (hΩs : (Matrix.fromBlocks T X Y G).IsHermitian) :
    (blockOdd X Y * blockOdd X Y).PosSemidef ∧
    ((1 / 4 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) - blockOdd X Y * blockOdd X Y).PosSemidef ∧
    (((1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) - blockOdd X Y * blockOdd X Y) -
      (3 / 4 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).PosSemidef ∧
    ((1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) - blockOdd X Y * blockOdd X Y).PosDef := by
  have hodd : odd (blockCut n) (Matrix.fromBlocks T X Y G) = blockOdd X Y := by
    rw [odd_apply]
    change component10 (blockCut n) (Matrix.fromBlocks T X Y G) +
        component01 (blockCut n) (Matrix.fromBlocks T X Y G) = blockOdd X Y
    rw [component10, component01, complementIdempotent, one_sub_blockCut]
    simp [blockCut, blockOdd, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  have hq := orthogonalProjector_F_sq_le_quarter
    (blockCut_isIdempotent (n := n)) (blockCut_isHermitian (n := n)) hΩ hΩs
  have h3q := orthogonalProjector_one_sub_F_sq_ge_three_quarters
    (blockCut_isIdempotent (n := n)) (blockCut_isHermitian (n := n)) hΩ hΩs
  rw [hodd] at hq h3q
  exact ⟨hq.1, hq.2.1, h3q.1, h3q.2⟩

end MatrixBounds

end ProjectorSpectralBounds

section UnilateralNilpotent

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- F3: Unilateral nilpotent regime under a general Hermitian Peirce cut `P`:
when `X = 0` and `Y ∈ peirce01 P` is nonzero, `F = 0 + Y ≠ 0` yet `F * F = 0`.
In contrast, positive adjoint symmetry `(X' + Y').IsHermitian` forces `X' = 0 → Y' = 0`. -/
theorem unilateral_nilpotent_F_sq_zero
    {P Y : Matrix m m ℝ}
    (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (hY : Y ∈ peirce01 P) (hYne : Y ≠ 0) :
    let F : Matrix m m ℝ := (0 : Matrix m m ℝ) + Y
    F ≠ 0 ∧ F * F = 0 ∧
      (∀ X' Y' : Matrix m m ℝ, X' ∈ peirce10 P → Y' ∈ peirce01 P →
        (X' + Y').IsHermitian → X' = 0 → Y' = 0 ∧ X' + Y' = 0) := by
  dsimp only
  refine ⟨by simpa using hYne, ?_, ?_⟩
  · rw [zero_add]
    exact peirce01_mul_peirce01_eq_zero P hP.eq hY hY
  · intro X' Y' hX' hY' hHerm hX0
    subst hX0
    rw [zero_add] at hHerm ⊢
    have hPT : Pᴴ = P := hPs.eq
    have hPY : P * Y' = 0 := left_support01 hP hY'
    have hYP : Y' * P = Y' := right_support01 hP hY'
    have hPY' : P * Y' = Y' := by
      calc
        P * Y' = Pᴴ * Y'ᴴ := by rw [hPT, hHerm.eq]
        _ = (Y' * P)ᴴ := by rw [Matrix.conjTranspose_mul]
        _ = Y'ᴴ := by rw [hYP]
        _ = Y' := hHerm.eq
    have hY0 : Y' = 0 := hPY'.symm.trans hPY
    exact ⟨hY0, hY0⟩

/-- F3: `2 × 2` block form of the unilateral nilpotent regime:
for any `Y ≠ 0`, `blockOdd 0 Y ≠ 0`, `blockOdd 0 Y * blockOdd 0 Y = 0`,
if `Yᵀ = Y` then `blockOdd 0 Y` is swap-Krein self-adjoint, and `blockOdd 0 Y`
cannot be positive-adjoint Hermitian (where `X' = 0` forces `Y' = 0`). -/
theorem unilateral_nilpotent_blocks_sq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {Y : Matrix n n ℝ} (hYne : Y ≠ 0) :
    let F : Matrix (n ⊕ n) (n ⊕ n) ℝ := blockOdd (0 : Matrix n n ℝ) Y
    F ≠ 0 ∧ F * F = 0 ∧
      (Yᵀ = Y → blockSwap n * Fᵀ * blockSwap n = F) ∧
      ¬ F.IsHermitian ∧
      (∀ X' Y' : Matrix n n ℝ, (blockOdd X' Y').IsHermitian → X' = 0 →
        Y' = 0 ∧ blockOdd X' Y' = 0) := by
  dsimp only
  have hFne : blockOdd (0 : Matrix n n ℝ) Y ≠ 0 := by
    intro h0
    apply hYne
    have h0' : blockOdd (0 : Matrix n n ℝ) Y = blockOdd (0 : Matrix n n ℝ) 0 := by
      simpa [blockOdd] using h0
    exact (Matrix.fromBlocks_inj.mp h0').2.2.1
  have hFsq : blockOdd (0 : Matrix n n ℝ) Y * blockOdd (0 : Matrix n n ℝ) Y = 0 := by
    rw [blockOdd_sq]
    simp
  have hnotHerm : ¬ (blockOdd (0 : Matrix n n ℝ) Y).IsHermitian := by
    rw [blockOdd_isHermitian_iff, Matrix.transpose_zero]
    exact hYne
  refine ⟨hFne, hFsq, fun hYT => (blockOdd_swap_kreinSelfAdjoint_iff 0 Y).mpr
      ⟨Matrix.transpose_zero, hYT⟩, hnotHerm, ?_⟩
  intro X' Y' hHerm hX0
  subst hX0
  rw [blockOdd_isHermitian_iff, Matrix.transpose_zero] at hHerm
  subst hHerm
  exact ⟨rfl, by simp [blockOdd]⟩

/-- Concrete `2 × 2` unilateral nilpotent witness `F = !![0, 0; 1, 0]` (`X = 0, Y = 1`). -/
theorem unilateral_nilpotent_concrete_witness :
    let F : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    F ≠ 0 ∧ F * F = 0 ∧ J * Fᵀ * J = F ∧ ¬ F.IsHermitian := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h10 := congrFun (congrFun h 1) 0
    simp at h10
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have hFT : (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = !![0, 1; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hFT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro h
    have h01 := congrFun (congrFun h.eq 0) 1
    simp at h01

end UnilateralNilpotent

section HyperbolicPlane

/-- Hyperbolic-plane odd Krein-self-adjoint generator `F = [[0, 1], [-1, 0]]`. -/
def hyperbolicPlaneF : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Diagonal `2 × 2` grading matrix `Γ = [[1, 0], [0, -1]]`. -/
def hyperbolicPlaneGamma : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Cross-sheet swap matrix `J = [[0, 1], [1, 0]]`. -/
def hyperbolicPlaneJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Closed noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` (Trap T16). -/
theorem hyperbolicPlane_gamma_noncomm :
    hyperbolicPlaneGamma * hyperbolicPlaneF ≠ hyperbolicPlaneF * hyperbolicPlaneGamma := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [hyperbolicPlaneGamma, hyperbolicPlaneF, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- F5b: Concrete `2 × 2` hyperbolic-plane witness `F = !![0, 1; -1, 0]`, satisfying
`Γ * Γ = 1`, `{Γ, F} = 0`, `Γ * Fᵀ * Γ = F`, `J * Fᵀ * J = F`, `F * F = -1`,
and `¬ (F * F).PosSemidef`. -/
theorem hyperbolicPlane_kreinSelfAdjoint_sq_neg_one :
    hyperbolicPlaneGamma * hyperbolicPlaneGamma = 1 ∧
    hyperbolicPlaneGamma * hyperbolicPlaneF + hyperbolicPlaneF * hyperbolicPlaneGamma = 0 ∧
    hyperbolicPlaneGamma * hyperbolicPlaneFᵀ * hyperbolicPlaneGamma = hyperbolicPlaneF ∧
    hyperbolicPlaneJ * hyperbolicPlaneFᵀ * hyperbolicPlaneJ = hyperbolicPlaneF ∧
    hyperbolicPlaneF * hyperbolicPlaneF = -(1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    ¬ (hyperbolicPlaneF * hyperbolicPlaneF).PosSemidef := by
  have hGammaSq : hyperbolicPlaneGamma * hyperbolicPlaneGamma = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hyperbolicPlaneGamma, Matrix.mul_apply, Fin.sum_univ_two]
  have hAnti :
      hyperbolicPlaneGamma * hyperbolicPlaneF + hyperbolicPlaneF * hyperbolicPlaneGamma = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hyperbolicPlaneGamma, hyperbolicPlaneF]
  have hFT : hyperbolicPlaneFᵀ = !![0, -1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hyperbolicPlaneF]
  have hGammaSA :
      hyperbolicPlaneGamma * hyperbolicPlaneFᵀ * hyperbolicPlaneGamma = hyperbolicPlaneF := by
    rw [hFT]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hyperbolicPlaneGamma, hyperbolicPlaneF]
  have hJSA :
      hyperbolicPlaneJ * hyperbolicPlaneFᵀ * hyperbolicPlaneJ = hyperbolicPlaneF := by
    rw [hFT]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hyperbolicPlaneJ, hyperbolicPlaneF]
  have hFsq : hyperbolicPlaneF * hyperbolicPlaneF = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hyperbolicPlaneF, Matrix.mul_apply, Fin.sum_univ_two]
  have hNotPos : ¬ (hyperbolicPlaneF * hyperbolicPlaneF).PosSemidef := by
    intro hps
    have hdiag := hps.diag_nonneg (i := (0 : Fin 2))
    rw [hFsq] at hdiag
    simp at hdiag
    norm_num at hdiag
  exact ⟨hGammaSq, hAnti, hGammaSA, hJSA, hFsq, hNotPos⟩

/-- Explicit coordinate linear equivalence `DoubledSpace ℝ ≃ₗ[ℝ] (Fin 2 → ℝ)`. -/
noncomputable def doubledRealEquiv : InfoGeometry.Krein.DoubledSpace ℝ ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun u := ![WithLp.fst u, WithLp.snd u]
  invFun v := InfoGeometry.Krein.to_doubled (v 0) (v 1)
  map_add' u w := by
    ext i
    fin_cases i <;> simp [WithLp.add_fst, WithLp.add_snd]
  map_smul' c u := by
    ext i
    fin_cases i <;> simp [WithLp.smul_fst, WithLp.smul_snd]
  left_inv u := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp
  right_inv v := by
    ext i
    fin_cases i <;> simp

/-- Bridge connecting `hyperbolicPlaneF` / `hyperbolicPlaneGamma` / `hyperbolicPlaneJ`
to `InfoGeometry.Krein.clockAxis`, `RealDoubledChiralKreinAdjoint.clockAxis_isChiralKreinHermitian`,
and `Krein.isKreinSelfAdjoint_complex_i`. -/
theorem hyperbolicPlane_clockAxis_bridge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (∀ u : InfoGeometry.Krein.DoubledSpace ℝ,
      doubledRealEquiv (InfoGeometry.Krein.clockAxis u) =
        (-hyperbolicPlaneF) *ᵥ doubledRealEquiv u) ∧
    (∀ u : InfoGeometry.Krein.DoubledSpace ℝ,
      doubledRealEquiv (-(InfoGeometry.Krein.clockAxis u)) =
        hyperbolicPlaneF *ᵥ doubledRealEquiv u) ∧
    (∀ u : InfoGeometry.Krein.DoubledSpace ℝ,
      doubledRealEquiv (InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.gamma5 u) =
        hyperbolicPlaneGamma *ᵥ doubledRealEquiv u) ∧
    (∀ u : InfoGeometry.Krein.DoubledSpace ℝ,
      doubledRealEquiv (InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.etaChiral u) =
        hyperbolicPlaneJ *ᵥ doubledRealEquiv u) ∧
    (InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint.IsChiralKreinSelfAdjoint
      (InfoGeometry.Krein.clockAxis (E := E))) ∧
    (InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint
      (H := InfoGeometry.Krein.DoubledSpace E) (InfoGeometry.Krein.clockAxis (E := E))) ∧
    ((InfoGeometry.Krein.clockAxis (E := E)).comp (InfoGeometry.Krein.clockAxis (E := E)) =
      -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, InfoGeometry.Krein.clockAxis_sq E⟩
  · intro u
    ext i
    fin_cases i <;>
      simp [doubledRealEquiv, hyperbolicPlaneF, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro u
    ext i
    fin_cases i <;>
      simp [doubledRealEquiv, hyperbolicPlaneF, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro u
    ext i
    fin_cases i <;>
      simp [doubledRealEquiv, hyperbolicPlaneGamma,
        InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.gamma5,
        InfoGeometry.Krein.spectral_epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro u
    ext i
    fin_cases i <;>
      simp [doubledRealEquiv, hyperbolicPlaneJ,
        InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.etaChiral,
        InfoGeometry.Krein.modular_j, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · exact (InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint.isChiralKreinSelfAdjoint_iff_form
      (InfoGeometry.Krein.clockAxis (E := E))).mpr
      (InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint.clockAxis_isChiralKreinHermitian
        (E := E))
  · exact InfoGeometry.Krein.isKreinSelfAdjoint_complex_i (E := E)

end HyperbolicPlane

section NoncommutativityWitnesses

/-- Closed noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` (Trap T16). -/
theorem hyperbolicPlane_mat2_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨hyperbolicPlaneGamma, hyperbolicPlaneF, hyperbolicPlane_gamma_noncomm⟩

/-- Noncommutativity witness for general finite-index real matrices `Matrix m m ℝ` (Trap T16). -/
theorem matrix_mul_noncommutative_of_nontrivial
    {m : Type*} [Fintype m] [DecidableEq m] [Nontrivial m] :
    ∃ A B : Matrix m m ℝ, A * B ≠ B * A := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne m
  let A : Matrix m m ℝ := Matrix.of fun r c => if r = i ∧ c = j then 1 else 0
  let B : Matrix m m ℝ := Matrix.of fun r c => if r = j ∧ c = i then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have hii := congrFun (congrFun h i) i
  have hL : (A * B) i i = 1 := by
    simp [A, B, Matrix.mul_apply]
  have hR : (B * A) i i = 0 := by
    simp [A, B, Matrix.mul_apply, hij]
  rw [hL, hR] at hii
  norm_num at hii

/-- Noncommutativity witness for `2 × 2` block matrices `Matrix (n ⊕ n) (n ⊕ n) ℝ` (Trap T16). -/
theorem blockMatrix_mul_noncommutative_of_nontrivial
    {n : Type*} [Fintype n] [DecidableEq n] [Nontrivial n] :
    ∃ A B : Matrix (n ⊕ n) (n ⊕ n) ℝ, A * B ≠ B * A := by
  obtain ⟨a⟩ := (inferInstance : Nonempty n)
  refine ⟨blockCut n, blockSwap n, ?_⟩
  intro h
  have h01 := congrFun (congrFun h (Sum.inl a)) (Sum.inr a)
  have hL : blockCut n * blockSwap n = Matrix.fromBlocks (0 : Matrix n n ℝ) 1 0 0 := by
    simp [blockCut, blockSwap, Matrix.fromBlocks_multiply]
  have hR : blockSwap n * blockCut n = Matrix.fromBlocks (0 : Matrix n n ℝ) 0 1 0 := by
    simp [blockCut, blockSwap, Matrix.fromBlocks_multiply]
  rw [hL, hR] at h01
  simp at h01

end NoncommutativityWitnesses

end InfoGeometry.NCG.PeirceProjectorSpectralBounds
