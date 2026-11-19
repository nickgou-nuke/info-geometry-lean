/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Core
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Clifford8BdGHorizon
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Supertwistor16AndRealBloch
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSBathAndAnisotropicKuboMori
import InfoGeometry.Modular.SchrodingerGKSL
import InfoGeometry.Modular.SchrodingerGKSLFlowBridge
import InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
import InfoGeometry.Modular.WeldedBlochQuantumSpohnSynthesis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# KMS Complete Positivity, Kraus Semigroup Decomposition, & Flow Unification

This module formalizes:
1. Full $k$-positivity (complete positivity) of `partialTraceKKT : M₈(ℝ) →ₗ[ℝ] M₂(ℝ)` for arbitrary
   finite ancilla index `κ : Type*` (`[Fintype κ] [DecidableEq κ]`), closing the disclaimer
   in `KMSBathAndAnisotropicKuboMori.lean` line 224.
2. The 4-channel time-dependent Kraus decomposition and complete positivity of `thermalSemigroupC`
   and its real specialization `gkslPropagator` at $\omega = 0$, closing the disclaimer in
   `KMSBathAndAnisotropicKuboMori.lean` line 413.
3. The exact generator-flow identity uniting `SchrodingerGKSLFlowBridge.gkslFlow` with
   `thermalSemigroupC`, closing `SchrodingerGKSLFlowBridge.lean` lines 14–15.
4. OpenGauss T16 non-commutativity witness on `Matrix (Fin 8) (Fin 8) ℝ`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSCompletePositivityAndKrausSemigroup

open Matrix
open scoped Kronecker
open InfoGeometry.OperatorAlgebra.PeirceBiSandwich
open InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
open InfoGeometry.Modular.WeldedBlochQuantumSpohnSynthesis

/-! ### Part I: Full k-Positivity of `partialTraceKKT` -/

/-- Kronecker-amplified KKT sector blocks `W_a = 1_κ ⊗ V_a`. -/
def W_KKT (κ : Type*) [Fintype κ] [DecidableEq κ] (a : Fin 4) :
    Matrix (κ × Fin 8) (κ × Fin 2) ℝ :=
  (1 : Matrix κ κ ℝ) ⊗ₖ (V_KKT a)

lemma W_KKT_apply (κ : Type*) [Fintype κ] [DecidableEq κ] (a : Fin 4)
    (k₁ k₂ : κ) (i : Fin 8) (j : Fin 2) :
    W_KKT κ a (k₁, i) (k₂, j) = if k₁ = k₂ then V_KKT a i j else 0 := by
  show ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT a) (k₁, i) (k₂, j) = _
  rw [kronecker_apply, Matrix.one_apply]
  split_ifs with h
  · rw [one_mul]
  · rw [zero_mul]

theorem W_KKT_isometry (κ : Type*) [Fintype κ] [DecidableEq κ] (a : Fin 4) :
    (W_KKT κ a)ᵀ * (W_KKT κ a) = 1 := by
  show ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT a)ᵀ * ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT a) = 1
  rw [← kroneckerMap_transpose (· * ·)]
  rw [← mul_kronecker_mul]
  have h1 : (1 : Matrix κ κ ℝ)ᵀ * (1 : Matrix κ κ ℝ) = 1 := by
    rw [transpose_one, one_mul]
  have h2 : (V_KKT a)ᵀ * (V_KKT a) = 1 := kkt_kraus_isometric_and_completeness.1 a
  rw [h1, h2, one_kronecker_one]

theorem W_KKT_completeness (κ : Type*) [Fintype κ] [DecidableEq κ] :
    ∑ a : Fin 4, (W_KKT κ a) * (W_KKT κ a)ᵀ = 1 := by
  rw [Fin.sum_univ_four]
  show (W_KKT κ 0) * ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT 0)ᵀ +
       (W_KKT κ 1) * ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT 1)ᵀ +
       (W_KKT κ 2) * ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT 2)ᵀ +
       (W_KKT κ 3) * ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT 3)ᵀ = 1
  rw [← kroneckerMap_transpose (· * ·), ← kroneckerMap_transpose (· * ·),
      ← kroneckerMap_transpose (· * ·), ← kroneckerMap_transpose (· * ·)]
  show ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT 0) * ((1 : Matrix κ κ ℝ)ᵀ ⊗ₖ (V_KKT 0)ᵀ) +
       ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT 1) * ((1 : Matrix κ κ ℝ)ᵀ ⊗ₖ (V_KKT 1)ᵀ) +
       ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT 2) * ((1 : Matrix κ κ ℝ)ᵀ ⊗ₖ (V_KKT 2)ᵀ) +
       ((1 : Matrix κ κ ℝ) ⊗ₖ V_KKT 3) * ((1 : Matrix κ κ ℝ)ᵀ ⊗ₖ (V_KKT 3)ᵀ) = 1
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]
  have h1 : (1 : Matrix κ κ ℝ) * (1 : Matrix κ κ ℝ)ᵀ = 1 := by
    rw [transpose_one, mul_one]
  rw [h1, ← kronecker_add, ← kronecker_add, ← kronecker_add]
  have h_comp := kkt_kraus_isometric_and_completeness.2
  rw [h_comp, one_kronecker_one]

/-- Amplified partial trace map `(id ⊗ partialTraceKKT)`. -/
noncomputable def partialTraceKKT_amplified (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Matrix (κ × Fin 8) (κ × Fin 8) ℝ →ₗ[ℝ] Matrix (κ × Fin 2) (κ × Fin 2) ℝ where
  toFun M := ∑ a : Fin 4, (W_KKT κ a)ᵀ * M * (W_KKT κ a)
  map_add' M N := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

theorem partialTraceKKT_amplified_preserves_posSemidef (κ : Type*) [Fintype κ] [DecidableEq κ]
    {M : Matrix (κ × Fin 8) (κ × Fin 8) ℝ} (hM : M.PosSemidef) :
    (partialTraceKKT_amplified κ M).PosSemidef := by
  dsimp [partialTraceKKT_amplified]
  have h_term (a : Fin 4) : ((W_KKT κ a)ᵀ * M * (W_KKT κ a)).PosSemidef := by
    have hconj : (W_KKT κ a)ᵀ = (W_KKT κ a)ᴴ := by
      rw [conjTranspose_eq_transpose_of_trivial]
    rw [hconj]
    exact hM.conjTranspose_mul_mul_same (W_KKT κ a)
  have h0 := h_term 0; have h1 := h_term 1; have h2 := h_term 2; have h3 := h_term 3
  rw [Fin.sum_univ_four]
  exact (((h0.add h1).add h2).add h3)

theorem partialTraceKKT_amplified_preserves_trace (κ : Type*) [Fintype κ] [DecidableEq κ]
    (M : Matrix (κ × Fin 8) (κ × Fin 8) ℝ) :
    (partialTraceKKT_amplified κ M).trace = M.trace := by
  dsimp [partialTraceKKT_amplified]
  rw [trace_sum]
  have h_tr (a : Fin 4) :
      ((W_KKT κ a)ᵀ * M * (W_KKT κ a)).trace = (M * ((W_KKT κ a) * (W_KKT κ a)ᵀ)).trace := by
    calc ((W_KKT κ a)ᵀ * M * (W_KKT κ a)).trace
      _ = ((W_KKT κ a) * ((W_KKT κ a)ᵀ * M)).trace := by
        exact trace_mul_comm ((W_KKT κ a)ᵀ * M) (W_KKT κ a)
      _ = ((W_KKT κ a * (W_KKT κ a)ᵀ) * M).trace := by
        rw [← Matrix.mul_assoc]
      _ = (M * ((W_KKT κ a) * (W_KKT κ a)ᵀ)).trace := by
        exact trace_mul_comm (W_KKT κ a * (W_KKT κ a)ᵀ) M
  rw [Fin.sum_univ_four]
  simp_rw [h_tr]
  rw [← trace_add, ← trace_add, ← trace_add,
      ← Matrix.mul_add, ← Matrix.mul_add, ← Matrix.mul_add]
  have h_comp : (W_KKT κ 0) * (W_KKT κ 0)ᵀ +
      (W_KKT κ 1) * (W_KKT κ 1)ᵀ +
      (W_KKT κ 2) * (W_KKT κ 2)ᵀ +
      (W_KKT κ 3) * (W_KKT κ 3)ᵀ = 1 := by
    have hc := W_KKT_completeness κ
    rw [Fin.sum_univ_four] at hc
    exact hc
  rw [h_comp, Matrix.mul_one]

/-! ### Part II: 4-Channel Kraus Representation & CPTP Semigroup -/

noncomputable def thermalKrausR (γ θ t : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => mat2 (Real.sqrt (boltzmannPlus θ)) 0 0
              (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)))
  | 1 => mat2 0 (Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t))) 0 0
  | 2 => mat2 (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t))) 0 0
              (Real.sqrt (boltzmannMinus θ))
  | 3 => mat2 0 0 (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t))) 0

theorem thermalKrausR_unital {γ θ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    ∑ k : Fin 4, (thermalKrausR γ θ t k)ᵀ * thermalKrausR γ θ t k = 1 := by
  rcases boltzmann_nonneg θ with ⟨hp_pos, hm_pos⟩
  have he_nonneg : 0 ≤ Real.exp (-γ * t) := le_of_lt (Real.exp_pos _)
  have h_gt : 0 ≤ γ * t := mul_nonneg hγ ht
  have h_neg : -γ * t ≤ 0 := by
    linarith [h_gt]
  have he_le1 : Real.exp (-γ * t) ≤ 1 := Real.exp_le_one_iff.mpr h_neg
  have h1e_nonneg : 0 ≤ 1 - Real.exp (-γ * t) := sub_nonneg.mpr he_le1
  have h_bp_mul : Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ) = boltzmannPlus θ :=
    Real.mul_self_sqrt (le_of_lt hp_pos)
  have h_bm_mul : Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ) = boltzmannMinus θ :=
    Real.mul_self_sqrt (le_of_lt hm_pos)
  have h_ep_mul : Real.sqrt (Real.exp (-γ * t)) * Real.sqrt (Real.exp (-γ * t)) = Real.exp (-γ * t) :=
    Real.mul_self_sqrt he_nonneg
  have h_1e_mul : Real.sqrt (1 - Real.exp (-γ * t)) * Real.sqrt (1 - Real.exp (-γ * t)) =
      1 - Real.exp (-γ * t) :=
    Real.mul_self_sqrt h1e_nonneg
  have h_bsum : boltzmannPlus θ + boltzmannMinus θ = 1 := (boltzmann_sum_and_diff θ).1
  rw [Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [thermalKrausR, mat2, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    simp_rw [Fin.sum_univ_two]
    dsimp
    have h0 : Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ) = boltzmannPlus θ := h_bp_mul
    have h2 : (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t))) *
        (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t))) =
        boltzmannMinus θ * Real.exp (-γ * t) := by
      calc (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t))) *
          (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)))
        _ = (Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ)) *
            (Real.sqrt (Real.exp (-γ * t)) * Real.sqrt (Real.exp (-γ * t))) := by ring
        _ = boltzmannMinus θ * Real.exp (-γ * t) := by rw [h_bm_mul, h_ep_mul]
    have h3 : (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t))) *
        (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t))) =
        boltzmannMinus θ * (1 - Real.exp (-γ * t)) := by
      calc (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t))) *
          (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t)))
        _ = (Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ)) *
            (Real.sqrt (1 - Real.exp (-γ * t)) * Real.sqrt (1 - Real.exp (-γ * t))) := by ring
        _ = boltzmannMinus θ * (1 - Real.exp (-γ * t)) := by rw [h_bm_mul, h_1e_mul]
    rw [h0, h2, h3]
    linear_combination h_bsum
  · dsimp [thermalKrausR, mat2, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    simp_rw [Fin.sum_univ_two]
    dsimp
    ring
  · dsimp [thermalKrausR, mat2, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    simp_rw [Fin.sum_univ_two]
    dsimp
    ring
  · dsimp [thermalKrausR, mat2, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    simp_rw [Fin.sum_univ_two]
    dsimp
    have h0 : (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t))) *
        (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t))) =
        boltzmannPlus θ * Real.exp (-γ * t) := by
      calc (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t))) *
          (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)))
        _ = (Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ)) *
            (Real.sqrt (Real.exp (-γ * t)) * Real.sqrt (Real.exp (-γ * t))) := by ring
        _ = boltzmannPlus θ * Real.exp (-γ * t) := by rw [h_bp_mul, h_ep_mul]
    have h1 : (Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t))) *
        (Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t))) =
        boltzmannPlus θ * (1 - Real.exp (-γ * t)) := by
      calc (Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t))) *
          (Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)))
        _ = (Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ)) *
            (Real.sqrt (1 - Real.exp (-γ * t)) * Real.sqrt (1 - Real.exp (-γ * t))) := by ring
        _ = boltzmannPlus θ * (1 - Real.exp (-γ * t)) := by rw [h_bp_mul, h_1e_mul]
    have h2 : Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ) = boltzmannMinus θ := h_bm_mul
    rw [h0, h1, h2]
    linear_combination h_bsum

lemma sqrt_exp_neg_gamma_t (γ t : ℝ) :
    Real.sqrt (Real.exp (-γ * t)) = Real.exp (-(1 / 2 : ℝ) * γ * t) := by
  have he : Real.exp (-(1 / 2 : ℝ) * γ * t) = Real.exp ((-γ * t) / 2) := by
    congr 1; ring
  rw [he, Real.exp_half]

theorem gkslPropagator_eq_kraus_sum (γ θ t : ℝ) (hγ : 0 < γ) (ht : 0 ≤ t)
    (ρ : Matrix (Fin 2) (Fin 2) ℝ) :
    gkslPropagator (ratePlus γ θ) (rateMinus γ θ) t ρ =
      ∑ k : Fin 4, thermalKrausR γ θ t k * ρ * (thermalKrausR γ θ t k)ᵀ := by
  have h_sum_rates : rateMinus γ θ + ratePlus γ θ = γ := by
    dsimp [ratePlus, rateMinus]
    calc γ * boltzmannMinus θ + γ * boltzmannPlus θ
      _ = γ * (boltzmannPlus θ + boltzmannMinus θ) := by ring
      _ = γ * 1 := by rw [(boltzmann_sum_and_diff θ).1]
      _ = γ := mul_one γ
  have h_pos : 0 < rateMinus γ θ + ratePlus γ θ := by
    rw [h_sum_rates]
    exact hγ
  have hp0 : ratePlus γ θ / γ = boltzmannPlus θ := by
    dsimp [ratePlus]
    rw [mul_div_cancel_left₀ _ hγ.ne']
  have hp1 : rateMinus γ θ / γ = boltzmannMinus θ := by
    dsimp [rateMinus]
    rw [mul_div_cancel_left₀ _ hγ.ne']
  rcases boltzmann_nonneg θ with ⟨hp_pos, hm_pos⟩
  have he_nonneg : 0 ≤ Real.exp (-γ * t) := le_of_lt (Real.exp_pos _)
  have h_gt : 0 ≤ γ * t := mul_nonneg (le_of_lt hγ) ht
  have h_neg : -γ * t ≤ 0 := by
    linarith [h_gt]
  have he_le1 : Real.exp (-γ * t) ≤ 1 := Real.exp_le_one_iff.mpr h_neg
  have h1e_nonneg : 0 ≤ 1 - Real.exp (-γ * t) := sub_nonneg.mpr he_le1
  have h_bp_mul : Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ) = boltzmannPlus θ :=
    Real.mul_self_sqrt (le_of_lt hp_pos)
  have h_bm_mul : Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ) = boltzmannMinus θ :=
    Real.mul_self_sqrt (le_of_lt hm_pos)
  have h_ep_mul : Real.sqrt (Real.exp (-γ * t)) * Real.sqrt (Real.exp (-γ * t)) = Real.exp (-γ * t) :=
    Real.mul_self_sqrt he_nonneg
  have h_1e_mul : Real.sqrt (1 - Real.exp (-γ * t)) * Real.sqrt (1 - Real.exp (-γ * t)) =
      1 - Real.exp (-γ * t) :=
    Real.mul_self_sqrt h1e_nonneg
  have h_sqrt_exp := sqrt_exp_neg_gamma_t γ t
  have h_bsum : boltzmannPlus θ + boltzmannMinus θ = 1 := (boltzmann_sum_and_diff θ).1
  rw [Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j
  · change gkslPropagator (ratePlus γ θ) (rateMinus γ θ) t ρ 0 0 =
           (thermalKrausR γ θ t 0 * ρ * (thermalKrausR γ θ t 0)ᵀ +
            thermalKrausR γ θ t 1 * ρ * (thermalKrausR γ θ t 1)ᵀ +
            thermalKrausR γ θ t 2 * ρ * (thermalKrausR γ θ t 2)ᵀ +
            thermalKrausR γ θ t 3 * ρ * (thermalKrausR γ θ t 3)ᵀ) 0 0
    rw [gksl_propagator_00 _ _ _ _ h_pos]
    rw [h_sum_rates, hp0]
    dsimp [thermalKrausR, mat2, Matrix.mul_apply, Matrix.transpose_apply, Matrix.trace]
    simp_rw [Fin.sum_univ_two]
    dsimp
    have h_rhs : (Real.sqrt (boltzmannPlus θ) * ρ 0 0 + 0 * ρ 1 0) * Real.sqrt (boltzmannPlus θ) +
        (Real.sqrt (boltzmannPlus θ) * ρ 0 1 + 0 * ρ 1 1) * 0 +
        ((0 * ρ 0 0 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 1 0) * 0 +
          (0 * ρ 0 1 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 1 1) *
            (Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)))) +
        ((Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 0 0 + 0 * ρ 1 0) *
            (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t))) +
          (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 0 1 + 0 * ρ 1 1) * 0) +
        ((0 * ρ 0 0 + 0 * ρ 1 0) * 0 + (0 * ρ 0 1 + 0 * ρ 1 1) * 0) =
        boltzmannPlus θ * ρ 0 0 +
        boltzmannPlus θ * (1 - Real.exp (-γ * t)) * ρ 1 1 +
        boltzmannMinus θ * Real.exp (-γ * t) * ρ 0 0 := by
      calc (Real.sqrt (boltzmannPlus θ) * ρ 0 0 + 0 * ρ 1 0) * Real.sqrt (boltzmannPlus θ) +
           (Real.sqrt (boltzmannPlus θ) * ρ 0 1 + 0 * ρ 1 1) * 0 +
           ((0 * ρ 0 0 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 1 0) * 0 +
             (0 * ρ 0 1 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 1 1) *
               (Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)))) +
           ((Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 0 0 + 0 * ρ 1 0) *
               (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t))) +
             (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 0 1 + 0 * ρ 1 1) * 0) +
           ((0 * ρ 0 0 + 0 * ρ 1 0) * 0 + (0 * ρ 0 1 + 0 * ρ 1 1) * 0)
        _ = (Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ)) * ρ 0 0 +
            (Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ)) *
              (Real.sqrt (1 - Real.exp (-γ * t)) * Real.sqrt (1 - Real.exp (-γ * t))) * ρ 1 1 +
            (Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ)) *
              (Real.sqrt (Real.exp (-γ * t)) * Real.sqrt (Real.exp (-γ * t))) * ρ 0 0 := by ring
        _ = boltzmannPlus θ * ρ 0 0 +
            boltzmannPlus θ * (1 - Real.exp (-γ * t)) * ρ 1 1 +
            boltzmannMinus θ * Real.exp (-γ * t) * ρ 0 0 := by rw [h_bp_mul, h_bm_mul, h_ep_mul, h_1e_mul]
    rw [h_rhs]
    linear_combination -(ρ 0 0 * Real.exp (-γ * t)) * h_bsum
  · change gkslPropagator (ratePlus γ θ) (rateMinus γ θ) t ρ 0 1 =
           (thermalKrausR γ θ t 0 * ρ * (thermalKrausR γ θ t 0)ᵀ +
            thermalKrausR γ θ t 1 * ρ * (thermalKrausR γ θ t 1)ᵀ +
            thermalKrausR γ θ t 2 * ρ * (thermalKrausR γ θ t 2)ᵀ +
            thermalKrausR γ θ t 3 * ρ * (thermalKrausR γ θ t 3)ᵀ) 0 1
    rw [gksl_propagator_01]
    rw [h_sum_rates]
    dsimp [thermalKrausR, mat2, Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw [Fin.sum_univ_two]
    dsimp
    have h_rhs : (Real.sqrt (boltzmannPlus θ) * ρ 0 1) *
          (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t))) +
        (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 0 1) *
          Real.sqrt (boltzmannMinus θ) =
        boltzmannPlus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 0 1 +
        boltzmannMinus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 0 1 := by
      calc (Real.sqrt (boltzmannPlus θ) * ρ 0 1) *
             (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t))) +
           (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 0 1) *
             Real.sqrt (boltzmannMinus θ)
        _ = (Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ)) *
              Real.sqrt (Real.exp (-γ * t)) * ρ 0 1 +
            (Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ)) *
              Real.sqrt (Real.exp (-γ * t)) * ρ 0 1 := by ring
        _ = boltzmannPlus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 0 1 +
            boltzmannMinus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 0 1 := by
          rw [h_bp_mul, h_bm_mul, h_sqrt_exp]
    have h_eval : (Real.sqrt (boltzmannPlus θ) * ρ 0 0 + 0 * ρ 1 0) * 0 +
        (Real.sqrt (boltzmannPlus θ) * ρ 0 1 + 0 * ρ 1 1) *
          (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t))) +
        ((0 * ρ 0 0 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 1 0) * 0 +
          (0 * ρ 0 1 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 1 1) * 0) +
        ((Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 0 0 + 0 * ρ 1 0) * 0 +
          (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 0 1 + 0 * ρ 1 1) *
            Real.sqrt (boltzmannMinus θ)) +
        ((0 * ρ 0 0 + 0 * ρ 1 0) * (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t))) +
          (0 * ρ 0 1 + 0 * ρ 1 1) * 0) =
        (Real.sqrt (boltzmannPlus θ) * ρ 0 1) *
          (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t))) +
        (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 0 1) *
          Real.sqrt (boltzmannMinus θ) := by ring
    have h_lhs : ρ 0 1 * Real.exp (-(1 / 2 : ℝ) * γ * t) =
        boltzmannPlus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 0 1 +
        boltzmannMinus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 0 1 := by
      calc ρ 0 1 * Real.exp (-(1 / 2 : ℝ) * γ * t)
        _ = (boltzmannPlus θ + boltzmannMinus θ) * (Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 0 1) := by
            rw [h_bsum, one_mul]
            ring
        _ = boltzmannPlus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 0 1 +
            boltzmannMinus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 0 1 := by
            ring
    rw [h_eval, h_rhs, h_lhs]
  · change gkslPropagator (ratePlus γ θ) (rateMinus γ θ) t ρ 1 0 =
           (thermalKrausR γ θ t 0 * ρ * (thermalKrausR γ θ t 0)ᵀ +
            thermalKrausR γ θ t 1 * ρ * (thermalKrausR γ θ t 1)ᵀ +
            thermalKrausR γ θ t 2 * ρ * (thermalKrausR γ θ t 2)ᵀ +
            thermalKrausR γ θ t 3 * ρ * (thermalKrausR γ θ t 3)ᵀ) 1 0
    rw [gksl_propagator_10]
    rw [h_sum_rates]
    dsimp [thermalKrausR, mat2, Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw [Fin.sum_univ_two]
    dsimp
    have h_rhs : (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 1 0) *
          Real.sqrt (boltzmannPlus θ) +
        (Real.sqrt (boltzmannMinus θ) * ρ 1 0) *
          (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t))) =
        boltzmannPlus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 1 0 +
        boltzmannMinus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 1 0 := by
      calc (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 1 0) *
             Real.sqrt (boltzmannPlus θ) +
           (Real.sqrt (boltzmannMinus θ) * ρ 1 0) *
             (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t)))
        _ = (Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ)) *
              Real.sqrt (Real.exp (-γ * t)) * ρ 1 0 +
            (Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ)) *
              Real.sqrt (Real.exp (-γ * t)) * ρ 1 0 := by ring
        _ = boltzmannPlus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 1 0 +
            boltzmannMinus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 1 0 := by
          rw [h_bp_mul, h_bm_mul, h_sqrt_exp]
    have h_eval : (0 * ρ 0 0 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 1 0) *
          Real.sqrt (boltzmannPlus θ) +
        (0 * ρ 0 1 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 1 1) * 0 +
        ((0 * ρ 0 0 + 0 * ρ 1 0) * 0 + (0 * ρ 0 1 + 0 * ρ 1 1) *
          (Real.sqrt (boltzmannPlus θ) * Real.sqrt (1 - Real.exp (-γ * t)))) +
        ((0 * ρ 0 0 + Real.sqrt (boltzmannMinus θ) * ρ 1 0) *
            (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t))) +
          (0 * ρ 0 1 + Real.sqrt (boltzmannMinus θ) * ρ 1 1) * 0) +
        ((Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 0 0 + 0 * ρ 1 0) * 0 +
          (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 0 1 + 0 * ρ 1 1) * 0) =
        (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 1 0) *
          Real.sqrt (boltzmannPlus θ) +
        (Real.sqrt (boltzmannMinus θ) * ρ 1 0) *
          (Real.sqrt (boltzmannMinus θ) * Real.sqrt (Real.exp (-γ * t))) := by ring
    have h_lhs : ρ 1 0 * Real.exp (-(1 / 2 : ℝ) * γ * t) =
        boltzmannPlus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 1 0 +
        boltzmannMinus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 1 0 := by
      calc ρ 1 0 * Real.exp (-(1 / 2 : ℝ) * γ * t)
        _ = (boltzmannPlus θ + boltzmannMinus θ) * (Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 1 0) := by
            rw [h_bsum, one_mul]
            ring
        _ = boltzmannPlus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 1 0 +
            boltzmannMinus θ * Real.exp (-(1 / 2 : ℝ) * γ * t) * ρ 1 0 := by
            ring
    rw [h_eval, h_rhs, h_lhs]
  · change gkslPropagator (ratePlus γ θ) (rateMinus γ θ) t ρ 1 1 =
           (thermalKrausR γ θ t 0 * ρ * (thermalKrausR γ θ t 0)ᵀ +
            thermalKrausR γ θ t 1 * ρ * (thermalKrausR γ θ t 1)ᵀ +
            thermalKrausR γ θ t 2 * ρ * (thermalKrausR γ θ t 2)ᵀ +
            thermalKrausR γ θ t 3 * ρ * (thermalKrausR γ θ t 3)ᵀ) 1 1
    rw [gksl_propagator_11 _ _ _ _ h_pos]
    rw [h_sum_rates, hp1]
    dsimp [thermalKrausR, mat2, Matrix.mul_apply, Matrix.transpose_apply, Matrix.trace]
    simp_rw [Fin.sum_univ_two]
    dsimp
    have h_rhs : (0 * ρ 0 0 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 1 0) * 0 +
        (0 * ρ 0 1 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 1 1) *
          (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t))) +
        ((0 * ρ 0 0 + 0 * ρ 1 0) * 0 + (0 * ρ 0 1 + 0 * ρ 1 1) * 0) +
        ((0 * ρ 0 0 + Real.sqrt (boltzmannMinus θ) * ρ 1 0) * 0 +
          (0 * ρ 0 1 + Real.sqrt (boltzmannMinus θ) * ρ 1 1) * Real.sqrt (boltzmannMinus θ)) +
        ((Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 0 0 + 0 * ρ 1 0) *
            (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t))) +
          (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 0 1 + 0 * ρ 1 1) * 0) =
        boltzmannPlus θ * Real.exp (-γ * t) * ρ 1 1 +
        boltzmannMinus θ * ρ 1 1 +
        boltzmannMinus θ * (1 - Real.exp (-γ * t)) * ρ 0 0 := by
      calc (0 * ρ 0 0 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 1 0) * 0 +
           (0 * ρ 0 1 + Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t)) * ρ 1 1) *
             (Real.sqrt (boltzmannPlus θ) * Real.sqrt (Real.exp (-γ * t))) +
           ((0 * ρ 0 0 + 0 * ρ 1 0) * 0 + (0 * ρ 0 1 + 0 * ρ 1 1) * 0) +
           ((0 * ρ 0 0 + Real.sqrt (boltzmannMinus θ) * ρ 1 0) * 0 +
             (0 * ρ 0 1 + Real.sqrt (boltzmannMinus θ) * ρ 1 1) * Real.sqrt (boltzmannMinus θ)) +
           ((Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 0 0 + 0 * ρ 1 0) *
               (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t))) +
             (Real.sqrt (boltzmannMinus θ) * Real.sqrt (1 - Real.exp (-γ * t)) * ρ 0 1 + 0 * ρ 1 1) * 0)
        _ = (Real.sqrt (boltzmannPlus θ) * Real.sqrt (boltzmannPlus θ)) *
              (Real.sqrt (Real.exp (-γ * t)) * Real.sqrt (Real.exp (-γ * t))) * ρ 1 1 +
            (Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ)) * ρ 1 1 +
            (Real.sqrt (boltzmannMinus θ) * Real.sqrt (boltzmannMinus θ)) *
              (Real.sqrt (1 - Real.exp (-γ * t)) * Real.sqrt (1 - Real.exp (-γ * t))) * ρ 0 0 := by ring
        _ = boltzmannPlus θ * Real.exp (-γ * t) * ρ 1 1 +
            boltzmannMinus θ * ρ 1 1 +
            boltzmannMinus θ * (1 - Real.exp (-γ * t)) * ρ 0 0 := by
          rw [h_bp_mul, h_bm_mul, h_ep_mul, h_1e_mul]
    rw [h_rhs]
    linear_combination -(ρ 1 1 * Real.exp (-γ * t)) * h_bsum

/-! ### Part III: Generator-Flow Identity Bridging SchrodingerGKSLFlowBridge -/

theorem gkslFlow_eq_thermalSemigroupC (γ ω θ t : ℝ) (hγ : 0 ≤ γ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    InfoGeometry.Modular.SchrodingerGKSLFlowBridge.gkslFlow (thermalHamiltonian ω)
      ![(Real.sqrt (ratePlus γ θ) : ℂ) • wittFPlus,
        (Real.sqrt (rateMinus γ θ) : ℂ) • wittFMinus] t ρ =
      thermalSemigroupC γ ω θ t ρ := by
  let H := thermalHamiltonian ω
  let V : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
    ![(Real.sqrt (ratePlus γ θ) : ℂ) • wittFPlus,
      (Real.sqrt (rateMinus γ θ) : ℂ) • wittFMinus]
  have h_ode : ∀ s, HasDerivAt (fun u => thermalSemigroupC γ ω θ u ρ)
      (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V
        (thermalSemigroupC γ ω θ s ρ)) s := by
    intro s
    have hw := (thermalLindbladian_weld_to_schrodinger_and_gksl γ ω θ hγ
      (thermalSemigroupC γ ω θ s ρ)).1
    rw [← hw]
    refine hasDerivAt_pi.2 (fun i => hasDerivAt_pi.2 (fun j => ?_))
    rw [← thermalLindbladianOp_eq_thermalLindbladianC]
    exact forward_kolmogorov_ode γ ω θ ρ i j s
  have h_init : thermalSemigroupC γ ω θ 0 ρ = ρ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      { dsimp [thermalSemigroupC, mat2]
        simp only [mul_zero, Real.exp_zero, Complex.ofReal_one,
                   Complex.exp_zero, one_mul, mul_one]
        try ring }
  have h_uniq := InfoGeometry.Modular.SchrodingerGKSLFlowBridge.gkslFlow_unique_of_ode
    H V ρ (fun s => thermalSemigroupC γ ω θ s ρ) h_ode h_init
  exact (congr_fun h_uniq t).symm

/-! ### Part IV: OpenGauss T16 Non-commutativity Witness -/

theorem kms_complete_positivity_noncommuting_witness :
    V_KKT 0 * (V_KKT 1)ᵀ ≠ (V_KKT 1) * (V_KKT 0)ᵀ := by
  intro h
  have h02 := congrArg (fun M => M 0 2) h
  dsimp [V_KKT, toMatR, V_KKT_Z, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at h02
  norm_num at h02

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich.KMSCompletePositivityAndKrausSemigroup
