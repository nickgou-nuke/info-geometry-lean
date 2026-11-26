/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.UHFColimitCStarCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Powers Product State, Inductive Modular Flow, and Point Spectrum `{λ^k : k ∈ ℤ}` on `UHFAlg` (`F3b`)

This module constructs the one-parameter Powers product state family `ω_λ` (`λ > 0`)
on the `2^∞` UHF inductive colimit algebra `UHFAlg` (reusing
`UHFColimitCStarCompletion`), keeping the algebraic inductive limit, point spectrum,
outer-flow obstruction, and infinite C*-completion strictly distinct:

1. **Powers Weights & Stage-Compatible State**:
   `powersWeight lam n : Fin (2^n) → ℝ` with recursive tensor weights
   `(1 / (1 + λ), λ / (1 + λ))` along `finSumTwoPow n`.
   Proves `powersStageState_one : powersStageState lam n 1 = 1` and exact step
   compatibility `powersStageState lam (n + 1) (uhfStep n A) = powersStageState lam n A`,
   descending cleanly to a normalized linear functional `powersAlgState : UHFAlg → ℂ`.
2. **Inductive Modular Flow & `UHFAlg` Automorphism Group**:
   `powersStageFlow lam n t A i j := ((w_i / w_j : ℝ) : ℂ) ^ (I * t) * A i j`
   is proved to be a `*-automorphism` commuting with `uhfStep n` (`powersStageFlow_uhfStep`),
   descending to `powersAlgFlowFun : UHFAlg → UHFAlg` and leaving `powersAlgState` invariant.
3. **Exact Point Spectrum `{λ^k : k ∈ ℤ}` (Distinct from Full Closed Spectrum `{0} ∪ {λ^k}`)**:
   Constructs explicit nonzero raising/lowering matrix units `E_k, E_kᴴ ∈ UHFStage k`
   satisfying `powersStageModularOp lam k E_k = (lam ^ k : ℂ) • E_k` and
   `powersStageModularOp lam k E_kᴴ = ((lam ^ k)⁻¹ : ℂ) • E_kᴴ` for every `k : ℕ`.
   (Note: `{λ^k : k ∈ ℤ}` is the **point spectrum**; for `0 < λ < 1`, its topological
   closure adds `0`, and full von Neumann Type `III_λ` factor classification requires
   the weak-operator GNS commutant closure beyond `UHFAlg`.)
4. **Non-Traciality & Finite-Stage Outer-Flow Obstruction**:
   For `λ ≠ 1`, proves non-traciality at stage 1 and proves that no finite-stage
   unitary `U ∈ UHFStage m` (`U * Uᴴ = 1`) can inner-implement `powersAlgFlowFun hpos t`
   on `UHFAlg` whenever `(lam : ℂ) ^ (Complex.I * (t : ℂ)) ≠ 1`.
5. **OpenGauss T16 Witness**:
   Re-exports the noncommuting `Matrix (Fin 2) (Fin 2) ℂ` witness.
-/

noncomputable section

namespace InfoGeometry.Algebra.UHFPowersModularState

open Matrix Complex Finset
open scoped Matrix.Norms.L2Operator

open InfoGeometry.Algebra.UHFColimitCStarCompletion

/-! =========================================================================
    1. OpenGauss T16 Witness & Scalar Helpers
    ========================================================================= -/

/-- Closed T16 noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem mat2_complex_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  let E01 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 1], ![0, 0]]
  let E10 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 0], ![1, 0]]
  refine ⟨E01, E10, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have hL : (E01 * E10) 0 0 = 1 := by
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : (E10 * E01) 0 0 = 0 := by
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hL, hR] at h00
  exact one_ne_zero h00

private lemma scalar_cpow_mul_ratio {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (t : ℂ) :
    ((a / b : ℝ) : ℂ) ^ t * ((b / c : ℝ) : ℂ) ^ t = ((a / c : ℝ) : ℂ) ^ t := by
  have h1 : 0 ≤ a / b := div_nonneg ha.le hb.le
  have h2 : 0 ≤ b / c := div_nonneg hb.le hc.le
  have hmul : (a / b) * (b / c) = a / c := by field_simp [hb.ne']
  calc
    ((a / b : ℝ) : ℂ) ^ t * ((b / c : ℝ) : ℂ) ^ t
        = (((a / b : ℝ) : ℂ) * ((b / c : ℝ) : ℂ)) ^ t :=
          (Complex.mul_cpow_ofReal_nonneg h1 h2 t).symm
    _ = (((a / b) * (b / c) : ℝ) : ℂ) ^ t := by rw [← Complex.ofReal_mul]
    _ = ((a / c : ℝ) : ℂ) ^ t := by rw [hmul]

private lemma scalar_cpow_conj_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    star (((a / b : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))) =
      ((b / a : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) := by
  have hpos : 0 < a / b := div_pos ha hb
  have harg : ((a / b : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hpos.le]
    exact Real.pi_ne_zero.symm
  have hconj_exp : starRingEnd ℂ (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) := by
    simp [Complex.conj_I, Complex.conj_ofReal]
  have hconj_base : starRingEnd ℂ ((a / b : ℝ) : ℂ) = ((a / b : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  calc
    star (((a / b : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)))
        = starRingEnd ℂ (((a / b : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))) := rfl
    _ = starRingEnd ℂ ((starRingEnd ℂ ((a / b : ℝ) : ℂ)) ^ (Complex.I * (t : ℂ))) := by
          rw [hconj_base]
    _ = ((a / b : ℝ) : ℂ) ^ (starRingEnd ℂ (Complex.I * (t : ℂ))) :=
          (Complex.cpow_conj _ _ harg).symm
    _ = (((a / b : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)))⁻¹ := by
          rw [hconj_exp, Complex.cpow_neg]
    _ = (((a / b : ℝ) : ℂ)⁻¹) ^ (Complex.I * (t : ℂ)) :=
          (Complex.inv_cpow _ _ harg).symm
    _ = ((b / a : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) := by
          rw [← Complex.ofReal_inv, inv_div]

private lemma scalar_cpow_inv_ne_one {lam : ℝ} (hpos : 0 < lam) (t : ℝ)
    (ht : (lam : ℂ) ^ (Complex.I * (t : ℂ)) ≠ 1) :
    ((lam⁻¹ : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) ≠ 1 := by
  intro heq
  apply ht
  have harg : (lam : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hpos.le]
    exact Real.pi_ne_zero.symm
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg] at heq
  exact inv_eq_one.mp heq

/-! =========================================================================
    2. Powers Weights & Inductive State on UHFAlg
    ========================================================================= -/

/-- Recursive Powers diagonal weights on `Fin (2^n)`. -/
def powersWeight (lam : ℝ) : (n : ℕ) → Fin (2 ^ n) → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun k =>
    match (finSumTwoPow n).symm k with
    | Sum.inl i => (1 / (1 + lam)) * powersWeight lam n i
    | Sum.inr i => (lam / (1 + lam)) * powersWeight lam n i

theorem powersWeight_inl (lam : ℝ) (n : ℕ) (i : Fin (2 ^ n)) :
    powersWeight lam (n + 1) (finSumTwoPow n (Sum.inl i)) =
      (1 / (1 + lam)) * powersWeight lam n i := by
  simp [powersWeight]

theorem powersWeight_inr (lam : ℝ) (n : ℕ) (i : Fin (2 ^ n)) :
    powersWeight lam (n + 1) (finSumTwoPow n (Sum.inr i)) =
      (lam / (1 + lam)) * powersWeight lam n i := by
  simp [powersWeight]

theorem powersWeight_pos {lam : ℝ} (hpos : 0 < lam) :
    ∀ (n : ℕ) (i : Fin (2 ^ n)), 0 < powersWeight lam n i
  | 0, _ => by simp [powersWeight]
  | n + 1, k => by
    have hdenom : 0 < 1 + lam := by linarith
    unfold powersWeight
    cases hk : (finSumTwoPow n).symm k with
    | inl i =>
      exact mul_pos (div_pos one_pos hdenom) (powersWeight_pos hpos n i)
    | inr i =>
      exact mul_pos (div_pos hpos hdenom) (powersWeight_pos hpos n i)

theorem sum_powersWeight {lam : ℝ} (hpos : 0 < lam) :
    ∀ n : ℕ, (∑ i : Fin (2 ^ n), powersWeight lam n i) = 1
  | 0 => by simp [powersWeight]
  | n + 1 => by
    have hdenom : (1 + lam) ≠ 0 := by linarith
    calc
      ∑ k : Fin (2 ^ (n + 1)), powersWeight lam (n + 1) k
          = ∑ x : Fin (2 ^ n) ⊕ Fin (2 ^ n),
              powersWeight lam (n + 1) (finSumTwoPow n x) := by
            rw [← Fintype.sum_equiv (finSumTwoPow n) _ _ fun _ => rfl]
      _ = (∑ i : Fin (2 ^ n), (1 / (1 + lam)) * powersWeight lam n i) +
            (∑ i : Fin (2 ^ n), (lam / (1 + lam)) * powersWeight lam n i) := by
            rw [Fintype.sum_sum_type]
            simp [powersWeight_inl, powersWeight_inr]
      _ = (1 / (1 + lam) + lam / (1 + lam)) * (∑ i : Fin (2 ^ n), powersWeight lam n i) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← add_mul]
      _ = 1 := by
            rw [sum_powersWeight hpos n, mul_one]
            field_simp [hdenom]

/-- Stage-`n` Powers product state `ω_λ^{(n)}(A) = ∑_i w_i^{(n)} A_{ii}`. -/
def powersStageState (lam : ℝ) (n : ℕ) (A : UHFStage n) : ℂ :=
  ∑ i : Fin (2 ^ n), (powersWeight lam n i : ℂ) * A i i

theorem powersStageState_one {lam : ℝ} (hpos : 0 < lam) (n : ℕ) :
    powersStageState lam n 1 = 1 := by
  unfold powersStageState
  simp only [Matrix.one_apply_eq, mul_one, ← Complex.ofReal_sum, sum_powersWeight hpos n,
    Complex.ofReal_one]

/-- Stage compatibility: `powersStageState lam (n + 1) (uhfStep n A) = powersStageState lam n A`. -/
theorem powersStageState_uhfStep {lam : ℝ} (hpos : 0 < lam) (n : ℕ) (A : UHFStage n) :
    powersStageState lam (n + 1) (uhfStep n A) = powersStageState lam n A := by
  have hdenom : (1 + lam : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith : (1 + lam : ℝ) ≠ 0)
  unfold powersStageState uhfStep
  rw [← Fintype.sum_equiv (finSumTwoPow n) _ _ fun _ => rfl]
  rw [Fintype.sum_sum_type]
  have hL : ∀ i : Fin (2 ^ n),
      ((powersWeight lam (n + 1) (finSumTwoPow n (Sum.inl i)) : ℂ) *
        (reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks A 0 0 A))
          (finSumTwoPow n (Sum.inl i)) (finSumTwoPow n (Sum.inl i))) =
        ((1 / (1 + lam) : ℂ) * (powersWeight lam n i : ℂ) * A i i) := by
    intro i
    rw [powersWeight_inl]
    simp only [coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
      Equiv.symm_apply_apply, fromBlocks_apply₁₁, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_add, mul_assoc]
  have hR : ∀ i : Fin (2 ^ n),
      ((powersWeight lam (n + 1) (finSumTwoPow n (Sum.inr i)) : ℂ) *
        (reindexAlgEquiv ℂ ℂ (finSumTwoPow n) (fromBlocks A 0 0 A))
          (finSumTwoPow n (Sum.inr i)) (finSumTwoPow n (Sum.inr i))) =
        (((lam / (1 + lam) : ℂ) * (powersWeight lam n i : ℂ) * A i i)) := by
    intro i
    rw [powersWeight_inr]
    simp only [coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
      Equiv.symm_apply_apply, fromBlocks_apply₂₂, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_add, mul_assoc]
  simp_rw [hL, hR, mul_assoc, ← Finset.mul_sum, ← add_mul]
  have hsum : (1 / (1 + lam : ℂ) + (lam : ℂ) / (1 + lam : ℂ)) = 1 := by
    field_simp [hdenom]
  rw [hsum, one_mul]

theorem powersStageState_uhfStepIter {lam : ℝ} (hpos : 0 < lam) :
    ∀ {m : ℕ} (k : ℕ) (A : UHFStage m),
      powersStageState lam (m + k) (uhfStepIter k A) = powersStageState lam m A
  | _, 0, _ => rfl
  | m, k + 1, A => by
    change powersStageState lam ((m + k) + 1) (uhfStep (m + k) (uhfStepIter k A)) =
      powersStageState lam m A
    rw [powersStageState_uhfStep hpos (m + k), powersStageState_uhfStepIter hpos k A]

theorem powersStageState_castStage (lam : ℝ) {m n : ℕ} (h : m = n) (A : UHFStage m) :
    powersStageState lam n (castStage h A) = powersStageState lam m A := by
  subst h; rfl

/-- Global Powers state descending cleanly to the inductive colimit `UHFAlg`. -/
def powersAlgState {lam : ℝ} (hpos : 0 < lam) : UHFAlg → ℂ :=
  Quotient.lift (fun x : Σ n : ℕ, UHFStage n => powersStageState lam x.1 x.2) (by
    rintro ⟨m, A⟩ ⟨n, B⟩ ⟨k₁, k₂, h12, heq⟩
    calc
      powersStageState lam m A
          = powersStageState lam (m + k₁) (uhfStepIter k₁ A) :=
        (powersStageState_uhfStepIter hpos k₁ A).symm
      _ = powersStageState lam (n + k₂) (castStage h12 (uhfStepIter k₁ A)) :=
        (powersStageState_castStage lam h12 _).symm
      _ = powersStageState lam (n + k₂) (uhfStepIter k₂ B) := by
        rw [eq_of_heq_stage h12 heq]
      _ = powersStageState lam n B :=
        powersStageState_uhfStepIter hpos k₂ B)

theorem powersAlgState_toUHF {lam : ℝ} (hpos : 0 < lam) (n : ℕ) (A : UHFStage n) :
    powersAlgState hpos (toUHF n A) = powersStageState lam n A := rfl

theorem powersAlgState_one {lam : ℝ} (hpos : 0 < lam) :
    powersAlgState hpos 1 = 1 :=
  powersStageState_one hpos 0

/-! =========================================================================
    3. Stagewise and Global Modular Automorphism Flow on UHFAlg
    ========================================================================= -/

/-- Stage-`n` Powers modular automorphism flow `σ_t^λ(A)_{ij} = (w_i / w_j)^{it} A_{ij}`. -/
def powersStageFlowMap (lam : ℝ) (n : ℕ) (t : ℝ) (A : UHFStage n) : UHFStage n :=
  Matrix.of fun i j =>
    ((powersWeight lam n i / powersWeight lam n j : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) * A i j

def powersStageFlow {lam : ℝ} (hpos : 0 < lam) (n : ℕ) (t : ℝ) :
    UHFStage n →⋆ₐ[ℂ] UHFStage n where
  toFun := powersStageFlowMap lam n t
  map_one' := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hw : powersWeight lam n i ≠ 0 := (powersWeight_pos hpos n i).ne'
      simp only [powersStageFlowMap, Matrix.of_apply, Matrix.one_apply_eq]
      rw [div_self hw, Complex.ofReal_one, Complex.one_cpow, mul_one]
    · simp [powersStageFlowMap, hij]
  map_mul' A B := by
    ext i j
    simp only [powersStageFlowMap, Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmul :
        ((powersWeight lam n i / powersWeight lam n k : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) *
          A i k *
          (((powersWeight lam n k / powersWeight lam n j : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) *
            B k j) =
          (((powersWeight lam n i / powersWeight lam n k : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) *
            ((powersWeight lam n k / powersWeight lam n j : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))) *
            (A i k * B k j) := by
      ring
    rw [hmul, scalar_cpow_mul_ratio (powersWeight_pos hpos n i) (powersWeight_pos hpos n k)
      (powersWeight_pos hpos n j)]
  map_zero' := by ext i j; simp [powersStageFlowMap]
  map_add' A B := by ext i j; simp [powersStageFlowMap, mul_add]
  commutes' c := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hw : powersWeight lam n i ≠ 0 := (powersWeight_pos hpos n i).ne'
      simp only [powersStageFlowMap, Matrix.of_apply, Algebra.algebraMap_eq_smul_one,
        Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [div_self hw, Complex.ofReal_one, Complex.one_cpow, one_mul]
    · simp [powersStageFlowMap, Algebra.algebraMap_eq_smul_one, hij]
  map_star' A := by
    ext i j
    change ((powersWeight lam n i / powersWeight lam n j : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) *
        star (A j i) =
      star (((powersWeight lam n j / powersWeight lam n i : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) *
        A j i)
    rw [star_mul', scalar_cpow_conj_ratio (powersWeight_pos hpos n j) (powersWeight_pos hpos n i) t,
      mul_comm]

theorem powersStageFlow_uhfStep {lam : ℝ} (hpos : 0 < lam) (n : ℕ) (t : ℝ) (A : UHFStage n) :
    powersStageFlow hpos (n + 1) t (uhfStep n A) =
      uhfStep n (powersStageFlow hpos n t A) := by
  have hdenom : 0 < 1 + lam := by linarith
  have h1 : (1 / (1 + lam)) ≠ 0 := (div_pos one_pos hdenom).ne'
  have hl : (lam / (1 + lam)) ≠ 0 := (div_pos hpos hdenom).ne'
  ext a b
  obtain ⟨x, rfl⟩ := (finSumTwoPow n).surjective a
  obtain ⟨y, rfl⟩ := (finSumTwoPow n).surjective b
  simp only [powersStageFlow, StarAlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, powersStageFlowMap, Matrix.of_apply, uhfStep, coe_reindexAlgEquiv,
    reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      simp only [fromBlocks_apply₁₁]
      have hratio :
          powersWeight lam (n + 1) (finSumTwoPow n (Sum.inl i)) /
              powersWeight lam (n + 1) (finSumTwoPow n (Sum.inl j)) =
            powersWeight lam n i / powersWeight lam n j := by
        rw [powersWeight_inl, powersWeight_inl, mul_div_mul_left _ _ h1]
      rw [hratio]
      rfl
    | inr j =>
      simp [fromBlocks_apply₁₂]
  | inr i =>
    cases y with
    | inl j =>
      simp [fromBlocks_apply₂₁]
    | inr j =>
      simp only [fromBlocks_apply₂₂]
      have hratio :
          powersWeight lam (n + 1) (finSumTwoPow n (Sum.inr i)) /
              powersWeight lam (n + 1) (finSumTwoPow n (Sum.inr j)) =
            powersWeight lam n i / powersWeight lam n j := by
        rw [powersWeight_inr, powersWeight_inr, mul_div_mul_left _ _ hl]
      rw [hratio]
      rfl

theorem powersStageFlow_uhfStepIter {lam : ℝ} (hpos : 0 < lam) (t : ℝ) :
    ∀ {m : ℕ} (k : ℕ) (A : UHFStage m),
      powersStageFlow hpos (m + k) t (uhfStepIter k A) =
        uhfStepIter k (powersStageFlow hpos m t A)
  | _, 0, _ => rfl
  | m, k + 1, A => by
    change powersStageFlow hpos ((m + k) + 1) t (uhfStep (m + k) (uhfStepIter k A)) =
      uhfStep (m + k) (uhfStepIter k (powersStageFlow hpos m t A))
    rw [powersStageFlow_uhfStep hpos (m + k) t, powersStageFlow_uhfStepIter hpos t k A]

theorem powersStageFlow_castStage {lam : ℝ} (hpos : 0 < lam) (t : ℝ) {m n : ℕ} (h : m = n)
    (A : UHFStage m) :
    powersStageFlow hpos n t (castStage h A) = castStage h (powersStageFlow hpos m t A) := by
  subst h; rfl

/-- Global Powers modular automorphism flow `σ_t^λ : UHFAlg → UHFAlg` descending
from the stagewise flow along the inductive colimit. -/
def powersAlgFlowFun {lam : ℝ} (hpos : 0 < lam) (t : ℝ) : UHFAlg → UHFAlg :=
  Quotient.lift (fun x : Σ n : ℕ, UHFStage n => toUHF x.1 (powersStageFlow hpos x.1 t x.2)) (by
    rintro ⟨m, A⟩ ⟨n, B⟩ ⟨k₁, k₂, h12, heq⟩
    calc
      toUHF m (powersStageFlow hpos m t A)
          = toUHF (m + k₁) (uhfStepIter k₁ (powersStageFlow hpos m t A)) :=
        (toUHF_uhfStepIter k₁ _).symm
      _ = toUHF (m + k₁) (powersStageFlow hpos (m + k₁) t (uhfStepIter k₁ A)) := by
        rw [powersStageFlow_uhfStepIter hpos t k₁ A]
      _ = toUHF (n + k₂) (castStage h12 (powersStageFlow hpos (m + k₁) t (uhfStepIter k₁ A))) :=
        (toUHF_castStage h12 _).symm
      _ = toUHF (n + k₂) (powersStageFlow hpos (n + k₂) t (castStage h12 (uhfStepIter k₁ A))) := by
        rw [powersStageFlow_castStage hpos t h12]
      _ = toUHF (n + k₂) (powersStageFlow hpos (n + k₂) t (uhfStepIter k₂ B)) := by
        rw [eq_of_heq_stage h12 heq]
      _ = toUHF (n + k₂) (uhfStepIter k₂ (powersStageFlow hpos n t B)) := by
        rw [powersStageFlow_uhfStepIter hpos t k₂ B]
      _ = toUHF n (powersStageFlow hpos n t B) :=
        toUHF_uhfStepIter k₂ _)

theorem powersAlgFlowFun_toUHF {lam : ℝ} (hpos : 0 < lam) (t : ℝ) (n : ℕ) (A : UHFStage n) :
    powersAlgFlowFun hpos t (toUHF n A) = toUHF n (powersStageFlow hpos n t A) := rfl

/-- Exact modular invariance of the global Powers state on `UHFAlg`:
`powersAlgState (powersAlgFlowFun t x) = powersAlgState x`. -/
theorem powersAlgState_flow_invariant {lam : ℝ} (hpos : 0 < lam) (t : ℝ) (x : UHFAlg) :
    powersAlgState hpos (powersAlgFlowFun hpos t x) = powersAlgState hpos x := by
  obtain ⟨n, A, rfl⟩ := exists_toUHF x
  rw [powersAlgFlowFun_toUHF, powersAlgState_toUHF, powersAlgState_toUHF]
  unfold powersStageState
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : powersWeight lam n i ≠ 0 := (powersWeight_pos hpos n i).ne'
  change (powersWeight lam n i : ℂ) * (powersStageFlowMap lam n t A i i) =
    (powersWeight lam n i : ℂ) * A i i
  simp only [powersStageFlowMap, Matrix.of_apply]
  rw [div_self hw, Complex.ofReal_one, Complex.one_cpow, one_mul]

/-! =========================================================================
    4. Exact Point Spectrum {λ^k : k ∈ ℤ}, Non-Traciality, and Outer-Flow Obstruction
    ========================================================================= -/

/-- Stage-`n` Powers modular operator `Δ_λ^{(n)}(A)_{ij} = (w_i / w_j) A_{ij}`. -/
def powersStageModularOp (lam : ℝ) (n : ℕ) (A : UHFStage n) : UHFStage n :=
  Matrix.of fun i j => ((powersWeight lam n i / powersWeight lam n j : ℝ) : ℂ) * A i j

/-- Explicit raising matrix unit `E_k` at stage `k` with `w_row / w_col = λ^k`. -/
def powersRaisingUnit (k : ℕ) : UHFStage k :=
  Matrix.of fun i j =>
    if i.val = 2 ^ k - 1 ∧ j.val = 0 then (1 : ℂ) else 0

theorem powersWeight_zero_val (lam : ℝ) :
    ∀ k : ℕ, powersWeight lam k ⟨0, pow_pos (by decide) k⟩ = (1 / (1 + lam)) ^ k
  | 0 => by simp [powersWeight]
  | k + 1 => by
    have hfin : finSumTwoPow k (Sum.inl ⟨0, pow_pos (by decide) k⟩) =
        ⟨0, pow_pos (by decide) (k + 1)⟩ := by
      ext; simp [finSumTwoPow]
    rw [← hfin, powersWeight_inl, powersWeight_zero_val lam k]
    ring

theorem powersWeight_last_val (lam : ℝ) :
    ∀ k : ℕ, powersWeight lam k ⟨2 ^ k - 1, Nat.sub_lt (pow_pos (by decide) k) one_pos⟩ =
      (lam / (1 + lam)) ^ k
  | 0 => by simp [powersWeight]
  | k + 1 => by
    have hfin : finSumTwoPow k (Sum.inr ⟨2 ^ k - 1, Nat.sub_lt (pow_pos (by decide) k) one_pos⟩) =
        ⟨2 ^ (k + 1) - 1, Nat.sub_lt (pow_pos (by decide) (k + 1)) one_pos⟩ := by
      ext
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
      have hp2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
      simp [finSumTwoPow, hp2]
      omega
    rw [← hfin, powersWeight_inr, powersWeight_last_val lam k]
    ring

/-- Positive point-spectrum eigenvector theorem: for every `k : ℕ`,
`Δ_λ^{(k)}(E_k) = λ^k E_k`. Note: `{λ^k : k ∈ ℤ}` is the algebraic **point spectrum**;
the full closed spectrum for `0 < λ < 1` additionally contains the accumulation point `0`. -/
theorem powersStageModularOp_raising_eigenvector {lam : ℝ} (hpos : 0 < lam) (k : ℕ) :
    powersStageModularOp lam k (powersRaisingUnit k) = (lam ^ k : ℂ) • powersRaisingUnit k := by
  have hdenom : (1 + lam) ≠ 0 := (add_pos zero_lt_one hpos).ne'
  ext i j
  by_cases hij : i.val = 2 ^ k - 1 ∧ j.val = 0
  · have hi : i = ⟨2 ^ k - 1, Nat.sub_lt (pow_pos (by decide) k) one_pos⟩ := Fin.ext hij.1
    have hj : j = ⟨0, pow_pos (by decide) k⟩ := Fin.ext hij.2
    subst hi hj
    simp only [powersStageModularOp, powersRaisingUnit, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, and_self, ↓reduceIte, mul_one]
    rw [powersWeight_last_val, powersWeight_zero_val]
    have hr : (lam / (1 + lam)) ^ k / (1 / (1 + lam)) ^ k = lam ^ k := by
      rw [div_pow, div_pow, one_pow]
      field_simp [hdenom]
    exact_mod_cast hr
  · rw [powersStageModularOp, powersRaisingUnit, Matrix.of_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, if_neg hij, mul_zero, mul_zero]

/-- Negative point-spectrum eigenvector theorem: for every `k : ℕ`,
`Δ_λ^{(k)}(E_kᴴ) = (λ^k)⁻¹ E_kᴴ`. -/
theorem powersStageModularOp_lowering_eigenvector {lam : ℝ} (hpos : 0 < lam) (k : ℕ) :
    powersStageModularOp lam k (powersRaisingUnit k)ᴴ =
      ((lam ^ k : ℂ)⁻¹) • (powersRaisingUnit k)ᴴ := by
  have hdenom : (1 + lam) ≠ 0 := (add_pos zero_lt_one hpos).ne'
  ext i j
  by_cases hij : j.val = 2 ^ k - 1 ∧ i.val = 0
  · have hi : i = ⟨0, pow_pos (by decide) k⟩ := Fin.ext hij.2
    have hj : j = ⟨2 ^ k - 1, Nat.sub_lt (pow_pos (by decide) k) one_pos⟩ := Fin.ext hij.1
    subst hi hj
    simp only [powersStageModularOp, powersRaisingUnit, Matrix.of_apply,
      Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, and_self, ↓reduceIte,
      star_one, mul_one]
    rw [powersWeight_zero_val, powersWeight_last_val]
    have hr : (1 / (1 + lam)) ^ k / (lam / (1 + lam)) ^ k = (lam ^ k)⁻¹ := by
      rw [div_pow, div_pow, one_pow]
      field_simp [hdenom, hpos.ne']
    exact_mod_cast hr
  · rw [powersStageModularOp, powersRaisingUnit, Matrix.of_apply, Matrix.smul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul, if_neg hij, star_zero,
      mul_zero, mul_zero]

/-- Non-traciality at stage 1 whenever `λ ≠ 1`. -/
theorem powersStageState_non_tracial {lam : ℝ} (hpos : 0 < lam) (hne : lam ≠ 1) :
    ∃ A B : UHFStage 1,
      powersStageState lam 1 (A * B) ≠ powersStageState lam 1 (B * A) := by
  have hdenom : (1 + lam) ≠ 0 := (add_pos zero_lt_one hpos).ne'
  let E01 : UHFStage 1 := Matrix.of ![![0, 1], ![0, 0]]
  let E10 : UHFStage 1 := Matrix.of ![![0, 0], ![1, 0]]
  have hsum2 : ∀ f : Fin (2 ^ 1) → ℂ, (∑ i : Fin (2 ^ 1), f i) = f 0 + f 1 := fun f => by
    change (∑ i : Fin 2, f (Fin.cast rfl i)) = f 0 + f 1
    exact Fin.sum_univ_two _
  refine ⟨E01, E10, ?_⟩
  have hL : powersStageState lam 1 (E01 * E10) = ((1 / (1 + lam) : ℝ) : ℂ) := by
    unfold powersStageState
    rw [hsum2]
    have hw0 : powersWeight lam 1 0 = 1 / (1 + lam) := by
      simpa using powersWeight_zero_val lam 1
    have hm00 : (E01 * E10) 0 0 = 1 := by simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
    have hm11 : (E01 * E10) 1 1 = 0 := by simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hw0, hm00, hm11]
    simp
  have hR : powersStageState lam 1 (E10 * E01) = ((lam / (1 + lam) : ℝ) : ℂ) := by
    unfold powersStageState
    rw [hsum2]
    have hw1 : powersWeight lam 1 1 = lam / (1 + lam) := by
      simpa using powersWeight_last_val lam 1
    have hm00 : (E10 * E01) 0 0 = 0 := by simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
    have hm11 : (E10 * E01) 1 1 = 1 := by simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hw1, hm00, hm11]
    simp
  rw [hL, hR]
  intro heq
  have hreal : (1 / (1 + lam) : ℝ) = lam / (1 + lam) := Complex.ofReal_injective heq
  have hlam : 1 = lam := by
    have hmul := congrArg (· * (1 + lam)) hreal
    rw [div_mul_cancel₀ _ hdenom, div_mul_cancel₀ _ hdenom] at hmul
    exact hmul
  exact hne hlam.symm

/-- Injectivity of `toUHF n` derived from `uhfStepIter_norm` in `UHFColimitCStarCompletion`. -/
theorem toUHF_injective (n : ℕ) : Function.Injective (toUHF n) := by
  intro A B h
  obtain ⟨k₁, k₂, h12, heq⟩ := Quotient.exact h
  have hk : k₁ = k₂ := Nat.add_left_cancel h12
  subst hk
  have hAB : uhfStepIter k₁ A = uhfStepIter k₁ B := eq_of_heq heq
  have hsub : uhfStepIter k₁ (A - B) = 0 := by
    rw [sub_eq_add_neg, uhfStepIter_add, uhfStepIter_neg, ← sub_eq_add_neg, hAB, sub_self]
  have hnorm : ‖A - B‖ = 0 := by
    rw [← uhfStepIter_norm k₁ (A - B), hsub, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Finite-stage outer-flow obstruction: whenever `(λ : ℂ)^{it} ≠ 1`, NO finite-stage
unitary `U : UHFStage m` (`U * Uᴴ = 1`) inner-implements `powersAlgFlowFun hpos t` on `UHFAlg`. -/
theorem powersAlgFlow_not_inner_at_stage {lam : ℝ} (hpos : 0 < lam) (t : ℝ)
    (ht : (lam : ℂ) ^ (Complex.I * (t : ℂ)) ≠ 1) (m : ℕ) (U : UHFStage m) (hU : U * Uᴴ = 1) :
    ∃ x : UHFAlg,
      toUHF m U * x * star (toUHF m U) ≠ powersAlgFlowFun hpos t x := by
  let Enext : UHFStage (m + 1) :=
    reindexAlgEquiv ℂ ℂ (finSumTwoPow m) (fromBlocks 0 1 0 0)
  refine ⟨toUHF (m + 1) Enext, ?_⟩
  have hcomm : uhfStep m U * Enext = Enext * uhfStep m U := by
    unfold uhfStep Enext
    rw [← map_mul, ← map_mul]
    congr 1
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp
  have hleft :
      toUHF m U * toUHF (m + 1) Enext * star (toUHF m U) = toUHF (m + 1) Enext := by
    rw [← toUHF_uhfStep m U, star_toUHF, mul_toUHF, mul_toUHF, hcomm, Matrix.mul_assoc]
    have hunit : uhfStep m U * star (uhfStep m U) = 1 := by
      rw [← uhfStep_star, ← uhfStep_mul]
      change uhfStep m (U * Uᴴ) = 1
      rw [hU, uhfStep_one]
    rw [hunit, Matrix.mul_one]
  intro heq
  rw [hleft, powersAlgFlowFun_toUHF] at heq
  have hstage := toUHF_injective (m + 1) heq.symm
  let i0 : Fin (2 ^ m) := ⟨0, pow_pos (by decide) m⟩
  have hentry := congrArg (fun M : UHFStage (m + 1) =>
    M (finSumTwoPow m (Sum.inl i0)) (finSumTwoPow m (Sum.inr i0))) hstage
  have hR : Enext (finSumTwoPow m (Sum.inl i0)) (finSumTwoPow m (Sum.inr i0)) = 1 := by
    simp [Enext]
  have hL :
      powersStageFlow hpos (m + 1) t Enext
          (finSumTwoPow m (Sum.inl i0)) (finSumTwoPow m (Sum.inr i0)) =
        ((lam⁻¹ : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) := by
    change ((powersWeight lam (m + 1) (finSumTwoPow m (Sum.inl i0)) /
        powersWeight lam (m + 1) (finSumTwoPow m (Sum.inr i0)) : ℝ) : ℂ) ^
        (Complex.I * (t : ℂ)) *
        Enext (finSumTwoPow m (Sum.inl i0)) (finSumTwoPow m (Sum.inr i0)) = _
    rw [hR, mul_one, powersWeight_inl, powersWeight_inr]
    have hdenom : (1 + lam) ≠ 0 := by linarith
    have hw0 : powersWeight lam m i0 ≠ 0 := (powersWeight_pos hpos m i0).ne'
    have hdiv : ((1 / (1 + lam)) * powersWeight lam m i0) /
        ((lam / (1 + lam)) * powersWeight lam m i0) = lam⁻¹ := by
      field_simp [hdenom, hw0, hpos.ne']
    rw [hdiv]
  rw [hL, hR] at hentry
  exact scalar_cpow_inv_ne_one hpos t ht hentry

end InfoGeometry.Algebra.UHFPowersModularState
