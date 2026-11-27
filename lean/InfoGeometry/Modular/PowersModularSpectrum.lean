/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.UHFColimitCStarCompletion
import InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit

/-!
# Powers Modular Spectrum, Limit-Point Closure, and Finite-Stage Boundaries (`TT-F3b`)

This module develops the spectral theory of the Powers states `powersState lam k` and
modular operators `powersModularOp lam k` on the finite UHF matrix stages
`UHFStage k = Matrix (Fin (2^k)) (Fin (2^k)) ℂ` (reusing
`InfoGeometry.Algebra.UHFColimitCStarCompletion`) and establishes exact finite-stage
boundaries distinguishing finite matrix stages and tracial colimits from infinite-dimensional
Type `III_λ` factors (`InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit`).

Note on module provenance: the sibling module `AlgebraicCrossedProductAndPowersWitness` could
not be imported because it currently fails compilation, so the Powers finite-stage state and
modular-operator primitives (`bitPopcount`, `powersWeight`, `powersState`, `powersModularOp`,
`powersModularOp_point_spectrum`) are constructed directly and self-containedly here on top of
`InfoGeometry.Algebra.UHFColimitCStarCompletion`.

1. **Non-Commutativity Witness (`UHFStage 1 = Matrix (Fin 2) (Fin 2) ℂ`)**:
   Explicit matrix units `E₀₁, E₁₀` satisfying `E₀₁ * E₁₀ ≠ E₁₀ * E₀₁` (`uhfStage1_noncomm`).
2. **Powers Finite-Stage States, KMS Condition, and Point Spectrum**:
   Compatible Powers product states `powersState lam k` (`powersState_compatible_uhfStep`,
   `powersState_one`) satisfying the KMS relation `powersState_kms` for `powersModularOp lam k`,
   with point spectrum `powersPointSpec lam := Set.range (fun k : ℤ => lam ^ k)`. For `0 < lam`,
   `x ∈ powersPointSpec lam` holds if and only if `x` is a real eigenvalue of
   `powersModularOp lam m` at some finite stage `m : ℕ` (`powersPointSpec_iff_exists_eigenvector`).
3. **Strict Antitonicity, Injectivity, and Exclusion of `0`**:
   For `0 < lam < 1`, `k ↦ lam ^ k` is strictly antitone (`powersPointSpec_strictAnti`) and
   injective (`powersPointSpec_injective`). For `0 < lam`, `0 ∉ powersPointSpec lam`
   (`zero_notMem_powersPointSpec`).
4. **Topological Limit-Point Closure (`{0} ∪ {λ^k | k ∈ ℤ}`)**:
   For `0 < lam < 1`, `0 ∈ closure (powersPointSpec lam)` (`zero_mem_closure_powersPointSpec`)
   since `lam ^ n → 0` as `n → ∞`, `insert 0 (powersPointSpec lam)` is closed
   (`isClosed_insert_zero_powersPointSpec`), and therefore
   `closure (powersPointSpec lam) = insert 0 (powersPointSpec lam)`
   (`closure_powersPointSpec_eq_insert_zero`).
5. **Finite-Stage Non-Type-III Boundary**:
   - Every fixed stage `UHFStage k` is finite-dimensional over `ℂ` (`uhfStage_finiteDimensional`),
     carries the normalized tracial state `uhfStageNormTrace k` (`uhfStageNormTrace_one`,
     `uhfStageNormTrace_comm`), and has every real modular eigenvalue bounded below by `lam ^ k`
     (`stage_eigenvalue_ge_pow`), so `lam ^ (k + 1)` is never an eigenvalue at stage `k`
     (`next_power_not_stage_eigenvalue`).
   - `UHFCStar` is the norm `C*`-completion `UniformSpace.Completion UHFAlg`, distinct from the
     GNS weak-operator closure `π_{ω_λ}(UHF)''`.
   - Every element of the real inductive colimit `RealBlockColimit m` factors through a
     finite-dimensional real stage `RealBlockStage m k` (`realBlockColimit_factors_through_stage`,
     `realBlockStage_finiteDimensional`), and for `m ≠ 0` `RealBlockColimit m` admits the
     normalized faithful tracial functional `realBlockColimitNormTrace`
     (`realBlockColimitNormTrace_one`, `realBlockColimitNormTrace_mul_comm`,
     `realBlockColimitNormTrace_faithful`).
   - Infinite weak-operator GNS closure completion, factoriality `Z(M) = ℂ·1`, and Type `III_λ`
     classification remain open contracts outside this finite-stage formalization.
-/

noncomputable section

namespace InfoGeometry.Modular.PowersModularSpectrum

open InfoGeometry.Algebra.UHFColimitCStarCompletion
open InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit

/-! ## 1. Non-Commutativity Witness on `UHFStage 1 = Matrix (Fin 2) (Fin 2) ℂ` -/

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ` (`UHFStage 1`). -/
theorem uhfStage1_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp at h00

/-- Non-commutativity witness stated directly in the `UHFStage 1` carrier. -/
theorem uhfStage1_stage_noncomm :
    ∃ A B : UHFStage 1, A * B ≠ B * A :=
  uhfStage1_noncomm

/-! ## 2. Finite-Stage Powers Product States & Modular Operators on `UHFStage k` -/

/-- Binary Hamming weight (number of `1`-bits in the binary expansion of `n`). -/
def bitPopcount : ℕ → ℕ :=
  Nat.binaryRec 0 (fun b _ r => (if b then 1 else 0) + r)

@[simp]
theorem bitPopcount_zero : bitPopcount 0 = 0 := by
  simp [bitPopcount]

theorem bitPopcount_step (n : ℕ) (hn : n ≠ 0) :
    bitPopcount n = n % 2 + bitPopcount (n / 2) := by
  have hbit : Nat.bit (n % 2 == 1) (n / 2) = n := by
    cases Nat.mod_two_eq_zero_or_one n with
    | inl h =>
        simp [h, Nat.bit]
        omega
    | inr h =>
        simp [h, Nat.bit]
        omega
  have hrec := Nat.binaryRec_eq (motive := fun _ => ℕ) (zero := 0)
    (bit := fun b _ r => (if b then 1 else 0) + r) (n % 2 == 1) (n / 2)
    (Or.inr fun hdiv => by
      by_contra hb
      have hm0 : n % 2 = 0 := by
        cases Nat.mod_two_eq_zero_or_one n with
        | inl h => exact h
        | inr h => simp [h] at hb
      exact hn (by omega))
  rw [hbit] at hrec
  change bitPopcount n = (if (n % 2 == 1) then 1 else 0) + bitPopcount (n / 2) at hrec
  rw [hrec]
  cases Nat.mod_two_eq_zero_or_one n with
  | inl h => simp [h]
  | inr h => simp [h]

/-- Binary doubling identity: for every `r < 2^k`, adding `2^k` adds `1` to `bitPopcount`. -/
theorem bitPopcount_twoPow_add :
    ∀ (k r : ℕ), r < 2 ^ k → bitPopcount (2 ^ k + r) = 1 + bitPopcount r
  | 0, r, hr => by
      have hr0 : r = 0 := by omega
      subst hr0
      rw [Nat.pow_zero, Nat.add_zero, bitPopcount_zero, Nat.add_zero,
        bitPopcount_step 1 (by decide), bitPopcount_zero]
  | k + 1, r, hr => by
      have hne : 2 ^ (k + 1) + r ≠ 0 := by positivity
      rw [bitPopcount_step _ hne]
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
      have hdiv : (2 ^ (k + 1) + r) / 2 = 2 ^ k + r / 2 := by omega
      have hmod : (2 ^ (k + 1) + r) % 2 = r % 2 := by omega
      have hrl : r / 2 < 2 ^ k := by omega
      rw [hdiv, hmod, bitPopcount_twoPow_add k (r / 2) hrl]
      by_cases hr0 : r = 0
      · subst hr0
        simp [bitPopcount_zero]
      · rw [bitPopcount_step r hr0]
        omega

/-- Binary all-ones integer `2^k - 1` has Hamming weight `k`. -/
theorem bitPopcount_twoPow_sub_one : ∀ k : ℕ, bitPopcount (2 ^ k - 1) = k
  | 0 => by
      rw [Nat.pow_zero, Nat.sub_self, bitPopcount_zero]
  | k + 1 => by
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ', two_mul]
      have hsplit : 2 ^ (k + 1) - 1 = 2 ^ k + (2 ^ k - 1) := by omega
      have hlt : 2 ^ k - 1 < 2 ^ k := Nat.sub_lt (Nat.two_pow_pos k) (by decide)
      rw [hsplit, bitPopcount_twoPow_add k (2 ^ k - 1) hlt, bitPopcount_twoPow_sub_one k]
      omega

/-- Powers diagonal weight `(1 / (1 + lam))^k * lam^(bitPopcount i)` at UHF stage `k`. -/
def powersWeight (lam : ℝ) (k : ℕ) (i : Fin (2 ^ k)) : ℝ :=
  (1 / (1 + lam)) ^ k * lam ^ bitPopcount i.val

theorem powersWeight_pos {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (i : Fin (2 ^ k)) :
    0 < powersWeight lam k i := by
  unfold powersWeight
  have h1p : 0 < 1 + lam := add_pos zero_lt_one hlam
  exact mul_pos (pow_pos (one_div_pos.mpr h1p) k) (pow_pos hlam (bitPopcount i.val))

theorem powersWeight_finSum_inl (lam : ℝ) (k : ℕ) (i : Fin (2 ^ k)) :
    powersWeight lam (k + 1) (finSumTwoPow k (Sum.inl i)) =
      (1 / (1 + lam)) * powersWeight lam k i := by
  unfold powersWeight
  have hval : (finSumTwoPow k (Sum.inl i)).val = i.val := by
    simp [finSumTwoPow]
  rw [hval, pow_succ', mul_assoc]

theorem powersWeight_finSum_inr (lam : ℝ) (k : ℕ) (i : Fin (2 ^ k)) :
    powersWeight lam (k + 1) (finSumTwoPow k (Sum.inr i)) =
      (lam / (1 + lam)) * powersWeight lam k i := by
  unfold powersWeight
  have hval : (finSumTwoPow k (Sum.inr i)).val = 2 ^ k + i.val := by
    simp [finSumTwoPow, Nat.add_comm]
  rw [hval, bitPopcount_twoPow_add k i.val i.isLt, pow_succ', pow_add, pow_one]
  ring

/-- Stage-`k` Powers linear functional `ω_λ^{(k)}(A) = ∑ i, w_i A_{i,i}` on `UHFStage k`. -/
def powersState (lam : ℝ) (k : ℕ) (A : UHFStage k) : ℂ :=
  ∑ i : Fin (2 ^ k), (powersWeight lam k i : ℂ) * A i i

/-- Inductive compatibility of `powersState` with `uhfStep k`. -/
theorem powersState_compatible_uhfStep {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (A : UHFStage k) :
    powersState lam (k + 1) (uhfStep k A) = powersState lam k A := by
  unfold powersState
  rw [← Equiv.sum_comp (finSumTwoPow k), Fintype.sum_sum_type]
  have hinl : ∀ i : Fin (2 ^ k),
      (uhfStep k A) (finSumTwoPow k (Sum.inl i)) (finSumTwoPow k (Sum.inl i)) = A i i := by
    intro i
    simp [uhfStep]
  have hinr : ∀ i : Fin (2 ^ k),
      (uhfStep k A) (finSumTwoPow k (Sum.inr i)) (finSumTwoPow k (Sum.inr i)) = A i i := by
    intro i
    simp [uhfStep]
  simp_rw [hinl, hinr, powersWeight_finSum_inl, powersWeight_finSum_inr, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1p : (1 + lam : ℝ) ≠ 0 := (add_pos zero_lt_one hlam).ne'
  have hreal : (1 / (1 + lam) + lam / (1 + lam) : ℝ) = 1 := by
    field_simp [h1p]
  have hcmul :
      ((1 / (1 + lam) * powersWeight lam k i : ℝ) : ℂ) * A i i +
        ((lam / (1 + lam) * powersWeight lam k i : ℝ) : ℂ) * A i i =
      (((1 / (1 + lam) + lam / (1 + lam)) * powersWeight lam k i : ℝ) : ℂ) * A i i := by
    rw [← add_mul]
    congr 1
    push_cast
    rw [← add_mul]
  rw [hcmul, hreal, one_mul]

/-- Normalization: `powersState lam k 1 = 1` for every stage `k` and `lam > 0`. -/
theorem powersState_one {lam : ℝ} (hlam : 0 < lam) : ∀ k : ℕ, powersState lam k 1 = 1
  | 0 => by
      simp [powersState, powersWeight]
  | k + 1 => by
      rw [← uhfStep_one k, powersState_compatible_uhfStep hlam k 1, powersState_one hlam k]

/-- Stage-`k` Powers modular operator `Δ_k(X)_{i,j} = (w_i / w_j) X_{i,j}`. -/
def powersModularOp (lam : ℝ) (k : ℕ) (X : UHFStage k) : UHFStage k :=
  Matrix.of fun i j => ((powersWeight lam k i / powersWeight lam k j : ℝ) : ℂ) * X i j

/-- Exact finite-stage KMS identity for `powersState`:
`ω_λ^{(k)}(A * Δ_k(B)) = ω_λ^{(k)}(B * A)`. -/
theorem powersState_kms {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (A B : UHFStage k) :
    powersState lam k (A * powersModularOp lam k B) = powersState lam k (B * A) := by
  unfold powersState powersModularOp
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hwi : powersWeight lam k i ≠ 0 := (powersWeight_pos hlam k i).ne'
  have hmul :
      (powersWeight lam k i : ℂ) * ((powersWeight lam k j / powersWeight lam k i : ℝ) : ℂ) =
        (powersWeight lam k j : ℂ) := by
    exact_mod_cast mul_div_cancel₀ (powersWeight lam k j) hwi
  calc
    (powersWeight lam k i : ℂ) *
        (A i j * (((powersWeight lam k j / powersWeight lam k i : ℝ) : ℂ) * B j i))
        = ((powersWeight lam k i : ℂ) * ((powersWeight lam k j / powersWeight lam k i : ℝ) : ℂ)) *
            (A i j * B j i) := by
          simp only [mul_assoc, mul_left_comm]
    _ = (powersWeight lam k j : ℂ) * (B j i * A i j) := by
          rw [hmul, mul_comm (A i j) (B j i)]

/-- Elementary matrix unit `e_{i,j}` in `UHFStage k`. -/
def elemUnit (k : ℕ) (i j : Fin (2 ^ k)) : UHFStage k :=
  Matrix.of fun r c => if r = i ∧ c = j then (1 : ℂ) else 0

theorem elemUnit_ne_zero (k : ℕ) (i j : Fin (2 ^ k)) : elemUnit k i j ≠ 0 := by
  intro h
  have h0 := congr_fun (congr_fun h i) j
  simp [elemUnit] at h0

theorem powersModularOp_elemUnit (lam : ℝ) (k : ℕ) (i j : Fin (2 ^ k)) :
    powersModularOp lam k (elemUnit k i j) =
      ((powersWeight lam k i / powersWeight lam k j : ℝ) : ℂ) • elemUnit k i j := by
  ext r c
  by_cases hrc : r = i ∧ c = j
  · rcases hrc with ⟨rfl, rfl⟩
    simp [powersModularOp, elemUnit]
  · simp [powersModularOp, elemUnit, hrc]

/-- For every integer `m : ℤ`, at stage `k = m.natAbs` there exists a nonzero matrix unit
`E : UHFStage k` with exact modular eigenvalue `(lam ^ m : ℂ)`. -/
theorem powersModularOp_point_spectrum {lam : ℝ} (hlam : 0 < lam) (m : ℤ) :
    ∃ (E : UHFStage m.natAbs),
      E ≠ 0 ∧ powersModularOp lam m.natAbs E = ((lam ^ m : ℝ) : ℂ) • E := by
  let k := m.natAbs
  let i0 : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
  let i1 : Fin (2 ^ k) := ⟨2 ^ k - 1, Nat.sub_lt (Nat.two_pow_pos k) (by decide)⟩
  have hw_ratio_pos :
      powersWeight lam k i1 / powersWeight lam k i0 = lam ^ k := by
    unfold powersWeight
    have h0 : bitPopcount i0.val = 0 := by simp [i0]
    have h1 : bitPopcount i1.val = k := bitPopcount_twoPow_sub_one k
    rw [h0, h1, pow_zero, mul_one]
    have hc : (1 / (1 + lam)) ^ k ≠ 0 := by positivity
    field_simp [hc]
  have hw_ratio_neg :
      powersWeight lam k i0 / powersWeight lam k i1 = (lam ^ k)⁻¹ := by
    rw [← hw_ratio_pos]
    have hpi0 : powersWeight lam k i0 ≠ 0 := (powersWeight_pos hlam k i0).ne'
    have hpi1 : powersWeight lam k i1 ≠ 0 := (powersWeight_pos hlam k i1).ne'
    field_simp [hpi0, hpi1]
  rcases Int.natAbs_eq m with hm | hm
  · refine ⟨elemUnit k i1 i0, elemUnit_ne_zero k i1 i0, ?_⟩
    rw [powersModularOp_elemUnit lam k i1 i0, hw_ratio_pos]
    have hpow : lam ^ m = lam ^ k := by
      conv_lhs => rw [hm]
      exact zpow_natCast lam k
    rw [hpow]
  · refine ⟨elemUnit k i0 i1, elemUnit_ne_zero k i0 i1, ?_⟩
    rw [powersModularOp_elemUnit lam k i0 i1, hw_ratio_neg]
    have hpow : lam ^ m = (lam ^ k)⁻¹ := by
      conv_lhs => rw [hm]
      exact zpow_neg lam k
    rw [hpow]

/-! ## 3. Powers Point Spectrum & Finite-Stage Eigenvalue Characterization -/

/-- The Powers modular point spectrum `{lam ^ k | k : ℤ}` for parameter `lam : ℝ`. -/
def powersPointSpec (lam : ℝ) : Set ℝ :=
  Set.range (fun k : ℤ => lam ^ k)

/-- Every integer power `lam ^ k` belongs to `powersPointSpec lam`. -/
theorem zpow_mem_powersPointSpec (lam : ℝ) (k : ℤ) :
    lam ^ k ∈ powersPointSpec lam :=
  ⟨k, rfl⟩

/-- Every element of `powersPointSpec lam` (`0 < lam`) has an exact nonzero eigenvector in
`UHFStage k.natAbs` for `powersModularOp lam k.natAbs`. -/
theorem powersPointSpec_eigenvalue_witness {lam : ℝ} (hlam : 0 < lam) {x : ℝ}
    (hx : x ∈ powersPointSpec lam) :
    ∃ (k : ℤ) (E : UHFStage k.natAbs),
      x = lam ^ k ∧ E ≠ 0 ∧ powersModularOp lam k.natAbs E = (x : ℂ) • E := by
  rcases hx with ⟨k, rfl⟩
  obtain ⟨E, hE0, hEeig⟩ := powersModularOp_point_spectrum hlam k
  exact ⟨k, E, rfl, hE0, hEeig⟩

/-- Entrywise coordinate extraction for a nonzero eigenvector of `powersModularOp lam m`:
if `E i j ≠ 0` and `powersModularOp lam m E = (x : ℂ) • E`, then `x` equals the integer power
`lam ^ ((bitPopcount i.val : ℤ) - (bitPopcount j.val : ℤ))`. -/
private theorem stage_eigenvalue_eq_zpow {lam : ℝ} (hlam : 0 < lam) {m : ℕ} {E : UHFStage m}
    {i j : Fin (2 ^ m)} (hij : E i j ≠ 0) {x : ℝ}
    (heig : powersModularOp lam m E = (x : ℂ) • E) :
    x = lam ^ ((bitPopcount i.val : ℤ) - (bitPopcount j.val : ℤ)) := by
  have heig_ij := congr_fun (congr_fun heig i) j
  simp only [powersModularOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at heig_ij
  have hratio_c : ((powersWeight lam m i / powersWeight lam m j : ℝ) : ℂ) = (x : ℂ) :=
    mul_right_cancel₀ hij heig_ij
  have hratio : powersWeight lam m i / powersWeight lam m j = x :=
    Complex.ofReal_injective hratio_c
  have hc : (1 / (1 + lam)) ^ m ≠ 0 := by positivity
  calc
    x = powersWeight lam m i / powersWeight lam m j := hratio.symm
    _ = lam ^ bitPopcount i.val / lam ^ bitPopcount j.val := by
      unfold powersWeight
      exact mul_div_mul_left _ _ hc
    _ = lam ^ ((bitPopcount i.val : ℤ) - (bitPopcount j.val : ℤ)) := by
      rw [zpow_sub₀ hlam.ne', zpow_natCast, zpow_natCast]

/-- Any real eigenvalue `x` of `powersModularOp lam m` at any finite stage `m` lies in
`powersPointSpec lam`. -/
theorem stage_eigenvalue_mem_powersPointSpec {lam : ℝ} (hlam : 0 < lam) {m : ℕ}
    {E : UHFStage m} (hE : E ≠ 0) {x : ℝ}
    (heig : powersModularOp lam m E = (x : ℂ) • E) :
    x ∈ powersPointSpec lam := by
  have hij : ∃ i j : Fin (2 ^ m), E i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hE
    ext i j
    exact h i j
  rcases hij with ⟨i, j, hij_ne⟩
  exact ⟨(bitPopcount i.val : ℤ) - (bitPopcount j.val : ℤ),
    (stage_eigenvalue_eq_zpow hlam hij_ne heig).symm⟩

/-- Exact equivalence between membership in `powersPointSpec lam` (`0 < lam`) and existence of a
nonzero eigenvector at some finite UHF stage `UHFStage m`. -/
theorem powersPointSpec_iff_exists_eigenvector {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    x ∈ powersPointSpec lam ↔
      ∃ (m : ℕ) (E : UHFStage m), E ≠ 0 ∧ powersModularOp lam m E = (x : ℂ) • E := by
  constructor
  · intro hx
    obtain ⟨k, E, -, hE0, heig⟩ := powersPointSpec_eigenvalue_witness hlam hx
    exact ⟨k.natAbs, E, hE0, heig⟩
  · rintro ⟨m, E, hE0, heig⟩
    exact stage_eigenvalue_mem_powersPointSpec hlam hE0 heig

/-! ## 4. Strict Antitonicity, Injectivity, and Exclusion of `0` -/

/-- For `0 < lam < 1`, the integer power map `k ↦ lam ^ k` is strictly antitone. -/
theorem powersPointSpec_strictAnti {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictAnti (fun k : ℤ => lam ^ k) :=
  zpow_right_strictAnti₀ hlam0 hlam1

/-- For `0 < lam < 1`, the integer power eigenvalues `lam ^ k` (`k : ℤ`) are pairwise distinct. -/
theorem powersPointSpec_injective {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Function.Injective (fun k : ℤ => lam ^ k) :=
  (powersPointSpec_strictAnti hlam0 hlam1).injective

/-- Zero is not in the point spectrum `powersPointSpec lam` whenever `0 < lam`. -/
theorem zero_notMem_powersPointSpec {lam : ℝ} (hlam0 : 0 < lam) :
    (0 : ℝ) ∉ powersPointSpec lam := by
  rintro ⟨k, hk⟩
  exact (zpow_pos hlam0 k).ne' hk

/-! ## 5. Limit-Point Closure: `closure (powersPointSpec lam) = insert 0 (powersPointSpec lam)` -/

/-- For `0 < lam < 1`, `0` is a limit point in the closure of `powersPointSpec lam` because
`lam ^ n → 0` as `n → ∞`. -/
theorem zero_mem_closure_powersPointSpec {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (0 : ℝ) ∈ closure (powersPointSpec lam) :=
  mem_closure_of_tendsto
    (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1)
    (Filter.Eventually.of_forall fun n : ℕ => ⟨(n : ℤ), zpow_natCast lam n⟩)

/-- For `0 < lam < 1`, the set `insert 0 (powersPointSpec lam)` is closed in `ℝ`. -/
theorem isClosed_insert_zero_powersPointSpec {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    IsClosed (insert (0 : ℝ) (powersPointSpec lam)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rcases lt_trichotomy x 0 with hx_lt | rfl | hx_pos
  · refine ⟨Set.Iio 0, fun y hy hy_mem => ?_, isOpen_Iio, hx_lt⟩
    rcases hy_mem with rfl | ⟨k, rfl⟩
    · exact absurd (Set.mem_Iio.mp hy) (lt_irrefl 0)
    · exact absurd hy (not_lt.mpr (zpow_pos hlam0 k).le)
  · exact absurd (Set.mem_insert 0 _) hx
  · have hinv : 1 < lam⁻¹ := (one_lt_inv₀ hlam0).mpr hlam1
    obtain ⟨n, hlo, hhi⟩ := exists_mem_Ico_zpow hx_pos hinv
    rw [inv_zpow'] at hlo hhi
    have hlo_lt : lam ^ (-n) < x :=
      lt_of_le_of_ne hlo fun h => hx (Set.mem_insert_of_mem 0 ⟨-n, h⟩)
    refine ⟨Set.Ioo (lam ^ (-n)) (lam ^ (-(n + 1))), ?_, isOpen_Ioo, ⟨hlo_lt, hhi⟩⟩
    intro y hy hy_mem
    rcases hy_mem with rfl | ⟨m, rfl⟩
    · exact absurd hy.1 (not_lt.mpr (zpow_pos hlam0 (-n)).le)
    · have hm1 : m < -n := (zpow_lt_zpow_iff_right_of_lt_one₀ hlam0 hlam1).mp hy.1
      have hm2 : -(n + 1) < m := (zpow_lt_zpow_iff_right_of_lt_one₀ hlam0 hlam1).mp hy.2
      omega

/-- Exact topological closure of the Powers point spectrum for `0 < lam < 1`:
`closure (powersPointSpec lam) = insert 0 (powersPointSpec lam)`. -/
theorem closure_powersPointSpec_eq_insert_zero {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    closure (powersPointSpec lam) = insert (0 : ℝ) (powersPointSpec lam) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact closure_minimal (Set.subset_insert 0 (powersPointSpec lam))
      (isClosed_insert_zero_powersPointSpec hlam0 hlam1)
  · exact Set.insert_subset_iff.mpr
      ⟨zero_mem_closure_powersPointSpec hlam0 hlam1, subset_closure⟩

/-! ## 6. Finite-Stage Non-Type-III Boundary Theorems -/

/-- Every `r < 2 ^ k` has binary Hamming weight at most `k`. -/
theorem bitPopcount_le_of_lt_twoPow : ∀ {k r : ℕ}, r < 2 ^ k → bitPopcount r ≤ k
  | 0, r, hr => by
      have hr0 : r = 0 := by omega
      subst hr0
      simp
  | k + 1, r, hr => by
      by_cases hr0 : r = 0
      · subst hr0
        simp
      · rw [bitPopcount_step r hr0]
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
        have hhalf : r / 2 < 2 ^ k := by omega
        have ih := bitPopcount_le_of_lt_twoPow hhalf
        have hmod : r % 2 ≤ 1 := by omega
        omega

/-- At any fixed finite stage `k`, every real eigenvalue of `powersModularOp lam k` (`0 < lam < 1`)
is bounded below by `lam ^ k`. -/
theorem stage_eigenvalue_ge_pow {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) {k : ℕ}
    {E : UHFStage k} (hE : E ≠ 0) {x : ℝ}
    (heig : powersModularOp lam k E = (x : ℂ) • E) :
    lam ^ k ≤ x := by
  have hij : ∃ i j : Fin (2 ^ k), E i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hE
    ext i j
    exact h i j
  rcases hij with ⟨i, j, hij_ne⟩
  rw [stage_eigenvalue_eq_zpow hlam0 hij_ne heig]
  have hpop : bitPopcount i.val ≤ k := bitPopcount_le_of_lt_twoPow i.isLt
  have hexp : (bitPopcount i.val : ℤ) - (bitPopcount j.val : ℤ) ≤ (k : ℤ) := by omega
  calc
    lam ^ k = lam ^ (k : ℤ) := (zpow_natCast lam k).symm
    _ ≤ lam ^ ((bitPopcount i.val : ℤ) - (bitPopcount j.val : ℤ)) :=
      (powersPointSpec_strictAnti hlam0 hlam1).antitone hexp

/-- For `0 < lam < 1`, `lam ^ (k + 1)` is never an eigenvalue of `powersModularOp lam k`,
demonstrating that no fixed finite stage captures the entire infinite point spectrum or its
accumulation point `0`. -/
theorem next_power_not_stage_eigenvalue {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (k : ℕ) :
    ¬ ∃ E : UHFStage k, E ≠ 0 ∧ powersModularOp lam k E = ((lam ^ (k + 1) : ℝ) : ℂ) • E := by
  rintro ⟨E, hE0, heig⟩
  have hge : lam ^ k ≤ lam ^ (k + 1) := stage_eigenvalue_ge_pow hlam0 hlam1 hE0 heig
  have hpos : 0 < lam ^ k := pow_pos hlam0 k
  have hlt : lam ^ (k + 1) < lam ^ k := by
    rw [pow_succ]
    exact mul_lt_of_lt_one_right hpos hlam1
  exact not_lt_of_ge hge hlt

/-- Every `UHFStage k` is finite-dimensional over `ℂ` (Type `I_{2^k}`), whereas a Type `III_λ`
factor is necessarily infinite-dimensional. -/
theorem uhfStage_finiteDimensional (k : ℕ) : FiniteDimensional ℂ (UHFStage k) :=
  inferInstance

/-- Normalized trace on the finite UHF matrix stage `UHFStage k`. -/
def uhfStageNormTrace (k : ℕ) (A : UHFStage k) : ℂ :=
  (1 / ((2 ^ k : ℕ) : ℂ)) * Matrix.trace A

/-- `uhfStageNormTrace k` is unital (`τ_k(1) = 1`) at every finite stage `k`. -/
theorem uhfStageNormTrace_one (k : ℕ) : uhfStageNormTrace k 1 = 1 := by
  unfold uhfStageNormTrace
  have htr : Matrix.trace (1 : UHFStage k) = ((2 ^ k : ℕ) : ℂ) := by
    simp [Matrix.trace, Matrix.diag]
  have hne : ((2 ^ k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.two_pow_pos k).ne'
  rw [htr, one_div_mul_cancel hne]

/-- `uhfStageNormTrace k` is tracial (`τ_k(A * B) = τ_k(B * A)`), contrasting with a Type `III`
factor which admits no finite tracial state. -/
theorem uhfStageNormTrace_comm (k : ℕ) (A B : UHFStage k) :
    uhfStageNormTrace k (A * B) = uhfStageNormTrace k (B * A) := by
  unfold uhfStageNormTrace
  rw [Matrix.trace_mul_comm A B]

/-- Every `RealBlockStage m k` is finite-dimensional over `ℝ`. -/
theorem realBlockStage_finiteDimensional (m k : ℕ) :
    FiniteDimensional ℝ (RealBlockStage m k) :=
  inferInstance

/-- Every element of the algebraic inductive colimit `RealBlockColimit m` factors through a
finite-dimensional real matrix stage `RealBlockStage m k`. -/
theorem realBlockColimit_factors_through_stage (m : ℕ) (x : RealBlockColimit m) :
    ∃ (k : ℕ) (X : RealBlockStage m k), x = toBlockColimit k X :=
  exists_toBlockColimit x

/-- Normalized trace functional on the Jaynesian inductive colimit `RealBlockColimit m`, defined
via the faithful normalized Hilbert–Schmidt inner product `colimitHSInner`. -/
def realBlockColimitNormTrace (m : ℕ) (x : RealBlockColimit m) : ℝ :=
  (1 / (m : ℝ)) * colimitHSInner 1 x

/-- For `m ≠ 0`, `realBlockColimitNormTrace m` is unital (`τ(1) = 1`). -/
theorem realBlockColimitNormTrace_one {m : ℕ} (hm : m ≠ 0) :
    realBlockColimitNormTrace m 1 = 1 := by
  change (1 / (m : ℝ)) * colimitHSInner (toBlockColimit 0 1) (toBlockColimit 0 1) = 1
  rw [colimitHSInner_toBlockColimit]
  unfold normHSInner InfoGeometry.Canonical.FiniteMatrixTomitaPolar.hsInner
  have htr :
      Matrix.trace (Matrix.transpose (1 : RealBlockStage m 0) * (1 : RealBlockStage m 0)) =
        (m : ℝ) := by
    simp [Matrix.trace, Matrix.diag]
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [htr]
  simp [hm_ne]

/-- `realBlockColimitNormTrace m` satisfies the tracial property `τ(x * y) = τ(y * x)` on
`RealBlockColimit m`. -/
theorem realBlockColimitNormTrace_mul_comm (m : ℕ) (x y : RealBlockColimit m) :
    realBlockColimitNormTrace m (x * y) = realBlockColimitNormTrace m (y * x) := by
  rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
  unfold realBlockColimitNormTrace
  rw [← toBlockColimit_one (m := m) k, mul_toBlockColimit, mul_toBlockColimit,
    colimitHSInner_toBlockColimit, colimitHSInner_toBlockColimit]
  unfold normHSInner InfoGeometry.Canonical.FiniteMatrixTomitaPolar.hsInner
  simp only [Matrix.transpose_one, one_mul]
  rw [Matrix.trace_mul_comm X Y]

/-- For `m ≠ 0`, `realBlockColimitNormTrace m` is faithful (`τ(star x * x) = 0 ↔ x = 0`),
certifying that `RealBlockColimit m` is a tracial real inductive colimit rather than a Type `III`
factor. -/
theorem realBlockColimitNormTrace_faithful {m : ℕ} (hm : m ≠ 0) (x : RealBlockColimit m) :
    realBlockColimitNormTrace m (star x * x) = 0 ↔ x = 0 := by
  rcases exists_toBlockColimit x with ⟨k, X, rfl⟩
  have hinner :
      colimitHSInner 1 (star (toBlockColimit k X) * toBlockColimit k X) =
        colimitHSInner (toBlockColimit k X) (toBlockColimit k X) := by
    rw [star_toBlockColimit, mul_toBlockColimit, ← toBlockColimit_one (m := m) k,
      colimitHSInner_toBlockColimit, colimitHSInner_toBlockColimit]
    unfold normHSInner InfoGeometry.Canonical.FiniteMatrixTomitaPolar.hsInner
    simp only [Matrix.transpose_one, one_mul]
    rfl
  have hm_pos : (0 : ℝ) < 1 / (m : ℝ) :=
    one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
  unfold realBlockColimitNormTrace
  rw [hinner, mul_eq_zero, or_iff_right hm_pos.ne', colimitHSInner_self_eq_zero_iff]

end InfoGeometry.Modular.PowersModularSpectrum
