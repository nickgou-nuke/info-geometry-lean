import Mathlib

namespace InfoGeometry.Physics

def stationaryEdgeCurrent {n : Type*}
    (π : n → ℝ) (q : n → n → ℝ) (i j : n) : ℝ :=
  π i * q i j - π j * q j i

noncomputable def weightedAdjoint {n : Type*}
    (π : n → ℝ) (L : n → n → ℝ) (i j : n) : ℝ :=
  (π i)⁻¹ * L j i * π j

theorem weightedAdjoint_involutive {n : Type*}
    (π : n → ℝ) (L : n → n → ℝ)
    (hπ : ∀ i, π i ≠ 0) (i j : n) :
    weightedAdjoint π (weightedAdjoint π L) i j = L i j := by
  simp only [weightedAdjoint]
  field_simp [hπ i, hπ j]

theorem weightedAdjoint_add {n : Type*}
    (π : n → ℝ) (L M : n → n → ℝ) (i j : n) :
    weightedAdjoint π (fun a b => L a b + M a b) i j =
      weightedAdjoint π L i j + weightedAdjoint π M i j := by
  simp only [weightedAdjoint]
  ring

theorem weightedAdjoint_neg {n : Type*}
    (π : n → ℝ) (L : n → n → ℝ) (i j : n) :
    weightedAdjoint π (fun a b => -L a b) i j =
      -weightedAdjoint π L i j := by
  simp only [weightedAdjoint]
  ring

theorem weightedAdjoint_smul {n : Type*}
    (π : n → ℝ) (c : ℝ) (L : n → n → ℝ) (i j : n) :
    weightedAdjoint π (fun a b => c * L a b) i j =
      c * weightedAdjoint π L i j := by
  simp only [weightedAdjoint]
  ring

theorem weightedAdjoint_eq_self_iff_detailedBalance {n : Type*}
    (π : n → ℝ) (q : n → n → ℝ)
    (hπ : ∀ i, π i ≠ 0) :
    (∀ i j, weightedAdjoint π q i j = q i j) ↔
      ∀ i j, π i * q i j = π j * q j i := by
  constructor
  · intro h i j
    have hij := h i j
    dsimp [weightedAdjoint] at hij
    field_simp [hπ i] at hij
    linarith
  · intro h i j
    dsimp [weightedAdjoint]
    field_simp [hπ i]
    nlinarith [h i j]

noncomputable def weightedSelfPart {n : Type*}
    (π : n → ℝ) (L : n → n → ℝ) (i j : n) : ℝ :=
  (1 / 2 : ℝ) * (L i j + weightedAdjoint π L i j)

noncomputable def weightedSkewPart {n : Type*}
    (π : n → ℝ) (L : n → n → ℝ) (i j : n) : ℝ :=
  (1 / 2 : ℝ) * (L i j - weightedAdjoint π L i j)

theorem weightedSelfPart_add_weightedSkewPart {n : Type*}
    (π : n → ℝ) (L : n → n → ℝ) (i j : n) :
    weightedSelfPart π L i j + weightedSkewPart π L i j = L i j := by
  simp only [weightedSelfPart, weightedSkewPart]
  ring

theorem weightedSelfPart_self_adjoint {n : Type*}
    (π : n → ℝ) (L : n → n → ℝ)
    (hπ : ∀ i, π i ≠ 0) (i j : n) :
    weightedAdjoint π (weightedSelfPart π L) i j =
      weightedSelfPart π L i j := by
  simp only [weightedSelfPart, weightedAdjoint]
  have h := weightedAdjoint_involutive π L hπ i j
  dsimp [weightedAdjoint] at h ⊢
  field_simp [hπ i, hπ j] at h ⊢
  nlinarith

theorem weightedSkewPart_skew_adjoint {n : Type*}
    (π : n → ℝ) (L : n → n → ℝ)
    (hπ : ∀ i, π i ≠ 0) (i j : n) :
    weightedAdjoint π (weightedSkewPart π L) i j =
      -weightedSkewPart π L i j := by
  simp only [weightedSkewPart, weightedAdjoint]
  have h := weightedAdjoint_involutive π L hπ i j
  dsimp [weightedAdjoint] at h ⊢
  field_simp [hπ i, hπ j] at h ⊢
  nlinarith

theorem weightedSkewPart_eq_zero_iff_detailedBalance {n : Type*}
    (π : n → ℝ) (q : n → n → ℝ)
    (hπ : ∀ i, π i ≠ 0) :
    (∀ i j, weightedSkewPart π q i j = 0) ↔
      ∀ i j, π i * q i j = π j * q j i := by
  constructor
  · intro h i j
    have hzero := h i j
    dsimp [weightedSkewPart] at hzero
    dsimp [weightedAdjoint] at hzero
    field_simp [hπ i] at hzero
    nlinarith
  · intro h i j
    dsimp [weightedSkewPart]
    dsimp [weightedAdjoint]
    field_simp [hπ i]
    nlinarith [h i j]

theorem stationaryEdgeCurrent_eq_two_mul_weightedSkewPart {n : Type*}
    (π : n → ℝ) (q : n → n → ℝ)
    (hπ : ∀ i, π i ≠ 0) (i j : n) :
    stationaryEdgeCurrent π q i j =
      2 * π i * weightedSkewPart π q i j := by
  dsimp [stationaryEdgeCurrent, weightedSkewPart, weightedAdjoint]
  field_simp [hπ i]

theorem stationaryEdgeCurrent_swap {n : Type*}
    (π : n → ℝ) (q : n → n → ℝ) (i j : n) :
    stationaryEdgeCurrent π q j i =
      -stationaryEdgeCurrent π q i j := by
  simp [stationaryEdgeCurrent]

theorem stationaryEdgeCurrent_total_sum_zero {n : Type*} [Fintype n]
    (π : n → ℝ) (q : n → n → ℝ) :
    ∑ i, ∑ j, stationaryEdgeCurrent π q i j = 0 := by
  simp only [stationaryEdgeCurrent, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  ring

theorem stationaryEdgeCurrent_self {n : Type*}
    (π : n → ℝ) (q : n → n → ℝ) (i : n) :
    stationaryEdgeCurrent π q i i = 0 := by
  simp [stationaryEdgeCurrent]

theorem stationaryEdgeCurrent_eq_zero_iff {n : Type*}
    (π : n → ℝ) (q : n → n → ℝ) (i j : n) :
    stationaryEdgeCurrent π q i j = 0 ↔
      π i * q i j = π j * q j i := by
  simp only [stationaryEdgeCurrent]
  constructor <;> intro h
  · linarith
  · linarith

theorem pairwise_detailedBalance_iff_zero_current {n : Type*}
    (π : n → ℝ) (q : n → n → ℝ) :
    (∀ i j, stationaryEdgeCurrent π q i j = 0) ↔
      ∀ i j, π i * q i j = π j * q j i := by
  constructor
  · intro h i j
    exact (stationaryEdgeCurrent_eq_zero_iff π q i j).mp (h i j)
  · intro h i j
    exact (stationaryEdgeCurrent_eq_zero_iff π q i j).mpr (h i j)

theorem sub_mul_log_div_nonneg
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * Real.log (a / b) := by
  rcases le_total b a with hba | hab
  · have hratio : 1 ≤ a / b := by
      rw [le_div_iff₀ hb]
      linarith
    exact mul_nonneg (sub_nonneg.mpr hba) (Real.log_nonneg hratio)
  · have hratio : a / b ≤ 1 := by
      rw [div_le_iff₀ hb]
      simpa using hab
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hab)
      (Real.log_nonpos (le_of_lt (div_pos ha hb)) hratio)

theorem sub_mul_log_div_eq_zero_iff
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) * Real.log (a / b) = 0 ↔ a = b := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hab | hlog
    · linarith
    · have hratio_pos : 0 < a / b := div_pos ha hb
      have hratio_one : a / b = 1 :=
        Real.eq_one_of_pos_of_log_eq_zero hratio_pos hlog
      exact (div_eq_one_iff_eq hb.ne').mp hratio_one
  · intro hab
    subst hab
    simp

noncomputable def stationaryEntropyProduction {n : Type*} [Fintype n]
    (π : n → ℝ) (q : n → n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j,
    stationaryEdgeCurrent π q i j *
      Real.log ((π i * q i j) / (π j * q j i))

theorem stationaryEntropyProduction_nonneg
    {n : Type*} [Fintype n]
    (π : n → ℝ) (q : n → n → ℝ)
    (hπ : ∀ i, 0 < π i) (hq : ∀ i j, 0 < q i j) :
    0 ≤ stationaryEntropyProduction π q := by
  unfold stationaryEntropyProduction
  have hterm : ∀ i j,
      0 ≤ stationaryEdgeCurrent π q i j *
        Real.log ((π i * q i j) / (π j * q j i)) := by
    intro i j
    simpa [stationaryEdgeCurrent, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using
      (sub_mul_log_div_nonneg
        (mul_pos (hπ i) (hq i j))
        (mul_pos (hπ j) (hq j i)))
  have hsum : 0 ≤ ∑ i, ∑ j,
      stationaryEdgeCurrent π q i j *
        Real.log ((π i * q i j) / (π j * q j i)) := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hterm i j
  positivity

theorem stationaryEntropyProduction_eq_zero_iff_detailedBalance
    {n : Type*} [Fintype n]
    (π : n → ℝ) (q : n → n → ℝ)
    (hπ : ∀ i, 0 < π i) (hq : ∀ i j, 0 < q i j) :
    stationaryEntropyProduction π q = 0 ↔
      ∀ i j, π i * q i j = π j * q j i := by
  have hterm : ∀ i j,
      0 ≤ stationaryEdgeCurrent π q i j *
        Real.log ((π i * q i j) / (π j * q j i)) := by
    intro i j
    simpa [stationaryEdgeCurrent, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using
      (sub_mul_log_div_nonneg
        (mul_pos (hπ i) (hq i j))
        (mul_pos (hπ j) (hq j i)))
  constructor
  · intro hzero
    have hsum : ∑ i, ∑ j,
        stationaryEdgeCurrent π q i j *
          Real.log ((π i * q i j) / (π j * q j i)) = 0 := by
      unfold stationaryEntropyProduction at hzero
      nlinarith
    have houter : ∀ i, ∑ j,
        stationaryEdgeCurrent π q i j *
          Real.log ((π i * q i j) / (π j * q j i)) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        Finset.sum_nonneg fun j _ => hterm i j)).mp hsum
      simpa using this
    intro i j
    have hinner := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j)).mp
      (houter i) j (Finset.mem_univ j)
    apply (sub_mul_log_div_eq_zero_iff
      (mul_pos (hπ i) (hq i j))
      (mul_pos (hπ j) (hq j i))).mp
    simpa [stationaryEdgeCurrent] using hinner
  · intro hbal
    unfold stationaryEntropyProduction
    have hzero : ∀ i j,
        stationaryEdgeCurrent π q i j *
          Real.log ((π i * q i j) / (π j * q j i)) = 0 := by
      intro i j
      apply (sub_mul_log_div_eq_zero_iff
        (mul_pos (hπ i) (hq i j))
        (mul_pos (hπ j) (hq j i))).mpr
      simpa [stationaryEdgeCurrent] using hbal i j
    simp [hzero]

theorem stationaryEntropyProduction_eq_zero_iff_pairwise_zero_current
    {n : Type*} [Fintype n]
    (π : n → ℝ) (q : n → n → ℝ)
    (hπ : ∀ i, 0 < π i) (hq : ∀ i j, 0 < q i j) :
    stationaryEntropyProduction π q = 0 ↔
      ∀ i j, stationaryEdgeCurrent π q i j = 0 := by
  rw [stationaryEntropyProduction_eq_zero_iff_detailedBalance π q hπ hq]
  exact (pairwise_detailedBalance_iff_zero_current π q).symm

theorem stationaryEntropyProduction_pos_iff_exists_nonzero_current
    {n : Type*} [Fintype n]
    (π : n → ℝ) (q : n → n → ℝ)
    (hπ : ∀ i, 0 < π i) (hq : ∀ i j, 0 < q i j) :
    0 < stationaryEntropyProduction π q ↔
      ∃ i j, stationaryEdgeCurrent π q i j ≠ 0 := by
  constructor
  · intro hpos
    by_contra hnone
    push_neg at hnone
    have hzero : stationaryEntropyProduction π q = 0 :=
      (stationaryEntropyProduction_eq_zero_iff_pairwise_zero_current π q hπ hq).2 hnone
    linarith
  · rintro ⟨i, j, hcurrent⟩
    have hnonneg : 0 ≤ stationaryEntropyProduction π q :=
      stationaryEntropyProduction_nonneg π q hπ hq
    have hne : stationaryEntropyProduction π q ≠ 0 := by
      intro hzero
      have hcurrents :=
        (stationaryEntropyProduction_eq_zero_iff_pairwise_zero_current π q hπ hq).1
          hzero
      exact hcurrent (hcurrents i j)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

def ouCirculationMatrix {n : Type*} [Fintype n]
    (M C D : Matrix n n ℝ) : Matrix n n ℝ :=
  M * C + D

theorem ouCirculationMatrix_transpose_eq_neg
    {n : Type*} [Fintype n]
    (M C D : Matrix n n ℝ)
    (hLyap : M * C + C * M.transpose + 2 • D = 0)
    (hC : C.transpose = C)
    (hD : D.transpose = D) :
    (ouCirculationMatrix M C D).transpose =
      -ouCirculationMatrix M C D := by
  ext i j
  have h := congrFun (congrFun hLyap i) j
  simp only [ouCirculationMatrix, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.neg_apply] at h ⊢
  have hDij : D i j = D j i := by
    have := congrFun (congrFun hD i) j
    simpa [Matrix.transpose_apply] using this.symm
  have hmul : (C * M.transpose) i j = (M * C) j i := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hCik : C i k = C k i := by
      have := congrFun (congrFun hC i) k
      simpa [Matrix.transpose_apply] using this.symm
    rw [hCik]
    ring
  rw [hmul] at h
  have h' := h
  norm_num at h'
  rw [hDij] at h'
  nlinarith

end InfoGeometry.Physics
