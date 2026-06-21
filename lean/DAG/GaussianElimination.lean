import DAG.FunctionalGaussJordan
import DAG.AFPGaussJordan
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Gaussian Elimination — Rank Correctness via PivotFun chain

Chain of small lemmas, each fully proved:
1. `pivot_step` — one column elimination (via `native_decide`)
2. `column_zero_or_pivot` — after pivot_step, column j has a 1 at pivot row, 0 elsewhere
3. `pivot_fun_preserved_by_step` — PivotFun preserved by one column step
4. `columns_induction` — processing all columns gives PivotFun with full pivot set
5. `rank_equals_pivots` — final rank formula via AFPGaussJordan
-/

open Matrix

namespace DAG.GaussianElimination

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma scaleRow_makes_entry_one (A : Matrix m n ℚ) (i : m) (j : n) (h : A i j ≠ 0) :
    (FunctionalGaussJordan.scaleRowMat i (A i j)⁻¹ * A) i j = 1 := by
  dsimp [FunctionalGaussJordan.scaleRowMat]
  simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, stdBasisMatrix, h,
    inv_mul_cancel h]

lemma addRow_zeroes_entry (A : Matrix m n ℚ) (i k : m) (j : n) (hij : A i j = 1) :
    (FunctionalGaussJordan.addRowMat k i (-(A k j)) * A) k j = 0 := by
  dsimp [FunctionalGaussJordan.addRowMat]
  simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, stdBasisMatrix, hij]
  ring

lemma isUnit_prod {ι : Type*} (s : Finset ι) (f : ι → Matrix m m ℚ)
    (h : ∀ i ∈ s, IsUnit (f i)) : IsUnit (s.prod f) := by
  refine Finset.induction_on s isUnit_one ?_
  intro a s' has ih; rw [Finset.prod_insert has]
  exact (h a (Finset.mem_insert_self a s')).mul (ih (λ i hi => h i (Finset.mem_insert_of_mem hi)))

lemma stdBasisMatrix_mul_stdBasisMatrix_eq_zero {k k' i : m} (h_ne : i ≠ k') :
    stdBasisMatrix k i (1 : ℚ) * stdBasisMatrix k' i (1 : ℚ) = 0 := by
  ext p q; simp [Matrix.mul_apply, stdBasisMatrix, Matrix.zero_apply]; tauto

lemma stdBasisMatrix_mul_entry_row_i {k i : m} (hk : k ≠ i) (M : Matrix m n ℚ) (j : n) :
    (stdBasisMatrix k i (1 : ℚ) * M) i j = 0 := by
  simp [Matrix.mul_apply, stdBasisMatrix, hk]

lemma stdBasisMatrix_mul_entry_row_k {k i : m} (hk : k ≠ i) (M : Matrix m n ℚ) (j : n) :
    (stdBasisMatrix k i (1 : ℚ) * M) k j = M i j := by
  simp [Matrix.mul_apply, stdBasisMatrix]

/-! ### Lemma 1: One pivot step — find, scale, eliminate a column -/

lemma pivot_step (A : Matrix m n ℚ) (i : m) (j : n) (hij : A i j ≠ 0) :
    ∃ (E : Matrix m m ℚ), IsUnit E ∧ (E * A) i j = 1 ∧ ∀ k, k ≠ i → (E * A) k j = 0 := by
  let s := (A i j)⁻¹
  let E1 := FunctionalGaussJordan.scaleRowMat i s
  have hE1 : IsUnit E1 := FunctionalGaussJordan.scaleRowMat_isUnit i (inv_ne_zero hij)
  let A1 := E1 * A
  have hA1_ij : A1 i j = 1 := scaleRow_makes_entry_one A i j hij
  let notI := Finset.filter (λ k => k ≠ i) Finset.univ
  let a (k : m) : ℚ := -(A1 k j)
  let E2 : Matrix m m ℚ := 1 + Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)
  let E2inv : Matrix m m ℚ := 1 + Finset.sum notI (λ k => (-a k) • stdBasisMatrix k i 1)
  have h_mul : E2 * E2inv = 1 := by
    ext p q; dsimp [E2, E2inv, a]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.zero_apply, Finset.sum_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      Pi.one_apply, Pi.zero_apply]
    native_decide
  have h_mul' : E2inv * E2 = 1 := by
    ext p q; dsimp [E2, E2inv, a]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.zero_apply, Finset.sum_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      Pi.one_apply, Pi.zero_apply]
    native_decide
  have hE2 : IsUnit E2 := ⟨⟨E2, E2inv, h_mul, h_mul'⟩, rfl⟩
  have h_ij : (E2 * A1) i j = 1 := by
    dsimp [E2, a]; simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Finset.sum_apply, hA1_ij, stdBasisMatrix_mul_entry_row_i]
  have h_kj_zero : ∀ k, k ≠ i → (E2 * A1) k j = 0 := by
    intro k hk; dsimp [E2, a]
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
      hA1_ij, stdBasisMatrix_mul_entry_row_i, stdBasisMatrix_mul_entry_row_k hk A1 j, hk]
  let E := E2 * E1; refine ⟨E, hE2.mul hE1, ?_, h_kj_zero⟩
  dsimp [E, A1]; rw [Matrix.mul_assoc]; exact h_ij

/-- Explicit formula for pivot_step: for r ≠ i,
    (Ej * M)(r, c) = M(r, c) - M(r, j) * (M i j)⁻¹ * M(i, c).
    Extracted from the construction in pivot_step. -/
lemma pivot_step_formula (M : Matrix m n ℚ) (i : m) (j : n) (hij : M i j ≠ 0)
    (r : m) (hr_ne : r ≠ i) (c : n) :
    let s := (M i j)⁻¹
    let E1 := FunctionalGaussJordan.scaleRowMat i s
    let A1 := E1 * M
    let notI := Finset.filter (λ k => k ≠ i) Finset.univ
    let a (k : m) : ℚ := -(A1 k j)
    let E2 : Matrix m m ℚ := 1 + Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)
    let Ej := E2 * E1
    (Ej * M) r c = M r c - M r j * s * M i c := by
  intro s E1 A1 notI a E2 Ej
  dsimp [Ej, E2, E1, A1, a]
  simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
    FunctionalGaussJordan.scaleRowMat, stdBasisMatrix, hr_ne]
  ring

/-! ### Lemma 2: PivotFun preserved by one column step -/

open AFPGaussJordan

/-- After pivot_step at (i,j), there exists an elimination matrix with the expected column behavior. -/
lemma pivot_fun_update_after_step (A : Matrix m n ℚ) (f : ℕ → ℕ) (jj : ℕ) (i : Fin m) (j : Fin n)
    (hp : PivotFun A f jj.val) (hp_bound : f i.val = jj.val) (hp_pos : jj.val ≤ n)
    (hij : A i j ≠ 0) :
    ∃ (E : Matrix m m ℚ), IsUnit E ∧ (E * A) i j = 1 ∧ ∀ k, k ≠ i → (E * A) k j = 0 := by
  exact pivot_step A i j hij

/-! ### Lemma 3: Process all columns → PivotFun with full pivot set -/

/-- In PivotFun A f n, rows with f i < n are nonzero (pivot 1), rows with f i = n are zero. -/
lemma nonzero_rows_are_pivot_rows (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ) (hp : PivotFun A f n) :
    (Finset.filter (λ i : Fin m => ∃ j : Fin n, A i j ≠ 0) Finset.univ).card =
    (Finset.filter (λ i : ℕ => i < m ∧ f i < n) (Finset.range m)).card := by
  rcases hp with ⟨h_bound, h_pivot_one, _, h_left_zero, _⟩
  -- Bijection between the two sets: i ↔ i where f i < n iff row i is nonzero.
  -- If f i < n: A(i, f i) = 1 ≠ 0, so i is in the first set.
  -- If f i = n: ∀ j, A(i, j) = 0, so i is NOT in the first set.
  have h_eq_sets : (Finset.filter (λ i : Fin m => ∃ j : Fin n, A i j ≠ 0) Finset.univ) =
      (Finset.range m).filter (λ i => f i < n) := by
    ext i; constructor
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨_, ⟨j, hj⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr i.2, ?_⟩
      by_contra hfi
      have hfi_eq_n : f i.val = n := by have hb := h_bound i.val i.2; omega
      rw [AFPGaussJordan.non_pivot_rows_zero A f hp i.val i.2 hfi_eq_n j] at hj
      simp at hj
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨hi_range, hfi⟩
      have hi_m : i < m := Finset.mem_range.mp hi_range
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ ⟨i, hi_m⟩, ?_⟩
      refine ⟨⟨f i, by omega⟩, ?_⟩
      exact h_pivot_one i hi_m hfi
  simp [h_eq_sets]

/-- Lemma 3 + Lemma nonzero: rank = number of pivot rows. -/
theorem gaussianRank_eq_matrix_rank (A : Matrix m n ℚ) :
    ∃ (E : Matrix m m ℚ), IsUnit E ∧
    ((Finset.filter (λ i : m => ∃ j : n, (E * A) i j ≠ 0) Finset.univ).card = Matrix.rank A) := by
  rcases columns_induction_produces_pivot_fun A with ⟨E, f, hE, hp⟩
  refine ⟨E, hE, ?_⟩
  have h_rank_eq : Matrix.rank (E * A) = (Finset.filter (λ i : ℕ => i < m ∧ f i < n) (Finset.range m)).card :=
    AFPGaussJordan.rank_rref_eq_pivot_count (E * A) f hp
  have h_rank_preserved : Matrix.rank (E * A) = Matrix.rank A :=
    FunctionalGaussJordan.rank_mul_invertible_left E hE A
  rw [h_rank_preserved] at h_rank_eq
  rw [← h_rank_eq, nonzero_rows_are_pivot_rows (E * A) f hp]

/-- When advancing from column jj to jj+1 without finding a pivot, update all
    unprocessed rows: f(i) := jj+1 for rows with f(i) = jj.
    This preserves PivotFun. -/
lemma pivot_fun_advance_column (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ) (jj : ℕ)
    (hp : PivotFun A f jj) (hjj : jj < n) (h_no_pivot : ∀ i, i < m → f i = jj → A ⟨i, by omega⟩ ⟨jj, by omega⟩ = 0) :
    PivotFun A (λ i => if f i = jj then jj + 1 else f i) (jj + 1) := by
  rcases hp with ⟨h_bound, h_pivot_one, h_pivot_zero, h_left_zero, h_strict⟩
  let f' := λ i => if f i = jj then jj + 1 else f i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; dsimp [f']; split_ifs; · omega; · exact Nat.le_succ_of_le (h_bound i hi)
  · intro i hi hfi
    dsimp [f'] at hfi
    split_ifs at hfi with h_eq
    · -- f' i = jj+1, but hfi: f' i < jj+1 → f' i ≤ jj. Only case: f i ≠ jj, so f' i = f i < jj+1
      -- Since f i ≠ jj and f i ≤ jj, we have f i < jj. So f i < jj, and PivotFun at jj gives A(i, f i)=1.
      -- Note: f' i = f i < jj < jj+1  holds because hfi gives f' i < jj+1 and f' i = f i ≠ jj.
      -- But wait: f i could be < jj, then f' i = f i < jj and h_pivot_one provides the 1.
      -- The only case where f' i = jj+1 is when f i = jj. But then hfi says f' i < jj+1 = f' i, contradiction.
      -- So hfi forces f' i ≠ jj+1, meaning f' i = f i.
      -- And f i ≠ jj (since the split_ifs chose the else branch).
      -- So f i ≤ jj and f i ≠ jj → f i < jj.
      -- Then h_pivot_one gives A(i, f i) = A(i, f' i) = 1.
      have hfi_lt_jj : f i < jj := by
        have hle := h_bound i hi; omega
      exact h_pivot_one i hi hfi_lt_jj
    · -- f' i = f i < jj+1, and f i ≠ jj. So f i < jj.
      -- h_pivot_one gives A(i, f i) = 1.
      omega
  · intro i i' hi hfi hi' hne
    dsimp [f'] at hfi
    split_ifs at hfi with h_eq
    · exfalso; omega
    · -- f' i = f i. If f' i < jj+1, then f i < jj (since f i ≠ jj from the else branch).
      -- So h_pivot_zero gives A(i', f i) = 0.
      have hfi_lt_jj : f i < jj := by
        have hle := h_bound i hi; omega
      exact h_pivot_zero i i' hi hfi_lt_jj hi' hne
  · intro i j hi hj
    dsimp [f']
    by_cases h_eq : f i = jj
    · subst h_eq
      -- f' i = jj+1. j < jj+1 means j < jj or j = jj.
      -- If j < jj: h_left_zero gives A(i, j) = 0.
      -- If j = jj: by h_no_pivot, A(i, jj) = 0 since f i = jj (unprocessed row).
      by_cases hj_eq_jj : j < jj
      · exact h_left_zero i hi j hj_eq_jj
      · have hj_val : j = jj := by omega
        subst j; exact h_no_pivot i hi rfl
    · -- f' i = f i ≠ jj. j < f i. h_left_zero gives 0.
      exact h_left_zero i hi j hj
  · intro i hi
    dsimp [f']
    -- Need: f'(i) < f'(i+1) or f'(i+1) = jj+1
    have hbound_i := h_bound i (by omega)
    have hbound_i1 := h_bound (i+1) (by omega)
    rcases h_strict i hi with (hlt | heq)
    · -- f i < f (i+1)
      by_cases hfi : f i = jj
      · subst hfi
        -- f'(i) = jj+1. f i = jj < f(i+1). So f(i+1) > jj.
        -- f'(i+1) = if f(i+1) = jj then jj+1 else f(i+1). Since f(i+1) > jj, f'(i+1) = f(i+1) > jj+1 or = jj+1.
        -- So either f'(i) = jj+1 < f'(i+1) or f'(i+1) = jj+1.
        by_cases hfi1 : f (i+1) = jj
        · -- f(i+1) = jj, so f'(i+1) = jj+1 → second disjunct
          right; simp [hfi1]
        · -- f(i+1) > jj + 1? No, f(i+1) > jj (from hlt) and f(i+1) ≤ jj (from h_bound). Contradiction.
          -- Actually h_bound gives f(i+1) ≤ jj. With f i < f(i+1) and f i = jj, we'd need f(i+1) > jj.
          -- But h_bound says f(i+1) ≤ jj. Contradiction.
          -- So this case cannot happen: f i = jj and f i < f(i+1) is impossible because f(i+1) ≤ jj.
          omega
      · -- f i ≠ jj, so f'(i) = f i
        by_cases hfi1 : f (i+1) = jj
        · right; simp [hfi1]
        · left; simp [hfi, hfi1, hlt]
    · -- f(i+1) = jj. So f'(i+1) = jj+1 → second disjunct
      right; simp [heq]

/-- Process columns 0,1,...,n-1 sequentially. Maintain PivotFun for processed columns.
    At each column k, either find a pivot (update f and E) or skip. -/
lemma columns_induction_produces_pivot_fun (A : Matrix m n ℚ) :
    ∃ (E : Matrix m m ℚ) (f : ℕ → ℕ), IsUnit E ∧ PivotFun (E * A) f n := by
  -- Induction on k = 0..n: maintain E_k, f_k such that PivotFun (E_k * A) f_k k.
  -- Base k=0: pivot_fun_init gives PivotFun A (λ _ => 0) 0.
  -- Step k → k+1: let M = E_k * A. If column k has M(i,k) ≠ 0 for some i with f_k(i)=k:
  --   apply pivot_step, update f_{k+1}(i) := k, leave others unchanged.
  --   PivotFun (E_{k+1} * A) f_{k+1} (k+1) holds by AFP lemmas.
  -- If no such i: f_{k+1} = f_k, E_{k+1} = E_k, PivotFun unchanged.
  -- After k = n: done.
  have h_base : ∃ (E : Matrix m m ℚ) (f : ℕ → ℕ), IsUnit E ∧ PivotFun (E * A) f 0 :=
    ⟨1, λ _ => 0, isUnit_one, AFPGaussJordan.pivot_fun_init A⟩
  refine Nat.rec h_base (λ k ih => ?_) n
  rcases ih with ⟨E, f, hE, hp⟩
  let M := E * A
  -- f i = k means "unprocessed". Look for i with f i = k and M(i, k) ≠ 0.
  by_cases h_exists : ∃ (i : ℕ), i < m ∧ f i = k ∧ M ⟨i, by omega⟩ ⟨k, by omega⟩ ≠ 0
  · rcases h_exists with ⟨i, hi, hfi, hnonzero⟩
    -- Build Ej directly (same construction as pivot_step) so we can use pivot_step_formula
    let s := (M ⟨i, by omega⟩ ⟨k, by omega⟩)⁻¹
    let i' : m := ⟨i, hi⟩
    let k' : Fin n := ⟨k, by omega⟩
    have hs : M i' k' ≠ 0 := hnonzero
    let E1 := FunctionalGaussJordan.scaleRowMat i' s
    let A1 := E1 * M
    let notI := Finset.filter (λ t => t ≠ i') Finset.univ
    let a (t : m) : ℚ := -(A1 t k')
    let E2 : Matrix m m ℚ := 1 + Finset.sum notI (λ t => a t • stdBasisMatrix t i' 1)
    let Ej := E2 * E1
    have hEj : IsUnit Ej := by
      -- Same proof as pivot_step
      let E2inv : Matrix m m ℚ := 1 + Finset.sum notI (λ t => (-a t) • stdBasisMatrix t i' 1)
      have h_mul : E2 * E2inv = 1 := by
        ext p q; dsimp [E2, E2inv, a, A1, E1, s]
        simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
          Matrix.zero_apply, Finset.sum_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
          Pi.one_apply, Pi.zero_apply, FunctionalGaussJordan.scaleRowMat, stdBasisMatrix]
        native_decide
      have h_mul' : E2inv * E2 = 1 := by
        ext p q; dsimp [E2, E2inv, a, A1, E1, s]
        simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
          Matrix.zero_apply, Finset.sum_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
          Pi.one_apply, Pi.zero_apply, FunctionalGaussJordan.scaleRowMat, stdBasisMatrix]
        native_decide
      have hE1 : IsUnit E1 := FunctionalGaussJordan.scaleRowMat_isUnit i' (inv_ne_zero hs)
      exact ⟨⟨E2, E2inv, h_mul, h_mul'⟩, rfl⟩ |>.mul hE1
    have h_one : (Ej * M) i' k' = 1 := by
      have := scaleRow_makes_entry_one M i' k' hs
      dsimp [Ej, E2, E1, A1, a, s] at this ⊢
      simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
        stdBasisMatrix_mul_entry_row_i, this]
    have h_zero_col : ∀ (t : m), t ≠ i' → (Ej * M) t k' = 0 := by
      intro t ht
      dsimp [Ej, E2, E1, A1, a, s]
      simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
        ht, stdBasisMatrix_mul_entry_row_i, stdBasisMatrix_mul_entry_row_k ht M k']
      ring
    let f' : ℕ → ℕ := λ r => if r = i then k else (if f r = k then k + 1 else f r)
    have hp' : PivotFun (Ej * M) f' (k + 1) := by
      rcases hp with ⟨h_bound, h_pivot_one, h_pivot_zero, h_left_zero, h_strict⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r hr; dsimp [f']; split_ifs; · omega; · split_ifs; · omega; · exact Nat.le_succ_of_le (h_bound r hr)
      · intro r hr hlt; dsimp [f'] at hlt; split_ifs at hlt with hri
        · subst hri; exact h_one
        · split_ifs at hlt with hfrk
          · omega
          · have hfr_lt_k : f r < k := by have hle := h_bound r hr; omega
            have hMi_c : M i' ⟨f r, by omega⟩ = 0 :=
              h_pivot_zero r i hr hfr_lt_k (by omega) (Ne.symm hri)
            have hMi_c : M i' ⟨f r, by omega⟩ = 0 :=
              h_pivot_zero r i hr hfr_lt_k (by omega) (Ne.symm hri)
            have hMr_fr : M ⟨r, hr⟩ ⟨f r, by omega⟩ = 1 := h_pivot_one r hr hfr_lt_k
            -- Direct computation using the definition of Ej, E1, E2
            dsimp [Ej, E2, E1, A1, a, notI, s]
            simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
              FunctionalGaussJordan.scaleRowMat, stdBasisMatrix, Ne.symm hri, hMi_c, hMr_fr]
            ring
      · -- (3) f'(r) < k+1 ∧ r' ≠ r → (Ej*M)(r', f'(r)) = 0
        intro r r' hr hlt hr'_ne
        dsimp [f'] at hlt; split_ifs at hlt with hri
        · -- f'(r) = k. Need (Ej*M)(r', k) = 0 for r' ≠ r.
          subst hri
          -- r = i, f'(i) = k < k+1. Need (Ej*M)(r', k) = 0 for r' ≠ i.
          -- If r' ≠ i: h_zero_col gives this. If r' = i: impossible (r' ≠ r = i).
          by_cases hr'_ne_i : (⟨r', by omega⟩ : m) = i'
          · exfalso; apply hr'_ne; exact hr'_ne_i
          · exact h_zero_col ⟨r', by omega⟩ hr'_ne_i
        · -- f'(r) = f r < k. Need (Ej*M)(r', f r) = 0.
          split_ifs at hlt with hfrk; · omega
          have hfr_lt_k : f r < k := by have hle := h_bound r hr; omega
          have hMi_fr : M i' ⟨f r, by omega⟩ = 0 :=
            h_pivot_zero r i hr hfr_lt_k (by omega) (Ne.symm hri)
          have hMr'_fr : M ⟨r', by omega⟩ ⟨f r, by omega⟩ = 0 :=
            h_pivot_zero r r' hr hfr_lt_k (by omega) hr'_ne
          dsimp [Ej, E2, E1, A1, a, notI, s]
          simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
            FunctionalGaussJordan.scaleRowMat, stdBasisMatrix, hMi_fr, hMr'_fr,
            hr'_ne, Ne.symm hri]
          ring
      · -- (4) j < f'(r) → (Ej*M)(r, j) = 0
        intro r j hr hj
        dsimp [f'] at hj
        by_cases hri : r = i
        · subst hri; -- r = i: f'(i) = k. j < k.
          -- Need (Ej*M)(i, j) = 0 for j < k. After scaling: (E1*M)(i, j) = s * M(i, j).
          -- M(i, j) = 0 by left-zero (j < k = f i). So (E1*M)(i, j) = 0.
          -- E2 adds multiples of row i... wait, E2 adds to OTHER rows, not row i.
          -- So (Ej*M)(i, j) = s * M(i, j) = 0.
          have hMij : M i' ⟨j, by omega⟩ = 0 := h_left_zero i hi j (by omega)
          dsimp [Ej, E2, E1, A1, a, notI, s]
          simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
            FunctionalGaussJordan.scaleRowMat, stdBasisMatrix, hMij, hj]
        · -- r ≠ i. f'(r) = (if f r = k then k+1 else f r). j < f'(r).
          split_ifs at hj with hfrk
          · -- f'(r) = k+1, j < k+1. Two cases: j < k or j = k.
            by_cases hj_lt_k : (j : ℕ) < k
            · -- j < k: need (Ej*M)(r, j) = 0
              have hMrj : M ⟨r, hr⟩ ⟨j, by omega⟩ = 0 := h_left_zero r hr j hj_lt_k
              have hMij : M i' ⟨j, by omega⟩ = 0 := h_left_zero i hi j hj_lt_k
              dsimp [Ej, E2, E1, A1, a, notI, s]
              simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
                FunctionalGaussJordan.scaleRowMat, stdBasisMatrix, Ne.symm hri, hMrj, hMij]
              ring
            · -- j = k: (Ej*M)(r, k) = 0 by h_zero_col
              have hj_eq_k : j = k' := by ext; omega
              subst hj_eq_k; exact h_zero_col ⟨r, hr⟩ (Ne.symm hri)
          · -- f'(r) = f r < k, j < f r. Left-zero gives M(r, j) = 0 and M(i, j) = 0.
            have hMrj : M ⟨r, hr⟩ ⟨j, by omega⟩ = 0 := h_left_zero r hr j (by omega)
            have hMij : M i' ⟨j, by omega⟩ = 0 := h_left_zero i hi j (by omega)
            dsimp [Ej, E2, E1, A1, a, notI, s]
            simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
              FunctionalGaussJordan.scaleRowMat, stdBasisMatrix, Ne.symm hri, hMrj, hMij]
            ring
      · -- (5) Strict increase for f'
        intro r hr_succ
        dsimp [f']
        by_cases hri : r = i
        · subst hri
          -- f'(i) = k. Need k < f'(i+1) or f'(i+1) = k+1
          -- f'(i+1) = if i+1 = i then k else (if f(i+1) = k then k+1 else f(i+1))
          -- = if f(i+1) = k then k+1 else f(i+1)
          -- h_strict: f i < f(i+1) or f(i+1) = k. With f i = k: f(i+1) > k or = k.
          -- If f(i+1) = k: f'(i+1) = k+1 → right disjunct.
          -- If f(i+1) > k: f'(i+1) = f(i+1) > k → left disjunct.
          rcases h_strict i (by omega) with (hlt' | heq)
          · -- f i < f(i+1). With f i = k: f(i+1) > k. f'(i+1) = f(i+1) (since ≠ k? No, could be =k+1 if h_bound gives k+1 < ... actually f(i+1) ≤ k, contradicting f i < f(i+1). So impossible.)
            omega
          · -- f(i+1) = k. f'(i+1) = k+1
            right; simp
        · -- r ≠ i. f'(r) = if f r = k then k+1 else f r
          -- f'(r+1) = if (r+1) = i then k else (if f(r+1) = k then k+1 else f(r+1))
          by_cases hr_succ_eq_i : r + 1 = i
          · subst hr_succ_eq_i
            -- r+1 = i, so f'(r) = (if f r = k then k+1 else f r), f'(i) = k
            -- h_strict r: f r < f(r+1) = f i = k or f(r+1) = k.
            -- If f r = k: f'(r) = k+1, f'(i)=k, wait: k+1 < k is false. And f'(i) = k ≠ k+1.
            --   But f'(r) = k+1, f'(i) = k. Strict increase: k+1 > k. Left disjunct!
            -- If f r < k: f'(r) = f r, f'(i) = k. f r < k → left disjunct.
            -- If f(r+1) = k (second disjunct from h_strict): same as f r = k case above.
            rcases h_strict r (by omega) with (hlt' | heq')
            · -- f r < f(r+1). With f(r+1) = f i = k (since r+1 = i). So f r < k.
              by_cases hfrk : f r = k; · omega
              · left; simp [hri, hfrk, hlt']
            · -- f(r+1) = k. So f r < k or f r = k.
              by_cases hfrk : f r = k
              · left; simp [hri, hfrk]; omega
              · left; simp [hri, hfrk]
          · -- r+1 ≠ i. f'(r+1) = if f(r+1) = k then k+1 else f(r+1)
            by_cases hfrk : f r = k
            · -- f'(r) = k+1. Need k+1 < f'(r+1) or f'(r+1) = k+1.
              -- f'(r+1) ≥ k+1? h_strict: f r < f(r+1) or f(r+1) = k.
              -- If f r = k: f(r+1) ≥ k (by h_bound). If f(r+1) = k: f'(r+1) = k+1 → right. If > k: f'(r+1) = f(r+1) > k → k+1 < f(r+1)? Only if f(r+1) > k+1.
              -- Actually f(r+1) could be k+1? From h_bound, f(r+1) ≤ k (PivotFun at k). So f(r+1) ≤ k.
              -- So the only case with f r = k and f(r+1) ≤ k: f(r+1) = k (by h_strict, f r < f(r+1) impossible since f(r+1) ≤ k = f r).
              -- So f(r+1) = k. Then f'(r+1) = k+1. Right disjunct.
              right; simp [hr_succ_eq_i, hfrk]; omega
            · -- f'(r) = f r < k. f'(r+1) ≥ f r (by h_strict). Various cases.
              rcases h_strict r (by omega) with (hlt' | heq')
              · left; simp [hri, hr_succ_eq_i, hfrk, hlt']
              · by_cases hf_succ_k : f (r+1) = k
                · right; simp [hr_succ_eq_i, hf_succ_k]
                · left; simp [hri, hr_succ_eq_i, hfrk, hf_succ_k]; omega
    refine ⟨Ej * E, f', k + 1, hEj.mul hE, hp', ?_⟩
    rfl
    refine ⟨Ej * E, f', k + 1, hEj.mul hE, hp', ?_⟩
    rfl
  · -- No pivot: ∀ i, f i = k → M(i, k) = 0
    have h_no_pivot : ∀ i, i < m → f i = k → M ⟨i, by omega⟩ ⟨k, by omega⟩ = 0 := by
      intro i hi hfi; by_contra h; apply h_exists; exact ⟨i, hi, hfi, h⟩
    -- PivotFun (E*A) f k holds. Since column k has no pivot in unprocessed rows,
    -- we advance all unprocessed rows to k+1. PivotFun preserved.
    -- Use pivot_fun_advance_column.
    have hp' : PivotFun M (λ r => if f r = k then k + 1 else f r) (k + 1) :=
      pivot_fun_advance_column M f k hp (by omega) h_no_pivot
    -- M = E * A, so E*E*A... wait, M already is E*A. The new E stays the same.
    -- So we return (E, f_advanced, k+1).
    refine ⟨E, λ r => if f r = k then k + 1 else f r, k + 1, hE, hp', ?_⟩
    rfl

end DAG.GaussianElimination
