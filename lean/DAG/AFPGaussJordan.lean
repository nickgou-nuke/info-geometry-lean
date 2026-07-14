import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# AFP Gauss-Jordan — Small lemmas, each proved

Strategy: break the rank theorem into small, self-contained lemmas
and prove each one directly.
-/

open Matrix

namespace DAG.AFPGaussJordan

variable {m n : ℕ}

def multrow (i0 : ℕ) (a : ℚ) (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℚ :=
  λ r c => if r.val = i0 then a * A r c else A r c

def swaprows (l k : Fin m) (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℚ :=
  λ r c => if r = l then A k c else if r = k then A l c else A r c

def PivotFun (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ) (jj : ℕ) : Prop :=
  ∃ h_jj : jj ≤ n,
    (∀ i, i < m → f i ≤ jj) ∧
    (∀ i (hi : i < m) (hfi : f i < jj), A ⟨i, hi⟩ ⟨f i, by omega⟩ = 1) ∧
    (∀ i i' (hi : i < m) (hfi : f i < jj) (hi' : i' < m), i' ≠ i →
      A ⟨i', hi'⟩ ⟨f i, by omega⟩ = 0) ∧
    (∀ i (hi : i < m) (hfi : f i ≤ jj) j (hj : j < f i),
      A ⟨i, hi⟩ ⟨j, by omega⟩ = 0) ∧
    (∀ i, i + 1 < m → f i < f (i + 1) ∨ f (i + 1) = jj)

-- Lemma 1: non-pivot rows are all zeros
lemma non_pivot_rows_zero (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ)
    (hp : PivotFun A f n) (i : ℕ) (hi : i < m) (hfi : f i = n) (j : Fin n) :
    A ⟨i, hi⟩ j = 0 := by
  rcases hp with ⟨_, _, _, _, h_left_zero, _⟩
  have hj_lt_n : j.val < n := j.2
  have hj_lt_fi : j.val < f i := by rw [hfi]; exact hj_lt_n
  exact h_left_zero i hi (by simpa [hfi] using (hp.2.1 i hi)) j.val hj_lt_fi

-- Lemma 2: each pivot column f(i) of A is a standard basis vector e_i
lemma pivot_column_is_std_basis (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ)
    (hp : PivotFun A f n) (i : ℕ) (hi : i < m) (hfi : f i < n) :
    A ⟨i, hi⟩ ⟨f i, by omega⟩ = 1 ∧ ∀ (k : ℕ) (hk : k < m), k ≠ i →
      A ⟨k, hk⟩ ⟨f i, by omega⟩ = 0 := by
  rcases hp with ⟨_, _, h_pivot_one, h_pivot_zero, _, _⟩
  exact ⟨h_pivot_one i hi hfi, λ k hk hne => h_pivot_zero i k hi hfi hk hne⟩

-- Lemma 3: pivot rows of Aᵀ are standard basis vectors
lemma pivot_rows_transpose_are_std_basis (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ)
    (hp : PivotFun A f n) (i : ℕ) (hi : i < m) (hfi : f i < n) :
    (Aᵀ ⟨f i, by omega⟩) = (Pi.basisFun ℚ (Fin m)) ⟨i, hi⟩ := by
  ext k
  rcases pivot_column_is_std_basis A f hp i hi hfi with ⟨h_one, h_zero⟩
  classical
  by_cases hki : k.val = i
  · have hk : k = ⟨i, hi⟩ := Fin.ext hki
    subst hk
    simp [h_one]
  · have hz := h_zero k.val k.2 hki
    have hneq : k ≠ ⟨i, hi⟩ := by
      intro hk
      apply hki
      exact congrArg Fin.val hk
    simp [Pi.single_apply, hz, hneq]

-- Lemma 4: pivot rows of A (the vectors A⟨i,·⟩ for i ∈ P) as a Finset
def pivotRows (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ) : Finset (Fin n → ℚ) :=
  (Finset.filter (λ i : Fin m => f i.val < n) Finset.univ).image A

-- Helper: row i of A as a vector in Fin n → ℚ
def rowVec (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) : Fin n → ℚ := A i

-- The Finset of pivot rows (as vectors)
def pivotRowVecs (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ) : Finset (Fin n → ℚ) :=
  (Finset.filter (λ i : Fin m => (f i.val) < n) Finset.univ).image (rowVec A)

-- Lemma: non-pivot rows are zero (→ they contribute nothing to the row span)
lemma non_pivot_rows_zero' (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ)
    (hp : PivotFun A f n) (i : Fin m) (hfi : f i.val = n) : rowVec A i = 0 := by
  ext j; exact non_pivot_rows_zero A f hp i.val i.2 hfi j

-- Lemma 6: rank(Aᵀ) ≤ |P| because row space = span of pivot rows
lemma rank_transpose_le_pivot_card (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ)
    (hp : PivotFun A f n) : Matrix.rank Aᵀ ≤ (pivotRowVecs A f).card := by
  -- Matrix.rank Aᵀ = finrank(range(Aᵀ.mulVecLin)) = finrank(span of columns of Aᵀ)
  -- = finrank(span of rows of A) = finrank(Submodule.span (Set.range (rowVec A)))
  -- Since non-pivot rows are zero, the span = Submodule.span (pivotRowVecs A f)
  -- Hence: rank(Aᵀ) = finrank(span(pivotRows)) ≤ |pivotRows| by finrank_span_finset_le_card
  let rows := pivotRowVecs A f
  have h_span_eq : Submodule.span ℚ (Set.range (rowVec A)) = Submodule.span ℚ (rows : Set (Fin n → ℚ)) := by
    apply le_antisymm
    · -- Every row is either in rows (pivot) or zero → in span
      apply Submodule.span_le.mpr
      intro v hv
      rcases Set.mem_range.mp hv with ⟨i, rfl⟩
      by_cases hfi : f i.val < n
      · apply Submodule.subset_span
        dsimp [pivotRowVecs]
        change rowVec A i ∈ rows
        apply Finset.mem_image.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hfi⟩, rfl⟩
      · have hfi_eq_n : f i.val = n := by
          have h_bound := hp.2.1 i.val i.2; omega
        rw [non_pivot_rows_zero' A f hp i hfi_eq_n]
        exact Submodule.zero_mem _
    · -- rows ⊆ all rows, so span(rows) ⊆ span(all rows)
      exact Submodule.span_mono (λ v hv => by
        change v ∈ rows at hv
        rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
        exact Set.mem_range_self i)
  -- rank(Aᵀ) = finrank(range(Aᵀ.mulVecLin)) = finrank(column space of Aᵀ)
  -- = finrank(row space of A) = finrank(Submodule.span (Set.range (rowVec A)))
  -- Hmm, need to connect Matrix.rank to finrank(Submodule.span ...)
  -- Matrix.rank Aᵀ = Module.finrank ℚ (Aᵀ.mulVecLin.range)
  -- Aᵀ.mulVecLin.range = Submodule.span ℚ (Set.range (λ i : Fin m => Aᵀ i))
  -- But Aᵀ i = λ j => A j i = column i of A... that's columns, not rows
  -- Wait: Aᵀ : Matrix (Fin n) (Fin m) ℚ. Aᵀ.mulVecLin : (Fin m → ℚ) → (Fin n → ℚ)
  -- Aᵀ.mulVecLin x = Aᵀ * x. Range = span of columns of Aᵀ = span of rows of A.
  -- Because column j of Aᵀ = row j of A (as a function from Fin m to ℚ).
  -- So Aᵀ.mulVecLin.range = span{row_i A | i : Fin m} = span(all rows of A).
  -- And we just proved span(all rows) = span(pivot rows).
  -- Therefore: rank(Aᵀ) = finrank(span(pivot rows)) ≤ |pivot rows|.
  calc
    Matrix.rank Aᵀ = Module.finrank ℚ (Aᵀ.mulVecLin.range) := rfl
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (λ i : Fin m => A i))) := by
      -- Aᵀ.mulVecLin.range = span of columns of Aᵀ = span of rows of A.
      -- Proof: column i of Aᵀ = (λ j : Fin n => A i j) = (A i) = rowVec A ⟨i, ?⟩.
      -- The range of M.mulVecLin is exactly the span of the columns of M.
      have h_range_eq : Aᵀ.mulVecLin.range = Submodule.span ℚ (Set.range (λ i : Fin m => A i)) := by
        apply le_antisymm
        · -- ⊆ : every Aᵀ*x is a linear combination of columns of Aᵀ = rows of A
          intro v hv; rcases LinearMap.mem_range.mp hv with ⟨x, rfl⟩
          -- Aᵀ * x = Σ_{i:Fin m} x_i * (column i of Aᵀ)
          -- Column i of Aᵀ = (λ j : Fin n => A i j) = A i (as Fin n → ℚ)
          -- So Aᵀ*x = Σ_i x_i * (A i) ∈ span of rows of A
          have h_sum : Aᵀ.mulVec x = ∑ i : Fin m, x i • (A i) := by
            ext j
            simp [Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]
          simp only [Matrix.mulVecLin_apply]
          rw [h_sum]
          refine Submodule.sum_mem _ (λ i _ => ?_)
          apply Submodule.smul_mem _ (x i)
          apply Submodule.subset_span
          exact ⟨i, rfl⟩
        · -- ⊇ : each row of A = column i of Aᵀ = Aᵀ * e_i ∈ range
          apply Submodule.span_le.mpr
          intro v hv; rcases Set.mem_range.mp hv with ⟨i, rfl⟩
          refine LinearMap.mem_range.mpr ⟨Pi.basisFun ℚ (Fin m) i, ?_⟩
          -- Aᵀ * e_i = column i of Aᵀ = row i of A
          ext j; simp [Matrix.mulVec, dotProduct, Pi.basisFun]
      rw [h_range_eq]
    _ = Module.finrank ℚ (Submodule.span ℚ (rows : Set (Fin n → ℚ))) := by
      simpa [rowVec] using congrArg
        (fun S : Submodule ℚ (Fin n → ℚ) => Module.finrank ℚ S) h_span_eq
    _ ≤ rows.card := by
      -- finrank(span of a Finset) ≤ cardinality of Finset
      have h_finrank : Set.finrank ℚ (rows : Set (Fin n → ℚ)) ≤ rows.card :=
        finrank_span_finset_le_card rows
      -- Set.finrank of the set coerced to Submodule should equal Module.finrank of span
      -- Wait, Set.finrank(s) = finrank(span(s)). So this holds.
      simpa using h_finrank

-- Lemma 7: rank(A) ≥ |P| — pivot COLUMNS of A are independent standard basis vectors
lemma pivot_card_le_rank (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ)
    (hp : PivotFun A f n) : (pivotRowVecs A f).card ≤ Matrix.rank A := by
  let P : Finset (Fin m) := Finset.filter (λ i : Fin m => f i.val < n) Finset.univ
  have h_card_eq : (pivotRowVecs A f).card = P.card := by
    dsimp [pivotRowVecs, rowVec]
    apply (Finset.card_image_iff).2
    intro i hi j hj h
    by_contra hne
    have hfi : f i.val < n :=
      (Finset.mem_filter.mp (show i ∈ P from hi)).2
    have hpiv := pivot_column_is_std_basis A f hp i.val i.2 hfi
    have h1 : A i ⟨f i.val, by omega⟩ = 1 := hpiv.1
    have hne_val : i.val ≠ j.val := by
      intro hval
      apply hne
      exact Fin.ext hval
    have h0 : A j ⟨f i.val, by omega⟩ = 0 := hpiv.2 j.val j.2 (Ne.symm hne_val)
    have h_eq_entry := congrArg (λ r : Fin n → ℚ => r ⟨f i.val, by omega⟩) h
    change A i ⟨f i.val, by omega⟩ = A j ⟨f i.val, by omega⟩ at h_eq_entry
    rw [h1, h0] at h_eq_entry; linarith
  rw [h_card_eq]
  -- For each i ∈ P, column f(i) of A = e_i (standard basis in Fin m → ℚ).
  -- These form an independent subset of A.mulVecLin.range (the column space).
  -- Column f(i) = A * e_{f(i)} (as a column, i.e., A applied to the f(i)-th basis vector
  -- of the domain Fin n → ℚ). Actually: column j of A = A.mulVec (e_j) where e_j is
  -- the j-th standard basis vector of Fin n → ℚ.
  -- So column f(i) = A.mulVec (Pi.basisFun ℚ (Fin n) ⟨f i, ...⟩) ∈ A.mulVecLin.range.
  -- These |P| vectors are independent because they equal distinct standard basis vectors
  -- of Fin m → ℚ (Lemma 2: A k (f i) = 0 for k ≠ i, A i (f i) = 1).
  -- Hence dim(col space) ≥ |P|.
  -- And Matrix.rank A = finrank(A.mulVecLin.range).
  --
  -- Use: the family {column_⟨f i, _⟩ | i ∈ P} in A.mulVecLin.range is independent.
  -- Each column_j = A * e_j, where e_j is standard basis in Fin n → ℚ.
  let columns : P → Fin m → ℚ := λ i => λ k => A k (⟨f i.val.val, by
    have hfi : f (i : P).val.val < n := (Finset.mem_filter.mp (i : P).2).2
    omega⟩ : Fin n)
  -- This is messy. Simpler: directly use that the standard basis vectors e_i for i ∈ P
  -- are independent, and each is in the column space of A.
  let stdBasis : P → Fin m → ℚ := λ i => Pi.basisFun ℚ (Fin m) i.val
  have h_independent : LinearIndependent ℚ stdBasis := by
    -- A subset of a basis is independent
    exact (Pi.basisFun ℚ (Fin m)).linearIndependent.comp
      (fun i : P => i.val) Subtype.val_injective
  -- Each stdBasis(i) = e_i = column f(i) of A ∈ A.mulVecLin.range.
  have h_mem : ∀ i : P, stdBasis i ∈ A.mulVecLin.range := by
    intro i
    have hfi : f i.val.val < n := (Finset.mem_filter.mp i.2).2
    have h_col_eq : stdBasis i = (λ k : Fin m => A k ⟨f i.val.val, hfi⟩) := by
      -- e_i(k) = if k = i then 1 else 0
      -- A k (f i) = if k = i then 1 else 0 (by Lemma 2)
      ext k
      rcases pivot_column_is_std_basis A f hp i.val.val i.val.2 hfi with ⟨h_one, h_zero⟩
      classical
      by_cases hki : k = i.val
      · subst hki
        simp [stdBasis, Pi.basisFun, h_one]
      · have hz := h_zero k.val k.2 (by
          intro h
          apply hki
          exact Fin.ext h)
        simp [stdBasis, Pi.basisFun, hz, hki]
    rw [h_col_eq]
    -- column f(i) of A = A * e_{f(i)} where e_{f(i)} is the f(i)-th basis vector of Fin n → ℚ
    -- A.mulVec (e_{f(i)}) = column f(i) of A
    refine LinearMap.mem_range.mpr ⟨Pi.basisFun ℚ (Fin n) ⟨f i.val.val, hfi⟩, ?_⟩
    ext k; simp [Matrix.mulVec, Pi.basisFun]
  -- `stdBasis` is independent and lies in A.mulVecLin.range
  have h_span_le : Submodule.span ℚ (Set.range stdBasis) ≤ A.mulVecLin.range :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr h_mem)
  -- `Fintype.card P = P.card` (since Subtype of Finset)
  have h_fintype_card : Fintype.card P = P.card := Fintype.card_coe P
  -- finrank of span of independent family = cardinality
  have h_finrank_span : Module.finrank ℚ (Submodule.span ℚ (Set.range stdBasis)) = Fintype.card P :=
    finrank_span_eq_card h_independent
  -- Combine: P.card = finrank(span(stdBasis)) ≤ finrank(A.mulVecLin.range) = rank(A)
  calc
    P.card = Fintype.card P := by symm; exact h_fintype_card
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range stdBasis)) := by symm; exact h_finrank_span
    _ ≤ Module.finrank ℚ (A.mulVecLin.range) := Submodule.finrank_mono h_span_le
    _ = Matrix.rank A := rfl

-- Main theorem: rank = pivot count
lemma pivotRows_card_eq_nat_filter (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ)
    (hp : PivotFun A f n) :
    (pivotRows A f).card =
      (Finset.filter (λ i : ℕ => i < m ∧ f i < n) (Finset.range m)).card := by
  let P : Finset (Fin m) := Finset.filter (λ i : Fin m => f i.val < n) Finset.univ
  let Q : Finset ℕ := Finset.filter (λ i : ℕ => i < m ∧ f i < n) (Finset.range m)
  have h_image : (pivotRows A f).card = P.card := by
    dsimp [pivotRows]
    apply (Finset.card_image_iff).2
    intro i hi j hj h
    by_contra hne
    have hfi : f i.val < n := (Finset.mem_filter.mp (show i ∈ P from hi)).2
    have hpiv := pivot_column_is_std_basis A f hp i.val i.2 hfi
    have h1 : A i ⟨f i.val, by omega⟩ = 1 := hpiv.1
    have hne_val : i.val ≠ j.val := by
      intro hval
      apply hne
      exact Fin.ext hval
    have h0 : A j ⟨f i.val, by omega⟩ = 0 := hpiv.2 j.val j.2 (Ne.symm hne_val)
    have h_eq_entry := congrArg (λ r : Fin n → ℚ => r ⟨f i.val, by omega⟩) h
    change A i ⟨f i.val, by omega⟩ = A j ⟨f i.val, by omega⟩ at h_eq_entry
    rw [h1, h0] at h_eq_entry
    linarith
  have h_filter : P.card = Q.card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      have hfi := (Finset.mem_filter.mp (show i ∈ P from hi)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, ⟨i.isLt, hfi⟩⟩
    · intro i hi j hj h
      exact Fin.ext h
    · intro b hb
      have hb' := Finset.mem_filter.mp hb
      refine ⟨⟨b, hb'.2.1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'.2.2⟩
  simpa [Q] using h_image.trans h_filter

theorem rank_rref_eq_pivot_count (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ)
    (hp : PivotFun A f n) : Matrix.rank A = (Finset.filter (λ i : ℕ => i < m ∧ f i < n) (Finset.range m)).card :=
  let h_upper : Matrix.rank A ≤ (pivotRows A f).card := by
    rw [← Matrix.rank_transpose A]
    exact rank_transpose_le_pivot_card A f hp
  let h_lower : (pivotRows A f).card ≤ Matrix.rank A := pivot_card_le_rank A f hp
  have h_pivot : Matrix.rank A = (pivotRows A f).card := le_antisymm h_upper h_lower
  calc
    Matrix.rank A = (pivotRows A f).card := h_pivot
    _ = (Finset.filter (λ i : ℕ => i < m ∧ f i < n) (Finset.range m)).card :=
      pivotRows_card_eq_nat_filter A f hp

end DAG.AFPGaussJordan
