import DAG.FunctionalGaussJordan
import DAG.AFPGaussJordan
import DAG.MatrixGaussJordan
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

open DAG.MatrixGaussJordan

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

lemma pivotFun_init
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) :
    AFPGaussJordan.PivotFun A (fun _ => 0) 0 := by
  refine ⟨Nat.zero_le n, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp
  · intro i hi hfi
    omega
  · intro i i' hi hfi hi' hne
    omega
  · intro i hi hfi j hj
    omega
  · intro i hi
    right
    rfl

lemma pivot_fun_advance_column
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ) (jj : ℕ)
    (hp : AFPGaussJordan.PivotFun A f jj) (hjj : jj < n)
    (h_no_pivot : ∀ (i : ℕ) (hi : i < m), f i = jj →
      A ⟨i, hi⟩ ⟨jj, hjj⟩ = 0) :
    AFPGaussJordan.PivotFun A
      (λ i => if f i = jj then jj + 1 else f i) (jj + 1) := by
  rcases hp with ⟨_, h_bound, h_pivot_one, h_pivot_zero, h_left_zero, h_strict⟩
  let f' := λ i => if f i = jj then jj + 1 else f i
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    dsimp [f']
    by_cases h_eq : f i = jj
    · simp [h_eq]
    · simp [h_eq]
      exact Nat.le_succ_of_le (h_bound i hi)
  · intro i hi hfi
    dsimp [f'] at hfi
    by_cases h_eq : f i = jj
    · simp [h_eq] at hfi
    · have hfi_lt_jj : f i < jj := by
        have hle := h_bound i hi
        omega
      simpa [h_eq] using h_pivot_one i hi hfi_lt_jj
  · intro i i' hi hfi hi' hne
    dsimp [f'] at hfi
    by_cases h_eq : f i = jj
    · simp [h_eq] at hfi
    · have hfi_lt_jj : f i < jj := by
        have hle := h_bound i hi
        omega
      simpa [h_eq] using h_pivot_zero i i' hi hfi_lt_jj hi' hne
  · intro i hi hfi j hj
    by_cases h_eq : f i = jj
    · by_cases hj_eq_jj : j < jj
      · have hj_old : j < f i := by simpa [h_eq] using hj_eq_jj
        exact h_left_zero i hi (h_bound i hi) j hj_old
      · have hj_val : j = jj := by omega
        subst j
        simpa using h_no_pivot i hi h_eq
    · have hj_old : j < f i := by simpa [h_eq] using hj
      exact h_left_zero i hi (h_bound i hi) j hj_old
  · intro i hi
    dsimp [f']
    have hbound_i := h_bound i (by omega)
    have hbound_i1 := h_bound (i + 1) (by omega)
    rcases h_strict i hi with (hlt | heq)
    · by_cases hfi : f i = jj
      · rw [hfi]
        by_cases hfi1 : f (i + 1) = jj
        · right; simp [hfi1]
        · omega
      · by_cases hfi1 : f (i + 1) = jj
        · right; simp [hfi1]
        · left; simp [hfi, hfi1, hlt]
    · right; simp [heq]

def PivotScanInvariant
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (f : ℕ → ℕ)
    (pivotRow col : ℕ) : Prop :=
  AFPGaussJordan.PivotFun A f col ∧
  (∀ r, r < pivotRow → f r < col) ∧
  (∀ r, pivotRow ≤ r → r < m → f r = col)

lemma pivotScanInvariant_init
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) :
    PivotScanInvariant A (fun _ => 0) 0 0 := by
  refine ⟨pivotFun_init A, ?_, ?_⟩
  · intro r hr
    omega
  · intro r hr hmr
    simp

lemma pivotScanInvariant_advance_no_pivot
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (f : ℕ → ℕ)
    (pivotRow col : ℕ)
    (hscan : PivotScanInvariant A f pivotRow col)
    (hcol : col < n)
    (h_no_pivot : ∀ i hi, f i = col →
      A ⟨i, hi⟩ ⟨col, hcol⟩ = 0) :
    PivotScanInvariant A
      (fun i => if f i = col then col + 1 else f i)
      pivotRow (col + 1) := by
  rcases hscan with ⟨hp, hbefore, hunprocessed⟩
  refine ⟨pivot_fun_advance_column A f col hp hcol h_no_pivot, ?_, ?_⟩
  · intro r hr
    by_cases hfr : f r = col
    · have hb := hbefore r hr
      simp [hfr] at hb ⊢
    · have hb := hbefore r hr
      simp [hfr] at ⊢
      omega
  · intro r hr hmr
    have hfr := hunprocessed r hr hmr
    simp [hfr]

lemma swap_unprocessed_preserves_left_zero
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    (f : ℕ → ℕ) (col : ℕ)
    (pr pi : Fin m)
    (hcol : col < n)
    (hpr_marker : f pr.val = col)
    (hpi_marker : f pi.val = col)
    (hleft : ∀ i (hi : i < m), f i ≤ col → ∀ (j : Fin n),
      j.val < f i → A ⟨i, hi⟩ j = 0) :
    ∀ r (hr : r < m), f r ≤ col → ∀ (j : Fin n), j.val < f r →
      let B : Matrix (Fin m) (Fin n) ℚ :=
        FunctionalGaussJordan.swapRowsMat pr pi * A
      B ⟨r, hr⟩ j = 0 := by
  intro r hr hfr j hj
  let B : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.swapRowsMat pr pi * A
  have hread := DAG.MatrixGaussJordan.swapRowsMat_apply
    (A := A) pr pi ⟨r, hr⟩ j
  change B ⟨r, hr⟩ j = 0
  dsimp [B]
  by_cases h_r_pr : (⟨r, hr⟩ : Fin m) = pr
  · have hr_pr : r = pr.val := congrArg Fin.val h_r_pr
    subst r
    simp [h_r_pr] at hread
    have hjcol : j.val < col := by simpa [hpr_marker] using hj
    have hsource := hleft pi pi.isLt (by omega) j
      (by simpa [hpi_marker] using hjcol)
    rw [hread]
    exact hsource
  · by_cases h_r_pi : (⟨r, hr⟩ : Fin m) = pi
    · have hr_pi : r = pi.val := congrArg Fin.val h_r_pi
      subst r
      simp [h_r_pi, h_r_pr] at hread
      have hjcol : j.val < col := by simpa [hpi_marker] using hj
      have hsource := hleft pr pr.isLt (by omega) j
        (by simpa [hpr_marker] using hjcol)
      rw [hread]
      exact hsource
    · simp [h_r_pr, h_r_pi] at hread
      rw [hread]
      exact hleft r hr hfr j hj

lemma fin_swap_row_ne_of_nat_ne
    {m : ℕ} {i i' : ℕ} {hi : i < m} {hi' : i' < m}
    {pr : Fin m}
    (hrow : (⟨i', hi'⟩ : Fin m) = pr)
    (hne : i' ≠ i) :
    pr.val ≠ i := by
  intro hval
  have hrowval := congrArg Fin.val hrow
  simp at hrowval
  apply hne
  omega

lemma fin_swap_row_ne_of_nat_ne_left
    {m : ℕ} {i i' : ℕ} {hi : i < m} {hi' : i' < m}
    {pi : Fin m}
    (hrow : (⟨i', hi'⟩ : Fin m) = pi)
    (hne : i' ≠ i) :
    pi.val ≠ i := by
  intro hval
  have hrowval := congrArg Fin.val hrow
  simp at hrowval
  apply hne
  omega

lemma swap_unprocessed_preserves_pivot_fun
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    (f : ℕ → ℕ) (col : ℕ)
    (pr pi : Fin m)
    (hcol : col < n)
    (hpr_marker : f pr.val = col)
    (hpi_marker : f pi.val = col)
    (hold_rows : ∀ i (hi : i < m), f i < col →
      (⟨i, hi⟩ : Fin m) ≠ pr ∧ (⟨i, hi⟩ : Fin m) ≠ pi)
    (hp : AFPGaussJordan.PivotFun A f col) :
    AFPGaussJordan.PivotFun
      (FunctionalGaussJordan.swapRowsMat pr pi * A) f col := by
  rcases hp with ⟨hn, hbound, hone, hzero, hleft, hstrict⟩
  have hleft' := swap_unprocessed_preserves_left_zero
    (A := A) f col pr pi hcol hpr_marker hpi_marker
    (fun i hi hfi j hj => hleft i hi hfi j.val hj)
  refine ⟨hn, hbound, ?_, ?_, ?_, hstrict⟩
  · intro i hi hfi
    have hread := DAG.MatrixGaussJordan.swapRowsMat_apply
      (A := A) pr pi ⟨i, hi⟩ ⟨f i, by omega⟩
    have hne_pr := hold_rows i hi hfi |>.1
    have hne_pi := hold_rows i hi hfi |>.2
    simp [hne_pr, hne_pi] at hread
    rw [hread]
    exact hone i hi hfi
  · intro i i' hi hfi hi' hne
    have hread := DAG.MatrixGaussJordan.swapRowsMat_apply
      (A := A) pr pi ⟨i', hi'⟩ ⟨f i, by omega⟩
    by_cases hpr : (⟨i', hi'⟩ : Fin m) = pr
    · have hi'_pr : i' = pr.val := congrArg Fin.val hpr
      subst i'
      simp [hpr] at hread
      rw [hread]
      exact hzero i pi hi hfi pi.isLt (by
        intro h
        have hmarker := hpi_marker
        rw [h] at hmarker
        omega)
    · by_cases hpi : (⟨i', hi'⟩ : Fin m) = pi
      · have hi'_pi : i' = pi.val := congrArg Fin.val hpi
        subst i'
        simp [hpi, hpr] at hread
        rw [hread]
        exact hzero i pr hi hfi pr.isLt (by
          intro h
          have hmarker := hpr_marker
          rw [h] at hmarker
          omega)
      · simp [hpr, hpi] at hread
        rw [hread]
        exact hzero i i' hi hfi hi' hne
  · intro i hi hfi j hj
    exact hleft' i hi hfi ⟨j, by omega⟩ (by simpa using hj)

def RrefPrefix
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (pivotRow col : ℕ) : Prop :=
  ∃ hFrontier : pivotRow ≤ m,
    ∃ pivotCol : Fin pivotRow → Fin n,
      (∀ r, (pivotCol r).val < col) ∧
      StrictMono pivotCol ∧
      (∀ r, A (Fin.castLE hFrontier r) (pivotCol r) = 1) ∧
      (∀ r s, r ≠ s →
        A (Fin.castLE hFrontier s) (pivotCol r) = 0) ∧
      (∀ r q, q.val < (pivotCol r).val →
        A (Fin.castLE hFrontier r) q = 0) ∧
      (∀ i q, pivotRow ≤ i.val → q.val < col → A i q = 0)

lemma rrefPrefix_init
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) :
    RrefPrefix A 0 0 := by
  refine ⟨by omega, fun r => Fin.elim0 r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact Fin.elim0 r
  · intro a
    exact Fin.elim0 a
  · intro r
    exact Fin.elim0 r
  · intro r s
    exact Fin.elim0 r
  · intro r q hq
    exact Fin.elim0 r
  · intro i q hi hq
    omega

lemma rrefPrefix_pivotColumn_isPivotColumnAt
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (hFrontier : pivotRow ≤ m)
    (pivotCol : Fin pivotRow → Fin n)
    (hlt : ∀ r, (pivotCol r).val < col)
    (hone : ∀ r, A (Fin.castLE hFrontier r) (pivotCol r) = 1)
    (hzero : ∀ r s, r ≠ s →
      A (Fin.castLE hFrontier s) (pivotCol r) = 0)
    (hunprocessed : ∀ i q, pivotRow ≤ i.val → q.val < col → A i q = 0) :
    ∀ r, DAG.MatrixGaussJordan.IsPivotColumnAt A (Fin.castLE hFrontier r) (pivotCol r) := by
  intro r k
  by_cases hk : k.val < pivotRow
  · let s : Fin pivotRow := ⟨k.val, hk⟩
    by_cases hsr : s = r
    · have hkrval : k.val = r.val := by
        simpa [s] using congrArg Fin.val hsr
      have hkr : k = Fin.castLE hFrontier r := by
        apply Fin.ext
        exact hkrval
      simp [hkr, hone]
    · have hks : k = Fin.castLE hFrontier s := by
        apply Fin.ext
        rfl
      rw [hks]
      rw [hzero r s (Ne.symm hsr)]
      simp [hsr]
  · have hkr : pivotRow ≤ k.val := Nat.le_of_not_gt hk
    have hz := hunprocessed k (pivotCol r) hkr (hlt r)
    have hne : k ≠ Fin.castLE hFrontier r := by
      intro heq
      have hkval : k.val = r.val := by
        simpa using congrArg Fin.val heq
      omega
    simp [hz, hne]

lemma rrefPrefix_advance_no_pivot
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (hp : RrefPrefix A pivotRow col)
    (hcol : col < n)
    (h_no_pivot : ∀ (i : Fin m), pivotRow ≤ i.val →
      A i ⟨col, hcol⟩ = 0) :
    RrefPrefix A pivotRow (col + 1) := by
  rcases hp with ⟨hFrontier, pivotCol, hlt, hmono, hone, hzero, hleft, hunprocessed⟩
  refine ⟨hFrontier, pivotCol, ?_, hmono, hone, hzero, hleft, ?_⟩
  · intro r
    have hr := hlt r
    omega
  · intro i q hi hq
    by_cases hqcol : q.val < col
    · exact hunprocessed i q hi hqcol
    · have hqeq : q.val = col := by omega
      have hqfin : q = ⟨col, hcol⟩ := Fin.ext hqeq
      subst q
      simpa using h_no_pivot i hi

def extendPivotCol
    {pivotRow n : ℕ}
    (old : Fin pivotRow → Fin n)
    (col : Fin n) : Fin (pivotRow + 1) → Fin n :=
  fun r => if hr : r.val < pivotRow then old ⟨r.val, hr⟩ else col

lemma strictMono_extendPivotCol
    {pivotRow n : ℕ}
    {old : Fin pivotRow → Fin n}
    {col : Fin n}
    (hold : StrictMono old)
    (hlt : ∀ r, (old r).val < col.val) :
    StrictMono (extendPivotCol old col) := by
  intro r s hrs
  by_cases hr : r.val < pivotRow
  · by_cases hs : s.val < pivotRow
    · dsimp [extendPivotCol]
      simp [hr, hs]
      apply hold
      exact Fin.mk_lt_mk.mpr (by omega)
    · dsimp [extendPivotCol]
      simp [hr, hs]
      exact Fin.mk_lt_mk.mpr (by
        have h := hlt ⟨r.val, hr⟩
        omega)
  · have hs : s.val < pivotRow := by
      omega
    exfalso
    omega

lemma rrefPrefix_successful_hone
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hFrontier : pivotRow ≤ m)
    (pivotCol : Fin pivotRow → Fin n)
    (hlt : ∀ r, (pivotCol r).val < col)
    (hone : ∀ r, A (Fin.castLE hFrontier r) (pivotCol r) = 1)
    (hzero : ∀ r s, r ≠ s →
      A (Fin.castLE hFrontier s) (pivotCol r) = 0)
    (hunprocessed : ∀ i q, pivotRow ≤ i.val → q.val < col → A i q = 0)
    (hcol : col < n) {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    ∀ r : Fin (pivotRow + 1),
      (selectedPivotStep A pivotRow col Es hcol pi hrow).1
        (Fin.castLE (show pivotRow + 1 ≤ m by omega) r)
        (extendPivotCol pivotCol ⟨col, hcol⟩ r) = 1 := by
  intro r
  by_cases hr : r.val < pivotRow
  · let old : Fin pivotRow := ⟨r.val, hr⟩
    have hold : IsPivotColumnAt A
        (Fin.castLE hFrontier old) (pivotCol old) :=
      rrefPrefix_pivotColumn_isPivotColumnAt
        hFrontier pivotCol hlt hone hzero hunprocessed old
    have hpres := selectedPivotStep_preserves_pivot_column
      Es hcol hfind hrow hold old.isLt
    have hrow_eq :
        Fin.castLE (show pivotRow + 1 ≤ m by omega) r =
          Fin.castLE hFrontier old := by
      apply Fin.ext
      rfl
    rw [hrow_eq]
    simpa [extendPivotCol, old, hr] using
      hpres (Fin.castLE hFrontier old)
  · have hr_eq : r.val = pivotRow := by omega
    have hr_eq' : r = ⟨pivotRow, by omega⟩ := by
      apply Fin.ext
      exact hr_eq
    rw [hr_eq']
    have hrow_eq :
        Fin.castLE (show pivotRow + 1 ≤ m by omega) ⟨pivotRow, by omega⟩ =
          (⟨pivotRow, hrow⟩ : Fin m) := by
      apply Fin.ext
      rfl
    rw [hrow_eq]
    simpa [extendPivotCol] using
      selectedPivotStep_pivot_eq_one Es hcol hfind hrow

lemma rrefPrefix_successful_hzero
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hFrontier : pivotRow ≤ m)
    (pivotCol : Fin pivotRow → Fin n)
    (hlt : ∀ r, (pivotCol r).val < col)
    (hone : ∀ r, A (Fin.castLE hFrontier r) (pivotCol r) = 1)
    (hzero : ∀ r s, r ≠ s →
      A (Fin.castLE hFrontier s) (pivotCol r) = 0)
    (hunprocessed : ∀ i q, pivotRow ≤ i.val → q.val < col → A i q = 0)
    (hcol : col < n) {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    ∀ r s : Fin (pivotRow + 1), r ≠ s →
      (selectedPivotStep A pivotRow col Es hcol pi hrow).1
        (Fin.castLE (show pivotRow + 1 ≤ m by omega) s)
        (extendPivotCol pivotCol ⟨col, hcol⟩ r) = 0 := by
  intro r s hrs
  by_cases hr : r.val < pivotRow
  · let old : Fin pivotRow := ⟨r.val, hr⟩
    let oldRow : Fin m := Fin.castLE hFrontier old
    let k : Fin m := Fin.castLE (show pivotRow + 1 ≤ m by omega) s
    have hold : IsPivotColumnAt A oldRow (pivotCol old) :=
      rrefPrefix_pivotColumn_isPivotColumnAt
        hFrontier pivotCol hlt hone hzero hunprocessed old
    have hpres := selectedPivotStep_preserves_pivot_column
      Es hcol hfind hrow hold old.isLt
    have hk : k ≠ oldRow := by
      intro h
      apply hrs
      apply Fin.ext
      simpa [k, oldRow, old] using congrArg Fin.val h.symm
    have hz := hpres k
    rw [if_neg hk] at hz
    simpa [extendPivotCol, old, k, hr] using hz
  · have hr_eq : r.val = pivotRow := by omega
    let k : Fin m := Fin.castLE (show pivotRow + 1 ≤ m by omega) s
    have hk : k ≠ (⟨pivotRow, hrow⟩ : Fin m) := by
      intro h
      have hs_eq : s.val = pivotRow := by
        simpa [k] using congrArg Fin.val h
      apply hrs
      apply Fin.ext
      omega
    have hz := selectedPivotStep_pivot_column_zero
      Es hcol hfind hrow k hk
    simpa [extendPivotCol, k, hr] using hz

lemma rrefPrefix_successful_hleft
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hFrontier : pivotRow ≤ m)
    (pivotCol : Fin pivotRow → Fin n)
    (hlt : ∀ r, (pivotCol r).val < col)
    (hleft : ∀ r q, q.val < (pivotCol r).val →
      A (Fin.castLE hFrontier r) q = 0)
    (hunprocessed : ∀ i q, pivotRow ≤ i.val → q.val < col → A i q = 0)
    (hcol : col < n) {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    ∀ r : Fin (pivotRow + 1), ∀ q : Fin n,
      q.val < (extendPivotCol pivotCol ⟨col, hcol⟩ r).val →
      (selectedPivotStep A pivotRow col Es hcol pi hrow).1
        (Fin.castLE (show pivotRow + 1 ≤ m by omega) r) q = 0 := by
  intro r q hq
  have hpi_ge : pivotRow ≤ pi.val :=
    (findPivot_spec A pivotRow ⟨col, hcol⟩ hfind).2
  by_cases hr : r.val < pivotRow
  · let old : Fin pivotRow := ⟨r.val, hr⟩
    let oldRow : Fin m := Fin.castLE hFrontier old
    have hqold : q.val < (pivotCol old).val := by
      simpa [extendPivotCol, old, hr] using hq
    have hqcol : q.val < col := lt_trans hqold (hlt old)
    have hold : A oldRow q = 0 := by
      simpa [oldRow] using hleft old q hqold
    have hsource : A pi q = 0 := hunprocessed pi q hpi_ge hqcol
    have hz := selectedPivotStep_preserves_old_left_zero
      Es hcol hfind hrow old.isLt hold hsource
    have hrow_eq :
        Fin.castLE (show pivotRow + 1 ≤ m by omega) r = oldRow := by
      apply Fin.ext
      rfl
    rw [hrow_eq]
    exact hz
  · have hr_eq : r.val = pivotRow := by omega
    have hqcol : q.val < col := by
      simpa [extendPivotCol, hr] using hq
    have hsource : A pi q = 0 := hunprocessed pi q hpi_ge hqcol
    have hz := selectedPivotStep_active_row_left_zero
      Es hcol hfind hrow hqcol hsource
    have hrow_eq :
        Fin.castLE (show pivotRow + 1 ≤ m by omega) r =
          (⟨pivotRow, hrow⟩ : Fin m) := by
      apply Fin.ext
      exact hr_eq
    rw [hrow_eq]
    exact hz

lemma rrefPrefix_successful_hunprocessed
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hunprocessed : ∀ i q, pivotRow ≤ i.val → q.val < col → A i q = 0)
    (hcol : col < n) {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    ∀ i : Fin m, ∀ q : Fin n,
      pivotRow + 1 ≤ i.val → q.val < col + 1 →
      (selectedPivotStep A pivotRow col Es hcol pi hrow).1 i q = 0 := by
  intro i q hi hq
  have hi_pr : i ≠ (⟨pivotRow, hrow⟩ : Fin m) := by
    intro h
    have hv : i.val = pivotRow := congrArg Fin.val h
    have hlt : pivotRow < i.val := by omega
    exact (Nat.ne_of_gt hlt) hv
  by_cases hqcol : q.val < col
  · have hpi_ge : pivotRow ≤ pi.val :=
      (findPivot_spec A pivotRow ⟨col, hcol⟩ hfind).2
    have htarget : A i q = 0 := hunprocessed i q (by omega) hqcol
    have hsource : A pi q = 0 := hunprocessed pi q hpi_ge hqcol
    have hactive : A ⟨pivotRow, hrow⟩ q = 0 :=
      hunprocessed ⟨pivotRow, hrow⟩ q (by simp) hqcol
    exact selectedPivotStep_preserves_unprocessed_left_zero
      Es hcol hfind hrow hi_pr htarget hsource hactive
  · have hqeq : q.val = col := by omega
    have hqfin : q = ⟨col, hcol⟩ := by
      apply Fin.ext
      exact hqeq
    rw [hqfin]
    exact selectedPivotStep_pivot_column_zero
      Es hcol hfind hrow i hi_pr

lemma rrefPrefix_successful_pivot
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hp : RrefPrefix A pivotRow col)
    (hcol : col < n)
    {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    RrefPrefix
      (selectedPivotStep A pivotRow col Es hcol pi hrow).1
      (pivotRow + 1) (col + 1) := by
  rcases hp with ⟨hFrontier, pivotCol, hlt, hmono, hone, hzero, hleft,
    hunprocessed⟩
  let j : Fin n := ⟨col, hcol⟩
  let newPivotCol : Fin (pivotRow + 1) → Fin n :=
    extendPivotCol pivotCol j
  have hnewFrontier : pivotRow + 1 ≤ m := by omega
  refine ⟨hnewFrontier, newPivotCol, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases hr : r.val < pivotRow
    · have hold : (pivotCol ⟨r.val, hr⟩).val < col := hlt ⟨r.val, hr⟩
      simpa [newPivotCol, extendPivotCol, j, hr] using
        Nat.lt_succ_of_lt hold
    · have hr_eq : r.val = pivotRow := by omega
      simp [newPivotCol, extendPivotCol, j, hr]
  · simpa [newPivotCol, j] using
      strictMono_extendPivotCol hmono (by
        intro r
        simpa [j] using hlt r)
  · simpa [newPivotCol, j] using
      rrefPrefix_successful_hone Es hFrontier pivotCol hlt hone hzero
        hunprocessed hcol hfind hrow
  · simpa [newPivotCol, j] using
      rrefPrefix_successful_hzero Es hFrontier pivotCol hlt hone hzero
        hunprocessed hcol hfind hrow
  · simpa [newPivotCol, j] using
      rrefPrefix_successful_hleft Es hFrontier pivotCol hlt hleft
        hunprocessed hcol hfind hrow
  · exact rrefPrefix_successful_hunprocessed
      Es hunprocessed hcol hfind hrow

lemma gaussJordanElimFull_go_rrefPrefix
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol_le : col ≤ n)
    (hp : RrefPrefix A pivotRow col) :
    let out := gaussJordanElimFull.go A pivotRow col Es
    RrefPrefix out.1 out.2.1 n := by
  let P := fun (X : Matrix (Fin m) (Fin n) ℚ) (r c : ℕ)
      (ops : List (Matrix (Fin m) (Fin m) ℚ)) =>
    c ≤ n → RrefPrefix X r c →
      let out := gaussJordanElimFull.go X r c ops
      RrefPrefix out.1 out.2.1 n
  have hP : P A pivotRow col Es := by
    apply gaussJordanElimFull_go_induction Es P
    · intro X r c ops hstop hcn hprefix
      have hc : c = n := by omega
      subst c
      rw [gaussJordanElimFull_go_col_exhausted ops (by omega)]
      simpa using hprefix
    · intro X r c ops hc hfind ih hcn hprefix
      have h_no_pivot : ∀ (i : Fin m), r ≤ i.val →
          X i ⟨c, hc⟩ = 0 := by
        intro i hi
        exact findPivot_none_spec X r ⟨c, hc⟩ hfind i hi
      have hnext : RrefPrefix X r (c + 1) :=
        rrefPrefix_advance_no_pivot hprefix hc h_no_pivot
      rw [gaussJordanElimFull_go_no_pivot ops hc hfind]
      exact ih (by omega) hnext
    · intro X r c ops hc pi hfind hr hcn hprefix
      rcases hprefix with ⟨hfrontier, _⟩
      have hpi_ge : r ≤ pi.val :=
        (findPivot_spec X r ⟨c, hc⟩ hfind).2
      omega
    · intro X r c ops hc pi hr hfind ih hcn hprefix
      have hnext : RrefPrefix
          (selectedPivotStep X r c ops hc pi hr).1
          (r + 1) (c + 1) :=
        rrefPrefix_successful_pivot ops hprefix hc hfind hr
      rw [gaussJordanElimFull_go_selected_pivot ops hc hfind hr]
      exact ih (by omega) hnext
  exact hP hcol_le hp

lemma gaussJordanElimFull_rrefPrefix
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) :
    let out := gaussJordanElimFull.go A 0 0 []
    RrefPrefix out.1 out.2.1 n := by
  exact gaussJordanElimFull_go_rrefPrefix [] (by omega) (rrefPrefix_init A)

lemma rrefPrefix_to_pivotFun
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow : ℕ}
    (hp : RrefPrefix A pivotRow n) :
    ∃ f : ℕ → ℕ, AFPGaussJordan.PivotFun A f n := by
  rcases hp with ⟨hFrontier, pivotCol, hlt, hmono, hone, hzero, hleft,
    hunprocessed⟩
  let f : ℕ → ℕ := fun i =>
    if hi : i < pivotRow then (pivotCol ⟨i, hi⟩).val else n
  refine ⟨f, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hip : i < pivotRow
    · simpa [f, hip] using Nat.le_of_lt (hlt ⟨i, hip⟩)
    · simp [f, hip]
  · intro i hi hfi
    have hip : i < pivotRow := by
      by_contra hnot
      simp [f, hnot] at hfi
    have hrow : (⟨i, hi⟩ : Fin m) =
        Fin.castLE hFrontier (⟨i, hip⟩ : Fin pivotRow) := by
      apply Fin.ext
      rfl
    have hf : f i = (pivotCol ⟨i, hip⟩).val := by
      simp [f, hip]
    have hcol : (⟨f i, hfi⟩ : Fin n) = pivotCol ⟨i, hip⟩ := by
      apply Fin.ext
      exact hf
    rw [hrow, hcol]
    exact hone ⟨i, hip⟩
  · intro i i' hi hfi hi' hne
    have hip : i < pivotRow := by
      by_contra hnot
      simp [f, hnot] at hfi
    let r : Fin pivotRow := ⟨i, hip⟩
    have hrow : (⟨i, hi⟩ : Fin m) = Fin.castLE hFrontier r := by
      apply Fin.ext
      rfl
    by_cases hi'p : i' < pivotRow
    · let s : Fin pivotRow := ⟨i', hi'p⟩
      have hrow' : (⟨i', hi'⟩ : Fin m) = Fin.castLE hFrontier s := by
        apply Fin.ext
        rfl
      have hrs : r ≠ s := by
        intro hrs
        apply hne
        exact (congrArg Fin.val hrs).symm
      have hf : f i = (pivotCol r).val := by
        simp [f, hip, r]
      have hcol : (⟨f i, hfi⟩ : Fin n) = pivotCol r := by
        apply Fin.ext
        exact hf
      rw [hrow', hcol]
      exact hzero r s hrs
    · have hi'ge : pivotRow ≤ i' := Nat.le_of_not_gt hi'p
      have hz := hunprocessed ⟨i', hi'⟩ (pivotCol r) hi'ge (hlt r)
      have hf : f i = (pivotCol r).val := by
        simp [f, hip, r]
      have hcol : (⟨f i, hfi⟩ : Fin n) = pivotCol r := by
        apply Fin.ext
        exact hf
      rw [hcol]
      exact hz
  · intro i hi hfi q hq
    by_cases hip : i < pivotRow
    · let r : Fin pivotRow := ⟨i, hip⟩
      have hrow : (⟨i, hi⟩ : Fin m) = Fin.castLE hFrontier r := by
        apply Fin.ext
        rfl
      have hq' : q < (pivotCol r).val := by
        simpa [f, hip, r] using hq
      simpa [hrow] using hleft r ⟨q, by omega⟩ (by simpa using hq')
    · have hige : pivotRow ≤ i := Nat.le_of_not_gt hip
      have hq' : q < n := by
        simpa [f, hip] using hq
      exact hunprocessed ⟨i, hi⟩ ⟨q, hq'⟩ hige hq'
  · intro i hi
    by_cases hs : i + 1 < pivotRow
    · have hip : i < pivotRow := by omega
      left
      have hmono' := hmono (show (⟨i, hip⟩ : Fin pivotRow) <
        ⟨i + 1, hs⟩ by exact Fin.mk_lt_mk.mpr (by omega))
      simpa [f, hip, hs] using hmono'
    · right
      simp [f, hs]

lemma gaussJordanElimFull_pivotFun
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) :
    let out := gaussJordanElimFull.go A 0 0 []
    ∃ f : ℕ → ℕ, AFPGaussJordan.PivotFun out.1 f n := by
  exact rrefPrefix_to_pivotFun (gaussJordanElimFull_rrefPrefix A)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

abbrev stdBasisMatrix (i j : m) (a : ℚ) : Matrix m m ℚ := Matrix.single i j a

lemma scaleRow_makes_entry_one (A : Matrix m n ℚ) (i : m) (j : n) (h : A i j ≠ 0) :
    (FunctionalGaussJordan.scaleRowMat i (A i j)⁻¹ * A) i j = 1 := by
  dsimp [FunctionalGaussJordan.scaleRowMat]
  rw [Matrix.add_mul]
  simp [Matrix.mul_apply, Matrix.single_apply]
  rw [sub_mul, inv_mul_cancel₀ h]
  ring

lemma addRow_zeroes_entry (A : Matrix m n ℚ) (i k : m) (j : n) (hij : A i j = 1) :
    (FunctionalGaussJordan.addRowMat k i (-(A k j)) * A) k j = 0 := by
  dsimp [FunctionalGaussJordan.addRowMat]
  rw [Matrix.add_mul]
  by_cases hki : k = i
  · subst k
    simp [Matrix.mul_apply, Matrix.single_apply, hij]
  · simp [Matrix.mul_apply, Matrix.single_apply, hki, hij]

lemma stdBasisMatrix_mul_stdBasisMatrix_eq_zero {k k' i : m} (h_ne : i ≠ k') :
    stdBasisMatrix k i (1 : ℚ) * stdBasisMatrix k' i (1 : ℚ) = 0 := by
  dsimp [stdBasisMatrix]
  rw [single_mul_single_of_ne (1 : ℚ) k i k' h_ne (1 : ℚ)]

lemma stdBasisMatrix_mul_entry_row_i {k i : m} (hk : k ≠ i) (M : Matrix m n ℚ) (j : n) :
    (stdBasisMatrix k i (1 : ℚ) * M) i j = 0 := by
  simp [Matrix.mul_apply, stdBasisMatrix, hk]

lemma stdBasisMatrix_mul_entry_row_k {k i : m} (hk : k ≠ i) (M : Matrix m n ℚ) (j : n) :
    (stdBasisMatrix k i (1 : ℚ) * M) k j = M i j := by
  dsimp [stdBasisMatrix]
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Matrix.single_apply, hbi, hbi.symm]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

lemma stdBasisMatrix_mul_entry_row_i_diag (M : Matrix m n ℚ) (i : m) (j : n) :
    (stdBasisMatrix i i (1 : ℚ) * M) i j = M i j := by
  dsimp [stdBasisMatrix]
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Matrix.single_apply, hbi, hbi.symm]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

lemma scaleRowMat_mul_entry_row_i (M : Matrix m n ℚ) (i : m) (c : n) (s : ℚ) :
    (FunctionalGaussJordan.scaleRowMat i s * M) i c = s * M i c := by
  dsimp [FunctionalGaussJordan.scaleRowMat]
  rw [Matrix.add_mul, Matrix.add_apply, Matrix.one_mul]
  rw [Matrix.smul_mul]
  rw [Matrix.smul_apply]
  rw [stdBasisMatrix_mul_entry_row_i_diag M i c]
  simp only [smul_eq_mul]
  ring

lemma stdBasisMatrix_diag_mul_entry_row_ne (M : Matrix m n ℚ) (i r : m) (hr : r ≠ i) (c : n) :
    (stdBasisMatrix i i (1 : ℚ) * M) r c = 0 := by
  dsimp [stdBasisMatrix]
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp [Matrix.single_apply, hr, hr.symm]

lemma scaleRowMat_mul_entry_row_ne (M : Matrix m n ℚ) (i r : m) (hr : r ≠ i) (c : n) (s : ℚ) :
    (FunctionalGaussJordan.scaleRowMat i s * M) r c = M r c := by
  dsimp [FunctionalGaussJordan.scaleRowMat]
  rw [Matrix.add_mul, Matrix.add_apply, Matrix.one_mul]
  rw [Matrix.smul_mul]
  rw [Matrix.smul_apply]
  rw [stdBasisMatrix_diag_mul_entry_row_ne M i r hr c]
  simp

lemma sum_row_units_sq_zero (i : m) (s : Finset m) (hs : ∀ k ∈ s, k ≠ i) (a : m → ℚ) :
    (Finset.sum s (fun k => a k • stdBasisMatrix k i (1 : ℚ))) *
      (Finset.sum s (fun k => a k • stdBasisMatrix k i (1 : ℚ))) = 0 := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  rw [smul_mul_smul]
  rw [Matrix.single_mul_single_of_ne (1 : ℚ) k i l (hs l hl).symm (1 : ℚ)]
  simp

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
  have h_units_sq :
      (Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)) *
        (Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)) = 0 := by
    apply sum_row_units_sq_zero i notI
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have h_neg_units :
      Finset.sum notI (λ k => (-a k) • stdBasisMatrix k i 1) =
        -(Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp [neg_smul]
  have h_square_inverse (S : Matrix m m ℚ) (hS : S * S = 0) :
      (1 + S) * (1 - S) = 1 := by
    calc
      (1 + S) * (1 - S) = 1 - S * S := by noncomm_ring
      _ = 1 := by rw [hS]; simp
  have h_square_inverse_rev (S : Matrix m m ℚ) (hS : S * S = 0) :
      (1 - S) * (1 + S) = 1 := by
    calc
      (1 - S) * (1 + S) = 1 - S * S := by noncomm_ring
      _ = 1 := by rw [hS]; simp
  have h_mul : E2 * E2inv = 1 := by
    dsimp [E2, E2inv]
    rw [h_neg_units]
    simpa [sub_eq_add_neg] using h_square_inverse
      (Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)) h_units_sq
  have h_mul' : E2inv * E2 = 1 := by
    dsimp [E2, E2inv]
    rw [h_neg_units]
    simpa [sub_eq_add_neg] using h_square_inverse_rev
      (Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)) h_units_sq
  have hE2 : IsUnit E2 := ⟨⟨E2, E2inv, h_mul, h_mul'⟩, rfl⟩
  have h_ij : (E2 * A1) i j = 1 := by
    dsimp [E2]
    rw [Matrix.add_mul]
    rw [Matrix.add_apply]
    rw [Matrix.one_mul]
    rw [hA1_ij]
    have hrow_sum : (Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)) i = 0 := by
      funext y
      have hz : ∀ k ∈ notI, (a k • stdBasisMatrix k i 1) i = 0 := by
        intro k hk
        funext z
        rw [smul_apply]
        simp [stdBasisMatrix, (Finset.mem_filter.mp hk).2]
      rw [Finset.sum_apply]
      simpa only [Pi.zero_apply] using congrFun (Finset.sum_eq_zero hz) y
    rw [Matrix.mul_apply]
    have hprod : ∀ x ∈ Finset.univ,
        (Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)) i x * A1 x j = 0 := by
      intro x hx
      rw [show (Finset.sum notI (λ k => a k • stdBasisMatrix k i 1)) i x = 0 from congrFun hrow_sum x]
      simp
    rw [Finset.sum_eq_zero hprod]
    simp
  have h_kj_zero : ∀ k, k ≠ i → (E2 * A1) k j = 0 := by
    intro k hk
    have hk_mem : k ∈ notI := by simp [notI, hk]
    have hsum_row : (Finset.sum notI (λ b => a b • stdBasisMatrix b i 1)) k =
        (a k • stdBasisMatrix k i 1) k := by
      funext y
      rw [Finset.sum_apply k notI]
      exact congrFun (Finset.sum_eq_single (s := notI)
        (f := fun b => (a b • stdBasisMatrix b i 1) k) k
        (by
          intro b hb hbk
          funext z
          simp [stdBasisMatrix, hbk])
        (by
          intro hk_not_mem
          exact (hk_not_mem hk_mem).elim)) y
    dsimp [E2]
    rw [Matrix.add_mul, Matrix.one_mul]
    have hprod :
        (Finset.sum notI (λ b => a b • stdBasisMatrix b i 1) * A1) k j =
          a k * A1 i j := by
      calc
        (Finset.sum notI (λ b => a b • stdBasisMatrix b i 1) * A1) k j =
            ((a k • stdBasisMatrix k i 1) * A1) k j := by
              rw [Matrix.mul_apply]
              apply Finset.sum_congr rfl
              intro x hx
              rw [congrFun hsum_row x]
        _ = a k * A1 i j := by
          rw [show (a k • stdBasisMatrix k i 1) * A1 =
              a k • (stdBasisMatrix k i 1 * A1) by rw [Matrix.smul_mul]]
          rw [Matrix.smul_apply]
          rw [stdBasisMatrix_mul_entry_row_k hk A1 j]
          simp [smul_eq_mul]
    rw [Matrix.add_apply, hprod]
    simp [a, hA1_ij]
  let E := E2 * E1
  refine ⟨E, hE2.mul hE1, ?_, ?_⟩
  · dsimp [E, A1]
    rw [Matrix.mul_assoc]
    exact h_ij
  · intro k hk
    dsimp [E, A1]
    rw [Matrix.mul_assoc]
    exact h_kj_zero k hk

lemma filtered_elimination_row_readback (A1 : Matrix m n ℚ) (i r : m) (j c : n)
    (hr : r ≠ i) :
    let notI : Finset m := Finset.filter (λ k => k ≠ i) Finset.univ
    (((1 : Matrix m m ℚ) + Finset.sum notI (λ k => -(A1 k j) • stdBasisMatrix k i 1)) * A1) r c =
      A1 r c - A1 r j * A1 i c := by
  intro notI
  have hr_mem : r ∈ notI := by simp [notI, hr]
  have hsum_row :
      (Finset.sum notI (λ b => -(A1 b j) • stdBasisMatrix b i 1)) r =
        (-(A1 r j) • stdBasisMatrix r i 1) r := by
    funext y
    rw [Finset.sum_apply r notI]
    exact congrFun (Finset.sum_eq_single (s := notI)
      (f := fun b => (-(A1 b j) • stdBasisMatrix b i 1) r) r
      (by
        intro b hb hbr
        funext z
        simp [stdBasisMatrix, hbr])
      (by
        intro hr_not_mem
        exact (hr_not_mem hr_mem).elim)) y
  rw [Matrix.add_mul, Matrix.add_apply]
  have hprod :
      (Finset.sum notI (λ k => -(A1 k j) • stdBasisMatrix k i 1) * A1) r c =
        -(A1 r j) * A1 i c := by
    calc
      (Finset.sum notI (λ k => -(A1 k j) • stdBasisMatrix k i 1) * A1) r c =
          ((-(A1 r j) • stdBasisMatrix r i 1) * A1) r c := by
            rw [Matrix.mul_apply]
            apply Finset.sum_congr rfl
            intro x hx
            rw [congrFun hsum_row x]
      _ = -(A1 r j) * A1 i c := by
        rw [show (-(A1 r j) • stdBasisMatrix r i 1) * A1 =
            -(A1 r j) • (stdBasisMatrix r i 1 * A1) by rw [Matrix.smul_mul]]
        rw [Matrix.smul_apply]
        rw [stdBasisMatrix_mul_entry_row_k hr A1 c]
        simp [smul_eq_mul]
  rw [hprod]
  rw [Matrix.one_mul]
  ring

/-- Explicit formula for pivot_step: for r ≠ i,
    (Ej * M)(r, c) = M(r, c) - M(r, j) * (M i j)⁻¹ * M(i, c).
    Extracted from the construction in pivot_step. -/
lemma pivot_step_formula (M : Matrix m n ℚ) (i : m) (j : n)
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
  have hcore := filtered_elimination_row_readback A1 i r j c hr_ne
  have hA1_i_c : A1 i c = s * M i c := by
    dsimp [A1, E1]
    exact scaleRowMat_mul_entry_row_i M i c s
  have hA1_r_c : A1 r c = M r c := by
    dsimp [A1, E1]
    exact scaleRowMat_mul_entry_row_ne M i r hr_ne c s
  have hA1_r_j : A1 r j = M r j := by
    dsimp [A1, E1]
    exact scaleRowMat_mul_entry_row_ne M i r hr_ne j s
  dsimp [Ej, E2, a]
  rw [Matrix.mul_assoc]
  rw [hcore]
  rw [hA1_i_c, hA1_r_c, hA1_r_j]
  ring

/-
The former `FinitePivotCorridor` was an unfinished reconstruction.  It mixed
the six-field working-tree `PivotFun` contract with an unproved recursive
construction and did not compile.  Keep it archived in source history rather
than exposing it as a production theorem surface.

/-! ### Lemma 2: PivotFun preserved by one column step -/

open AFPGaussJordan

section FinitePivotCorridor

variable {m n : ℕ}

/-- After pivot_step at (i,j), there exists an elimination matrix with the expected column behavior. -/
lemma pivot_fun_update_after_step (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ) (jj : ℕ) (i : Fin m) (j : Fin n)
    (hp : PivotFun A f jj) (hp_bound : f i.val = jj) (hp_pos : jj ≤ n)
    (hij : A i j ≠ 0) :
    ∃ (E : Matrix (Fin m) (Fin m) ℚ), IsUnit E ∧ (E * A) i j = 1 ∧ ∀ k, k ≠ i → (E * A) k j = 0 := by
  exact pivot_step A i j hij

/-! ### Lemma 3: Process all columns → PivotFun with full pivot set -/

/-- In PivotFun A f n, rows with f i < n are nonzero (pivot 1), rows with f i = n are zero. -/
lemma nonzero_rows_are_pivot_rows (A : Matrix (Fin m) (Fin n) ℚ) (f : ℕ → ℕ) (hp : PivotFun A f n) :
    (Finset.filter (λ i : Fin m => ∃ j : Fin n, A i j ≠ 0) Finset.univ).card =
    (Finset.filter (λ i : Fin m => f i.val < n) Finset.univ).card := by
  have hp_orig := hp
  rcases hp with ⟨_, h_bound, h_pivot_one, _, h_left_zero, _⟩
  -- Bijection between the two sets: i ↔ i where f i < n iff row i is nonzero.
  -- If f i < n: A(i, f i) = 1 ≠ 0, so i is in the first set.
  -- If f i = n: ∀ j, A(i, j) = 0, so i is NOT in the first set.
  have h_eq_sets : (Finset.filter (λ i : Fin m => ∃ j : Fin n, A i j ≠ 0) Finset.univ) =
      (Finset.filter (λ i : Fin m => f i.val < n) Finset.univ) := by
    ext i; constructor
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨_, ⟨j, hj⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      by_contra hfi
      have hfi_eq_n : f i.val = n := by have hb := h_bound i.val i.2; omega
      rw [AFPGaussJordan.non_pivot_rows_zero A f hp_orig i.val i.2 hfi_eq_n j] at hj
      simp at hj
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨_, hfi⟩
      have hi_m : i.val < m := i.isLt
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      refine ⟨⟨f i.val, by omega⟩, ?_⟩
      have hone := h_pivot_one i.val hi_m hfi
      have hone' : A i ⟨f i.val, by omega⟩ = 1 := by simpa using hone
      rw [hone']
      exact one_ne_zero
  simp [h_eq_sets]

/-- Lemma 3 + Lemma nonzero: rank = number of pivot rows. -/
theorem gaussianRank_eq_matrix_rank (A : Matrix (Fin m) (Fin n) ℚ) :
    ∃ (E : Matrix (Fin m) (Fin m) ℚ), IsUnit E ∧
    ((Finset.filter (λ i : Fin m => ∃ j : Fin n, (E * A) i j ≠ 0) Finset.univ).card = Matrix.rank A) := by
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
    (hp : PivotFun A f jj) (hjj : jj < n) (h_no_pivot : ∀ (i : ℕ) (hi : i < m), f i = jj → A ⟨i, hi⟩ ⟨jj, hjj⟩ = 0) :
    PivotFun A (λ i => if f i = jj then jj + 1 else f i) (jj + 1) := by
  rcases hp with ⟨_, h_bound, h_pivot_one, h_pivot_zero, h_left_zero, h_strict⟩
  let f' := λ i => if f i = jj then jj + 1 else f i
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    dsimp [f']
    by_cases h_eq : f i = jj
    · simp [h_eq]
    · simp [h_eq]
      exact Nat.le_succ_of_le (h_bound i hi)
  · intro i hi hfi
    dsimp [f'] at hfi
    by_cases h_eq : f i = jj
    · simp [h_eq] at hfi
    · have hfi_lt_jj : f i < jj := by
        have hle := h_bound i hi
        omega
      simpa [h_eq] using h_pivot_one i hi hfi_lt_jj
  · intro i i' hi hfi hi' hne
    dsimp [f'] at hfi
    by_cases h_eq : f i = jj
    · simp [h_eq] at hfi
    · have hfi_lt_jj : f i < jj := by
        have hle := h_bound i hi
        omega
      simpa [h_eq] using h_pivot_zero i i' hi hfi_lt_jj hi' hne
  · intro i hi hfi j hj
    by_cases h_eq : f i = jj
    ·
      -- f' i = jj+1. j < jj+1 means j < jj or j = jj.
      -- If j < jj: h_left_zero gives A(i, j) = 0.
      -- If j = jj: by h_no_pivot, A(i, jj) = 0 since f i = jj (unprocessed row).
      by_cases hj_eq_jj : j < jj
      · have hj_old : j < f i := by simpa [h_eq] using hj_eq_jj
        exact h_left_zero i hi (h_bound i hi) j hj_old
      · have hj_val : j = jj := by omega
        subst j
        simpa using h_no_pivot i hi h_eq
    · -- f' i = f i ≠ jj. j < f i. h_left_zero gives 0.
      have hj_old : j < f i := by simpa [h_eq] using hj
      exact h_left_zero i hi (h_bound i hi) j hj_old
  · intro i hi
    dsimp [f']
    -- Need: f'(i) < f'(i+1) or f'(i+1) = jj+1
    have hbound_i := h_bound i (by omega)
    have hbound_i1 := h_bound (i+1) (by omega)
    rcases h_strict i hi with (hlt | heq)
    · -- f i < f (i+1)
      by_cases hfi : f i = jj
      · rw [hfi]
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
lemma columns_induction_produces_pivot_fun (A : Matrix (Fin m) (Fin n) ℚ) :
    ∃ (E : Matrix (Fin m) (Fin m) ℚ) (f : ℕ → ℕ), IsUnit E ∧ PivotFun (E * A) f n := by
  -- Induction on k = 0..n: maintain E_k, f_k such that PivotFun (E_k * A) f_k k.
  -- Base k=0: pivot_fun_init gives PivotFun A (λ _ => 0) 0.
  -- Step k → k+1: let M = E_k * A. If column k has M(i,k) ≠ 0 for some i with f_k(i)=k:
  --   apply pivot_step, update f_{k+1}(i) := k, leave others unchanged.
  --   PivotFun (E_{k+1} * A) f_{k+1} (k+1) holds by AFP lemmas.
  -- If no such i: f_{k+1} = f_k, E_{k+1} = E_k, PivotFun unchanged.
  -- After k = n: done.
  have h_base : ∃ (E : Matrix (Fin m) (Fin m) ℚ) (f : ℕ → ℕ), IsUnit E ∧ PivotFun (E * A) f 0 :=
    ⟨1, λ _ => 0, isUnit_one, by
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi; simp
      · intro i hi hfi; omega
      · intro i i' hi hfi hi' hne; omega
      · intro i hi hfi j hj; omega
      · intro i hi; right; rfl⟩
  refine Nat.rec
    (motive := fun k => k ≤ n →
      ∃ (E : Matrix (Fin m) (Fin m) ℚ) (f : ℕ → ℕ),
        IsUnit E ∧ PivotFun (E * A) f k)
    (fun _ => h_base) (λ k ih => ?_) n le_rfl
  intro hkn
  have hk : k < n := by omega
  rcases ih (by omega) with ⟨E, f, hE, hp⟩
  let M := E * A
  -- f i = k means "unprocessed". Look for i with f i = k and M(i, k) ≠ 0.
  by_cases h_exists : ∃ (i : ℕ) (hi : i < m), f i = k ∧ M ⟨i, hi⟩ ⟨k, hk⟩ ≠ 0
  · rcases h_exists with ⟨i, hi, hfi, hnonzero⟩
    -- Build Ej directly (same construction as pivot_step) so we can use pivot_step_formula
    let s := (M ⟨i, hi⟩ ⟨k, hk⟩)⁻¹
    let i' : Fin m := ⟨i, hi⟩
    let k' : Fin n := ⟨k, hk⟩
    have hs : M i' k' ≠ 0 := hnonzero
    let E1 := FunctionalGaussJordan.scaleRowMat i' s
    let A1 := E1 * M
    let notI := Finset.filter (λ t => t ≠ i') Finset.univ
    let a (t : Fin m) : ℚ := -(A1 t k')
    let E2 : Matrix (Fin m) (Fin m) ℚ := 1 + Finset.sum notI (λ t => a t • stdBasisMatrix t i' 1)
    let Ej := E2 * E1
    have hEj : IsUnit Ej := by
      -- Same proof as pivot_step
      let E2inv : Matrix (Fin m) (Fin m) ℚ := 1 + Finset.sum notI (λ t => (-a t) • stdBasisMatrix t i' 1)
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
    have h_zero_col : ∀ (t : Fin m), t ≠ i' → (Ej * M) t k' = 0 := by
      intro t ht
      dsimp [Ej, E2, E1, A1, a, s]
      simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Finset.sum_apply,
        ht, stdBasisMatrix_mul_entry_row_i, stdBasisMatrix_mul_entry_row_k ht M k']
      ring
    let f' : ℕ → ℕ := λ r => if r = i then k else (if f r = k then k + 1 else f r)
    have hp' : PivotFun (Ej * M) f' (k + 1) := by
      rcases hp with ⟨_, h_bound, h_pivot_one, h_pivot_zero, h_left_zero, h_strict⟩
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
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

end FinitePivotCorridor
-/

/-! ## Verified executable owner -/

theorem gaussian_elimination_preserves_rank
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix.rank (MatrixGaussJordan.gaussJordanElim A).1 = Matrix.rank A :=
  MatrixGaussJordan.gaussJordanElim_preserves_rank A

end DAG.GaussianElimination
