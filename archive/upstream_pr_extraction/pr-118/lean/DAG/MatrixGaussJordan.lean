import Mathlib
import DAG.FunctionalGaussJordan
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix

set_option maxHeartbeats 400000

namespace DAG.MatrixGaussJordan

variable {m n : ℕ}

def findPivot (A : Matrix (Fin m) (Fin n) ℚ) (startRow : ℕ) (j : Fin n) : Option (Fin m) :=
  (Finset.filter (λ (i : Fin m) => A i j ≠ 0 ∧ (i.val : ℕ) ≥ startRow) Finset.univ).min

lemma findPivot_spec (A : Matrix (Fin m) (Fin n) ℚ) (startRow : ℕ) (j : Fin n) {i : Fin m}
    (h : findPivot A startRow j = some i) :
    A i j ≠ 0 ∧ startRow ≤ i.val := by
  classical
  let s : Finset (Fin m) :=
    Finset.filter (fun k : Fin m => A k j ≠ 0 ∧ startRow ≤ k.val) Finset.univ
  have hs : s.Nonempty := by
    by_contra hs0
    have htop : s.min = ⊤ :=
      Finset.min_eq_top.mpr (Finset.not_nonempty_iff_eq_empty.mp hs0)
    simpa [findPivot, s, htop] using h
  have hmem : s.min' hs ∈ s := Finset.min'_mem s hs
  have hmin : s.min = some i := by simpa [findPivot, s] using h
  have hi : s.min' hs = i := by
    apply WithTop.coe_eq_coe.mp
    rw [Finset.coe_min' hs]
    exact hmin
  rw [hi] at hmem
  simpa [s, Finset.mem_filter] using hmem

lemma findPivot_none_spec
    (A : Matrix (Fin m) (Fin n) ℚ) (startRow : ℕ) (j : Fin n)
    (h : findPivot A startRow j = none) :
    ∀ i : Fin m, startRow ≤ i.val → A i j = 0 := by
  classical
  intro i hi
  by_contra hA
  let s : Finset (Fin m) :=
    Finset.filter (fun k : Fin m => A k j ≠ 0 ∧ startRow ≤ k.val) Finset.univ
  have his : i ∈ s := by
    simp [s, hA, hi]
  have hs : s.Nonempty := ⟨i, his⟩
  have hmin : some (s.min' hs) = s.min := by
    simpa using (Finset.coe_min' hs)
  have hfind : findPivot A startRow j = some (s.min' hs) := by
    simpa [findPivot, s] using hmin.symm
  exact Option.some_ne_none _ (hfind.symm.trans h)

lemma findPivot_eq_none_iff
    (A : Matrix (Fin m) (Fin n) ℚ) (startRow : ℕ) (j : Fin n) :
    findPivot A startRow j = none ↔
      ∀ i : Fin m, startRow ≤ i.val → A i j = 0 := by
  constructor
  · exact findPivot_none_spec A startRow j
  · intro hzero
    cases hfind : findPivot A startRow j with
    | none => rfl
    | some i =>
        have hi := findPivot_spec A startRow j hfind
        exact (hi.1 (hzero i hi.2)).elim

lemma swap_selected_pivot_ne_zero
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow : ℕ} {j : Fin n} {pi : Fin m}
    (hrow : pivotRow < m)
    (hpivot : findPivot A pivotRow j = some pi) :
    let pr : Fin m := ⟨pivotRow, hrow⟩
    let A₁ := FunctionalGaussJordan.swapRowsMat pr pi * A
    A₁ pr j ≠ 0 := by
  let pr : Fin m := ⟨pivotRow, hrow⟩
  let A₁ := FunctionalGaussJordan.swapRowsMat pr pi * A
  have hpi := (findPivot_spec A pivotRow j hpivot).1
  dsimp [A₁, FunctionalGaussJordan.swapRowsMat]
  rw [Matrix.mul_apply]
  simp [PEquiv.toMatrix_apply, hpi]

lemma selected_pivotVal_ne_zero
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (hcol : col < n)
    {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    let pr : Fin m := ⟨pivotRow, hrow⟩
    let A₁ :=
      FunctionalGaussJordan.swapRowsMat pr pi * A
    A₁ pr ⟨col, hcol⟩ ≠ 0 :=
  swap_selected_pivot_ne_zero hrow hfind

noncomputable def gaussJordanElimFull.go (A : Matrix (Fin m) (Fin n) ℚ) (pivotRow : ℕ) (col : ℕ)
    (Es : List (Matrix (Fin m) (Fin m) ℚ)) :
    Matrix (Fin m) (Fin n) ℚ × ℕ × List (Matrix (Fin m) (Fin m) ℚ) :=
  if hcol : col < n then
    let j : Fin n := ⟨col, hcol⟩
    match findPivot A pivotRow j with
    | none => go A pivotRow (col + 1) Es
    | some pi =>
        if hpr : pivotRow < m then
          let pr : Fin m := ⟨pivotRow, hpr⟩
          let Eswap := FunctionalGaussJordan.swapRowsMat pr pi
          let A1 := Eswap * A
          let pivotVal := A1 pr j
          if hpv : pivotVal ≠ 0 then
            let Escale := FunctionalGaussJordan.scaleRowMat pr (pivotVal⁻¹)
            let A2 := Escale * A1
            let Elims := (Finset.filter (λ k => k ≠ pr) Finset.univ).toList.map
              (λ k => FunctionalGaussJordan.addRowMat k pr (-(A2 k j)))
            let A3 := (Elims.foldr (· * ·) 1) * A2
            go A3 (pivotRow + 1) (col + 1) (Elims ++ [Escale, Eswap] ++ Es)
          else go A1 (pivotRow + 1) (col + 1) (Eswap :: Es)
        else (A, pivotRow, Es)
  else (A, pivotRow, Es)
termination_by n - col
decreasing_by all_goals exact Nat.sub_succ_lt_self n col hcol

noncomputable def eliminationMatrices
    (A₂ : Matrix (Fin m) (Fin n) ℚ)
    (pr : Fin m)
    (j : Fin n) :
    List (Matrix (Fin m) (Fin m) ℚ) :=
  (Finset.filter (fun k => k ≠ pr) Finset.univ).toList.map
    (fun k =>
      FunctionalGaussJordan.addRowMat k pr (-(A₂ k j)))

noncomputable def selectedPivotStep
    (A : Matrix (Fin m) (Fin n) ℚ)
    (pivotRow col : ℕ)
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    (pi : Fin m)
    (hrow : pivotRow < m) :
    Matrix (Fin m) (Fin n) ℚ ×
      List (Matrix (Fin m) (Fin m) ℚ) :=
  let j : Fin n := ⟨col, hcol⟩
  let pr : Fin m := ⟨pivotRow, hrow⟩
  let Eswap := FunctionalGaussJordan.swapRowsMat pr pi
  let A₁ := Eswap * A
  let pivotVal := A₁ pr j
  let Escale :=
    FunctionalGaussJordan.scaleRowMat pr pivotVal⁻¹
  let A₂ := Escale * A₁
  let Elims := eliminationMatrices A₂ pr j
  let A₃ := Elims.foldr (· * ·) 1 * A₂
  (A₃, Elims ++ [Escale, Eswap] ++ Es)

lemma gaussJordanElimFull_go_selected_pivot
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    gaussJordanElimFull.go A pivotRow col Es =
      let step := selectedPivotStep A pivotRow col Es hcol pi hrow
      gaussJordanElimFull.go step.1 (pivotRow + 1) (col + 1) step.2 := by
  conv_lhs =>
    unfold gaussJordanElimFull.go
  rw [dif_pos hcol]
  dsimp only
  simp only [hfind]
  rw [dif_pos hrow]
  have hpv := selected_pivotVal_ne_zero hcol hfind hrow
  rw [dif_pos hpv]
  rfl

lemma gaussJordanElimFull_go_no_pivot
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = none) :
    gaussJordanElimFull.go A pivotRow col Es =
      gaussJordanElimFull.go A pivotRow (col + 1) Es := by
  conv_lhs =>
    unfold gaussJordanElimFull.go
  rw [dif_pos hcol]
  dsimp only
  simp only [hfind]

lemma gaussJordanElimFull_go_col_exhausted
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : n ≤ col) :
    gaussJordanElimFull.go A pivotRow col Es =
      (A, pivotRow, Es) := by
  conv_lhs =>
    unfold gaussJordanElimFull.go
  rw [dif_neg (Nat.not_lt.mpr hcol)]

lemma gaussJordanElimFull_go_induction
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (P : Matrix (Fin m) (Fin n) ℚ → ℕ → ℕ →
      List (Matrix (Fin m) (Fin m) ℚ) → Prop)
    (hstop : ∀ (X) (r c) (ops), n ≤ c → P X r c ops)
    (hnone : ∀ (X) (r c) (ops) (hc : c < n),
      findPivot X r ⟨c, hc⟩ = none →
      P X r (c + 1) ops → P X r c ops)
    (hrowex : ∀ (X) (r c) (ops) (hc : c < n) (pi),
      findPivot X r ⟨c, hc⟩ = some pi →
      m ≤ r → P X r c ops)
    (hsome : ∀ (X) (r c) (ops) (hc : c < n) (pi) (hr : r < m),
      findPivot X r ⟨c, hc⟩ = some pi →
      P (selectedPivotStep X r c ops hc pi hr).1 (r + 1) (c + 1)
        (selectedPivotStep X r c ops hc pi hr).2 →
      P X r c ops) :
    P A pivotRow col Es := by
  induction h : n - col using Nat.strong_induction_on generalizing A pivotRow col Es with
  | h k ih =>
    by_cases hc : col < n
    · by_cases hf : ∃ pi, findPivot A pivotRow ⟨col, hc⟩ = some pi
      · obtain ⟨pi, hpi⟩ := hf
        by_cases hr : pivotRow < m
        · apply hsome A pivotRow col Es hc pi hr hpi
          have hmeasure : n - (col + 1) < k := by omega
          apply ih (n - (col + 1)) hmeasure
          rfl
        · exact hrowex A pivotRow col Es hc pi hpi (Nat.not_lt.mp hr)
      · have hnone' : findPivot A pivotRow ⟨col, hc⟩ = none := by
          cases hfp : findPivot A pivotRow ⟨col, hc⟩ with
          | none => simpa using hfp
          | some pi => exact (hf ⟨pi, hfp⟩).elim
        apply hnone A pivotRow col Es hc hnone'
        have hmeasure : n - (col + 1) < k := by omega
        apply ih (n - (col + 1)) hmeasure
        rfl
    · exact hstop A pivotRow col Es (Nat.not_lt.mp hc)

noncomputable def gaussJordanElimFull.pivotHistory
    (A : Matrix (Fin m) (Fin n) ℚ)
    (pivotRow col : ℕ)
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (P : List (Fin m × Fin n)) : List (Fin m × Fin n) :=
  if hcol : col < n then
    let j : Fin n := ⟨col, hcol⟩
    match findPivot A pivotRow j with
    | none => pivotHistory A pivotRow (col + 1) Es P
    | some pi =>
        if hpr : pivotRow < m then
          let pr : Fin m := ⟨pivotRow, hpr⟩
          let Eswap := FunctionalGaussJordan.swapRowsMat pr pi
          let A1 := Eswap * A
          let pivotVal := A1 pr j
          if hpv : pivotVal ≠ 0 then
            let Escale := FunctionalGaussJordan.scaleRowMat pr pivotVal⁻¹
            let A2 := Escale * A1
            let Elims := eliminationMatrices A2 pr j
            let A3 := Elims.foldr (· * ·) 1 * A2
            pivotHistory A3 (pivotRow + 1) (col + 1)
              (Elims ++ [Escale, Eswap] ++ Es) (P ++ [(pr, j)])
          else
            pivotHistory A1 (pivotRow + 1) (col + 1) (Eswap :: Es) P
        else P
  else P
termination_by n - col
decreasing_by
  all_goals exact Nat.sub_succ_lt_self n col ‹col < n›

structure PivotTraceState (m n : ℕ) where
  matrix : Matrix (Fin m) (Fin n) ℚ
  pivotRow : ℕ
  operations : List (Matrix (Fin m) (Fin m) ℚ)
  pivots : List (Fin m × Fin n)

noncomputable def gaussJordanElimFull.withPivotTrace
    (A : Matrix (Fin m) (Fin n) ℚ)
    (pivotRow col : ℕ)
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (P : List (Fin m × Fin n)) : PivotTraceState m n :=
  let out := gaussJordanElimFull.go A pivotRow col Es
  { matrix := out.1
    pivotRow := out.2.1
    operations := out.2.2
    pivots := gaussJordanElimFull.pivotHistory A pivotRow col Es P }

lemma withPivotTrace_projection
    (A : Matrix (Fin m) (Fin n) ℚ)
    (pivotRow col : ℕ)
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (P : List (Fin m × Fin n)) :
    (gaussJordanElimFull.withPivotTrace A pivotRow col Es P).matrix =
        (gaussJordanElimFull.go A pivotRow col Es).1 ∧
      (gaussJordanElimFull.withPivotTrace A pivotRow col Es P).pivotRow =
        (gaussJordanElimFull.go A pivotRow col Es).2.1 ∧
      (gaussJordanElimFull.withPivotTrace A pivotRow col Es P).operations =
        (gaussJordanElimFull.go A pivotRow col Es).2.2 := by
  constructor
  · rfl
  constructor <;> rfl

lemma pivotHistory_no_pivot_eq
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (P : List (Fin m × Fin n))
    (hcol : col < n)
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = none) :
    gaussJordanElimFull.pivotHistory A pivotRow col Es P =
      gaussJordanElimFull.pivotHistory A pivotRow (col + 1) Es P := by
  conv_lhs =>
    unfold gaussJordanElimFull.pivotHistory
  rw [dif_pos hcol]
  dsimp only
  rw [hfind]

lemma pivotHistory_selected_pivot_eq
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (P : List (Fin m × Fin n))
    (hcol : col < n)
    {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    gaussJordanElimFull.pivotHistory A pivotRow col Es P =
      let step := selectedPivotStep A pivotRow col Es hcol pi hrow
      gaussJordanElimFull.pivotHistory step.1 (pivotRow + 1) (col + 1) step.2
        (P ++ [((⟨pivotRow, hrow⟩ : Fin m), (⟨col, hcol⟩ : Fin n))]) := by
  conv_lhs =>
    unfold gaussJordanElimFull.pivotHistory
  rw [dif_pos hcol]
  dsimp only
  rw [hfind]
  simp only
  rw [dif_pos hrow]
  have hpv := swap_selected_pivot_ne_zero hrow hfind
  rw [dif_pos hpv]
  rfl

lemma pivotHistory_row_exhausted_eq
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (P : List (Fin m × Fin n))
    (hcol : col < n)
    {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : m ≤ pivotRow) :
    gaussJordanElimFull.pivotHistory A pivotRow col Es P = P := by
  conv_lhs =>
    unfold gaussJordanElimFull.pivotHistory
  rw [dif_pos hcol]
  dsimp only
  rw [hfind]
  simp only [dif_neg (Nat.not_lt.mpr hrow)]

lemma pivotHistory_col_exhausted_eq
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (P : List (Fin m × Fin n))
    (hcol : n ≤ col) :
    gaussJordanElimFull.pivotHistory A pivotRow col Es P = P := by
  conv_lhs =>
    unfold gaussJordanElimFull.pivotHistory
  rw [dif_neg (Nat.not_lt.mpr hcol)]

lemma go_selected_pivot_eq
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    gaussJordanElimFull.go A pivotRow col Es =
      let j : Fin n := ⟨col, hcol⟩
      let pr : Fin m := ⟨pivotRow, hrow⟩
      let Eswap := FunctionalGaussJordan.swapRowsMat pr pi
      let A₁ := Eswap * A
      let pivotVal := A₁ pr j
      let Escale :=
        FunctionalGaussJordan.scaleRowMat pr pivotVal⁻¹
      let A₂ := Escale * A₁
      let Elims :=
        (Finset.filter (fun k => k ≠ pr) Finset.univ).toList.map
          (fun k =>
            FunctionalGaussJordan.addRowMat k pr (-(A₂ k j)))
      let A₃ := Elims.foldr (· * ·) 1 * A₂
      gaussJordanElimFull.go
        A₃
        (pivotRow + 1)
        (col + 1)
        (Elims ++ [Escale, Eswap] ++ Es) := by
  rw [gaussJordanElimFull.go, dif_pos hcol]
  simp only
  rw [hfind]
  simp only
  rw [dif_pos hrow]
  have hpv :
      let pr : Fin m := ⟨pivotRow, hrow⟩
      let A₁ :=
        FunctionalGaussJordan.swapRowsMat pr pi * A
      A₁ pr ⟨col, hcol⟩ ≠ 0 :=
    selected_pivotVal_ne_zero hcol hfind hrow
  rw [dif_pos hpv]

lemma go_selected_pivot_step_eq
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    gaussJordanElimFull.go A pivotRow col Es =
      let step := selectedPivotStep A pivotRow col Es hcol pi hrow
      gaussJordanElimFull.go
        step.1
        (pivotRow + 1)
        (col + 1)
        step.2 := by
  simpa [selectedPivotStep] using
    (go_selected_pivot_eq (A := A) (pivotRow := pivotRow)
      (col := col) Es hcol hfind hrow)

lemma go_no_pivot_eq
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = none) :
    gaussJordanElimFull.go A pivotRow col Es =
      gaussJordanElimFull.go A pivotRow (col + 1) Es := by
  rw [gaussJordanElimFull.go, dif_pos hcol]
  simp only
  rw [hfind]

lemma go_no_pivot_column_zero
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = none) :
    (∀ i : Fin m,
      pivotRow ≤ i.val → A i ⟨col, hcol⟩ = 0) ∧
    gaussJordanElimFull.go A pivotRow col Es =
      gaussJordanElimFull.go A pivotRow (col + 1) Es := by
  constructor
  · exact (findPivot_eq_none_iff A pivotRow ⟨col, hcol⟩).mp hfind
  · exact go_no_pivot_eq Es hcol hfind

lemma go_col_ge_eq
    (A : Matrix (Fin m) (Fin n) ℚ)
    (pivotRow col : ℕ)
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : n ≤ col) :
    gaussJordanElimFull.go A pivotRow col Es =
      (A, pivotRow, Es) := by
  rw [gaussJordanElimFull.go, dif_neg (Nat.not_lt.mpr hcol)]

lemma go_row_exhausted_eq
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : m ≤ pivotRow) :
    gaussJordanElimFull.go A pivotRow col Es =
      (A, pivotRow, Es) := by
  rw [gaussJordanElimFull.go, dif_pos hcol]
  simp only
  rw [hfind]
  simp only
  rw [dif_neg (Nat.not_lt.mpr hrow)]

lemma scale_selected_pivot_eq_one
    {A₁ : Matrix (Fin m) (Fin n) ℚ}
    {j : Fin n} {pivotVal : ℚ}
    {pr : Fin m}
    (hval : pivotVal = A₁ pr j)
    (hpv : pivotVal ≠ 0) :
    (FunctionalGaussJordan.scaleRowMat pr (pivotVal⁻¹) * A₁) pr j = 1 := by
  classical
  rw [Matrix.mul_apply]
  simp only [FunctionalGaussJordan.scaleRowMat, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single pr]
  · simp only [if_true, true_and, smul_eq_mul, mul_one]
    rw [← hval]
    calc
      (1 + (pivotVal⁻¹ - 1)) * pivotVal = pivotVal⁻¹ * pivotVal := by ring
      _ = 1 := inv_mul_cancel₀ hpv
  · intro b hb hbp
    simp [hbp, hbp.symm]
  · intro hnot
    exact (hnot (Finset.mem_univ pr)).elim

lemma addRowMat_preserves_source_row
    {X : Matrix (Fin m) (Fin n) ℚ}
    {k pr : Fin m} (hkp : k ≠ pr) (c : ℚ) (j : Fin n) :
    (FunctionalGaussJordan.addRowMat k pr c * X) pr j = X pr j := by
  classical
  simp only [FunctionalGaussJordan.addRowMat, Matrix.mul_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.single_apply]
  rw [Finset.sum_eq_single pr]
  · simp [hkp]
  · intro b hb hbp
    simp [hbp, hbp.symm]
  · intro hnot
    exact (hnot (Finset.mem_univ pr)).elim

lemma addRowMat_zeros_target_entry
    {X : Matrix (Fin m) (Fin n) ℚ}
    {k pr : Fin m}
    (hkp : k ≠ pr)
    (j : Fin n)
    (hpivot : X pr j = 1) :
    (FunctionalGaussJordan.addRowMat k pr (-(X k j)) * X) k j = 0 := by
  classical
  unfold FunctionalGaussJordan.addRowMat
  rw [Matrix.add_mul]
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single k]
  · simp [hkp, hpivot]
  · intro b hb hbk
    simp [hbk, hbk.symm]
  · intro hnot
    exact (hnot (Finset.mem_univ k)).elim

lemma addRowMat_preserves_other_row
    {X : Matrix (Fin m) (Fin n) ℚ}
    {q pr k : Fin m}
    (hkq : k ≠ q)
    (c : ℚ)
    (j : Fin n) :
    (FunctionalGaussJordan.addRowMat q pr c * X) k j = X k j := by
  classical
  unfold FunctionalGaussJordan.addRowMat
  rw [Matrix.add_mul]
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single k]
  · have hqk : q ≠ k := Ne.symm hkq
    simp [hqk]
  · intro b hb hbk
    simp [hbk, hbk.symm]
  · intro hnot
    exact (hnot (Finset.mem_univ k)).elim

def IsPivotColumnAt
    (A : Matrix (Fin m) (Fin n) ℚ)
    (r : Fin m) (c : Fin n) : Prop :=
  ∀ k : Fin m, A k c = if k = r then 1 else 0

lemma addRowMat_preserves_column_of_source_zero
    {X : Matrix (Fin m) (Fin n) ℚ}
    {q pr : Fin m} {c : Fin n}
    (hsource : X pr c = 0)
    (a : ℚ) :
    ∀ k,
      (FunctionalGaussJordan.addRowMat q pr a * X) k c =
        X k c := by
  intro k
  classical
  unfold FunctionalGaussJordan.addRowMat
  rw [Matrix.add_mul]
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single k]
  · have hqk : q = k ∨ q ≠ k := eq_or_ne q k
    rcases hqk with rfl | hqk
    · simp [hsource]
    · simp [hqk, hsource]
  · intro b hb hbk
    simp [hbk, hbk.symm]
  · intro hnot
    exact (hnot (Finset.mem_univ k)).elim

lemma scaleRowMat_apply_source_row
    {A : Matrix (Fin m) (Fin n) ℚ}
    (pr : Fin m) (c : ℚ) :
    (FunctionalGaussJordan.scaleRowMat pr c * A) pr = c • A pr := by
  funext j
  unfold FunctionalGaussJordan.scaleRowMat
  rw [Matrix.add_mul, Matrix.add_apply, Matrix.one_mul]
  rw [Matrix.smul_mul, Matrix.smul_apply]
  rw [Matrix.single_mul_apply_same]
  simp only [one_mul, smul_eq_mul, Pi.smul_apply]
  ring

lemma scaleRowMat_preserves_pivot_column
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pr oldRow : Fin m} {oldCol : Fin n}
    (hpr : pr ≠ oldRow)
    (hold : IsPivotColumnAt A oldRow oldCol)
    (c : ℚ) :
    IsPivotColumnAt
      (FunctionalGaussJordan.scaleRowMat pr c * A)
      oldRow oldCol := by
  intro k
  classical
  unfold FunctionalGaussJordan.scaleRowMat
  rw [Matrix.mul_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.single_apply]
  rw [Finset.sum_eq_single k]
  · by_cases hkp : k = pr
    · subst k
      have hzero : A pr oldCol = 0 := by
        have h := hold pr
        rw [if_neg hpr] at h
        exact h
      simp [hzero, hpr]
    · have hpk : pr ≠ k := Ne.symm hkp
      simpa [hpk] using hold k
  · intro b hb hbk
    by_cases hprb : pr = b
    · subst b
      simp [hbk, hbk.symm]
    · have hkb : k ≠ b := Ne.symm hbk
      simp [hprb, hkb]
  · intro hnot
    exact (hnot (Finset.mem_univ k)).elim

lemma swapRowsMat_preserves_row_entry
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pr pi oldRow : Fin m} {oldCol : Fin n}
    (hpr : oldRow ≠ pr)
    (hpi : oldRow ≠ pi) :
    let E : Matrix (Fin m) (Fin m) ℚ :=
      FunctionalGaussJordan.swapRowsMat pr pi
    (E * A) oldRow oldCol = A oldRow oldCol := by
  dsimp only
  unfold FunctionalGaussJordan.swapRowsMat
  rw [Matrix.mul_apply]
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Equiv.swap_apply_of_ne_of_ne hpr hpi]

lemma swapRowsMat_apply
    {A : Matrix (Fin m) (Fin n) ℚ}
    (pr pi : Fin m) (r : Fin m) (c : Fin n) :
    let B : Matrix (Fin m) (Fin n) ℚ :=
      FunctionalGaussJordan.swapRowsMat pr pi * A
    B r c =
      if r = pr then A pi c
      else if r = pi then A pr c
      else A r c := by
  dsimp only
  unfold FunctionalGaussJordan.swapRowsMat
  rw [Matrix.mul_apply]
  by_cases hpr : r = pr
  · subst r
    simp [Equiv.swap_apply_left]
  · by_cases hpi : r = pi
    · subst r
      simp [Equiv.swap_apply_right, hpr]
    · simp [Equiv.swap_apply_of_ne_of_ne hpr hpi, hpr, hpi]

lemma swap_selected_preserves_old_pivot_column
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m)
    {oldRow : Fin m} {oldCol : Fin n}
    (hold : IsPivotColumnAt A oldRow oldCol)
    (hOldRow : oldRow.val < pivotRow) :
    IsPivotColumnAt
      (FunctionalGaussJordan.swapRowsMat
        ⟨pivotRow, hrow⟩ pi * A)
      oldRow oldCol := by
  let pr : Fin m := ⟨pivotRow, hrow⟩
  have hpi_ge : pivotRow ≤ pi.val :=
    (findPivot_spec A pivotRow ⟨col, hcol⟩ hfind).2
  have hpr : oldRow ≠ pr := by
    intro h
    have : oldRow.val = pivotRow := congrArg Fin.val h
    omega
  have hpi : oldRow ≠ pi := by
    intro h
    have : pi.val = oldRow.val := congrArg Fin.val h.symm
    omega
  intro k
  classical
  unfold FunctionalGaussJordan.swapRowsMat
  rw [PEquiv.toMatrix_mul_apply]
  simp only [Equiv.toPEquiv_apply]
  by_cases hkpr : k = pr
  · subst k
    have hpi_col := hold pi
    rw [if_neg (Ne.symm hpi)] at hpi_col
    simpa [pr, Equiv.swap_apply_left, hpr, Ne.symm hpr] using hpi_col
  · by_cases hkpi : k = pi
    · subst k
      have hpr_col := hold pr
      rw [if_neg (Ne.symm hpr)] at hpr_col
      simpa [pr, Equiv.swap_apply_right, hpi, Ne.symm hpi] using hpr_col
    · have hkswap : (Equiv.swap pr pi) k = k :=
        Equiv.swap_apply_of_ne_of_ne hkpr hkpi
      have hkswap' : (Equiv.swap (⟨pivotRow, hrow⟩ : Fin m) pi) k = k := by
        simpa [pr] using hkswap
      rw [hkswap']
      exact hold k

def FixesRow
    (E : Matrix (Fin m) (Fin m) ℚ)
    (pr : Fin m) : Prop :=
  ∀ (B : Matrix (Fin m) (Fin n) ℚ),
    (E * B) pr = B pr

lemma addRowMat_mul_source_row
    (A : Matrix (Fin m) (Fin n) ℚ)
    (k pr : Fin m)
    (hkp : k ≠ pr)
    (c : ℚ)
    (j : Fin n) :
    (FunctionalGaussJordan.addRowMat k pr c * A) pr j = A pr j := by
  exact addRowMat_preserves_source_row hkp c j

lemma addRowMat_mul_source_row_apply
    (A : Matrix (Fin m) (Fin n) ℚ)
    (k pr : Fin m)
    (hkp : k ≠ pr)
    (c : ℚ) :
    (FunctionalGaussJordan.addRowMat k pr c * A) pr = A pr := by
  funext j
  exact addRowMat_mul_source_row A k pr hkp c j

lemma foldr_mul_fixesRow
    (L : List (Matrix (Fin m) (Fin m) ℚ))
    (pr : Fin m)
    (hL : ∀ E ∈ L, FixesRow (n := n) E pr) :
    FixesRow (n := n) (L.foldr (· * ·) 1) pr := by
  intro B
  induction L with
  | nil =>
      simp [FixesRow]
  | cons E L ih =>
      simp only [List.foldr_cons]
      rw [Matrix.mul_assoc]
      rw [hL E (by simp)]
      apply ih
      intro F hF
      exact hL F (by simp [hF])

lemma elimination_matrices_fix_pivot_row
    (A₂ : Matrix (Fin m) (Fin n) ℚ)
    (pr : Fin m)
    (j : Fin n) :
    ∀ E ∈ eliminationMatrices A₂ pr j, FixesRow (n := n) E pr := by
  intro E hE
  simp only [eliminationMatrices, List.mem_map, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and] at hE
  obtain ⟨k, hk, rfl⟩ := hE
  intro B
  exact addRowMat_mul_source_row_apply B k pr hk (-(A₂ k j))

lemma elimination_fold_preserves_selected_pivot
    (A₂ : Matrix (Fin m) (Fin n) ℚ)
    (pr : Fin m)
    (j : Fin n)
    (hpivot : A₂ pr j = 1) :
    let E : Matrix (Fin m) (Fin m) ℚ :=
      List.foldr (· * ·) 1 (eliminationMatrices A₂ pr j)
    (E * A₂) pr j = 1 := by
  let E : Matrix (Fin m) (Fin m) ℚ :=
    List.foldr (· * ·) 1 (eliminationMatrices A₂ pr j)
  change (E * A₂) pr j = 1
  have hfix := elimination_matrices_fix_pivot_row A₂ pr j
  have hfold := foldr_mul_fixesRow (n := n) _ pr hfix
  rw [congrFun (hfold A₂) j, hpivot]

lemma addRowMat_list_preserves_source_row
    (ks : List (Fin m))
    (pr : Fin m)
    (hks : ∀ k ∈ ks, k ≠ pr)
    (coeff : Fin m → ℚ)
    (X : Matrix (Fin m) (Fin n) ℚ) :
    ∀ col : Fin n,
      let E : Matrix (Fin m) (Fin m) ℚ :=
        (ks.map
          (fun k =>
            FunctionalGaussJordan.addRowMat k pr (coeff k))).foldr
          (· * ·) 1
      (E * X) pr col = X pr col := by
  intro col
  induction ks with
  | nil => simp
  | cons k ks ih =>
      have hk : k ≠ pr := hks k (by simp)
      have hks' : ∀ q ∈ ks, q ≠ pr := by
        intro q hq
        exact hks q (by simp [hq])
      simp only [List.map_cons, List.foldr_cons]
      rw [Matrix.mul_assoc]
      let Erest : Matrix (Fin m) (Fin m) ℚ :=
        (ks.map
          (fun q =>
            FunctionalGaussJordan.addRowMat q pr (coeff q))).foldr
              (· * ·) 1
      have hsource := addRowMat_preserves_source_row
        (X := Erest * X) hk (coeff k) col
      rw [hsource]
      exact ih hks'

lemma elimination_fold_preserves_source_row
    (X : Matrix (Fin m) (Fin n) ℚ)
    (pr : Fin m)
    (j col : Fin n) :
    let Elims :=
      (Finset.filter (fun k => k ≠ pr) Finset.univ).toList.map
        (fun k =>
          FunctionalGaussJordan.addRowMat k pr (-(X k j)))
    let E : Matrix (Fin m) (Fin m) ℚ := Elims.foldr (· * ·) 1
    (E * X) pr col = X pr col := by
  classical
  let ks : List (Fin m) :=
    (Finset.filter (fun k => k ≠ pr) Finset.univ).toList
  have hks : ∀ k ∈ ks, k ≠ pr := by
    intro k hk
    simpa [ks] using
      (Finset.mem_filter.mp (Finset.mem_toList.mp hk)).2
  simpa [ks] using
    addRowMat_list_preserves_source_row
      (pr := pr) ks hks (fun k => -(X k j)) X col

lemma elimination_fold_preserves_source_row_apply
    (X : Matrix (Fin m) (Fin n) ℚ)
    (pr : Fin m) (j : Fin n) :
    let Elims :=
      (Finset.filter (fun k => k ≠ pr) Finset.univ).toList.map
        (fun k =>
          FunctionalGaussJordan.addRowMat k pr (-(X k j)))
    let E : Matrix (Fin m) (Fin m) ℚ := Elims.foldr (· * ·) 1
    (E * X) pr = X pr := by
  funext col
  exact elimination_fold_preserves_source_row X pr j col

lemma scaleRowMat_apply_other_row
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pr i : Fin m} (hpi : i ≠ pr) (c : ℚ) :
    (FunctionalGaussJordan.scaleRowMat pr c * A) i = A i := by
  funext j
  unfold FunctionalGaussJordan.scaleRowMat
  rw [Matrix.add_mul, Matrix.add_apply, Matrix.one_mul]
  rw [Matrix.smul_mul, Matrix.smul_apply]
  rw [Matrix.single_mul_apply_of_ne (1 : ℚ) pr pr i j hpi A]
  simp

lemma swap_scale_preserves_source_zero
    {A : Matrix (Fin m) (Fin n) ℚ}
    (pr pi i : Fin m) (q : Fin n)
    (hi_pr : i ≠ pr) (hi_pi : i ≠ pi)
    (hsource : A pi q = 0) (htarget : A i q = 0)
    (c : ℚ) :
    let A₁ : Matrix (Fin m) (Fin n) ℚ :=
      FunctionalGaussJordan.swapRowsMat pr pi * A
    let A₂ : Matrix (Fin m) (Fin n) ℚ :=
      FunctionalGaussJordan.scaleRowMat pr c * A₁
    A₂ i q = 0 ∧ A₂ pr q = c * A pi q := by
  let A₁ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.swapRowsMat pr pi * A
  let A₂ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.scaleRowMat pr c * A₁
  have hswap_i : A₁ i q = A i q := by
    simpa [A₁] using swapRowsMat_preserves_row_entry hi_pr hi_pi
  have hscale_i : A₂ i q = A₁ i q := by
    have h := scaleRowMat_apply_other_row (A := A₁) hi_pr c
    exact congrFun h q
  have hswap_pr : A₁ pr q = A pi q := by
    simpa [A₁] using swapRowsMat_apply pr pi pr q
  have hscale_pr : A₂ pr q = c * A₁ pr q := by
    have h := scaleRowMat_apply_source_row (A := A₁) pr c
    exact congrFun h q
  constructor
  · change A₂ i q = 0
    rw [hscale_i, hswap_i, htarget]
  · change A₂ pr q = c * A pi q
    rw [hscale_pr, hswap_pr]

lemma selectedPivotStep_active_row
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    let step := selectedPivotStep A pivotRow col Es hcol pi hrow
    let pr : Fin m := ⟨pivotRow, hrow⟩
    let j : Fin n := ⟨col, hcol⟩
    let A₁ := FunctionalGaussJordan.swapRowsMat pr pi * A
    let pivotVal := A₁ pr j
    step.1 pr = pivotVal⁻¹ • A₁ pr := by
  let pr : Fin m := ⟨pivotRow, hrow⟩
  let j : Fin n := ⟨col, hcol⟩
  let A₁ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.swapRowsMat pr pi * A
  let pivotVal : ℚ := A₁ pr j
  let A₂ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.scaleRowMat pr pivotVal⁻¹ * A₁
  let Elims := eliminationMatrices A₂ pr j
  let E : Matrix (Fin m) (Fin m) ℚ := Elims.foldr (· * ·) 1
  have helim : (E * A₂) pr = A₂ pr := by
    simpa [Elims] using elimination_fold_preserves_source_row_apply A₂ pr j
  have hscale : A₂ pr = pivotVal⁻¹ • A₁ pr := by
    simpa [A₂] using scaleRowMat_apply_source_row pr pivotVal⁻¹
  simpa [selectedPivotStep, pr, j, A₁, pivotVal, A₂, Elims, E] using
    helim.trans hscale

lemma selectedPivotStep_active_row_left_zero
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m)
    {q : Fin n} (hq : q.val < col)
    (hsource : A pi q = 0) :
    (selectedPivotStep A pivotRow col Es hcol pi hrow).1
      ⟨pivotRow, hrow⟩ q = 0 := by
  let pr : Fin m := ⟨pivotRow, hrow⟩
  let j : Fin n := ⟨col, hcol⟩
  let A₁ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.swapRowsMat pr pi * A
  let pivotVal : ℚ := A₁ pr j
  have hrow_eq := selectedPivotStep_active_row
    (A := A) Es hcol hfind hrow
  have hpoint := congrFun hrow_eq q
  have hswap : A₁ pr q = A pi q := by
    simpa [A₁] using swapRowsMat_apply pr pi pr q
  have hscaled :
      (pivotVal⁻¹ • A₁ pr) q = pivotVal⁻¹ * A pi q := by
    rw [Pi.smul_apply, hswap]
    rfl
  rw [hpoint, hscaled, hsource]
  simp

lemma elimination_fold_preserves_pivot_one
    (X : Matrix (Fin m) (Fin n) ℚ)
    (pr : Fin m)
    (j : Fin n)
    (hpivot : X pr j = 1) :
    let Elims :=
      (Finset.filter (fun k => k ≠ pr) Finset.univ).toList.map
        (fun k =>
          FunctionalGaussJordan.addRowMat k pr (-(X k j)))
    let E : Matrix (Fin m) (Fin m) ℚ := Elims.foldr (· * ·) 1
    (E * X) pr j = 1 := by
  dsimp only
  rw [elimination_fold_preserves_source_row X pr j j]
  exact hpivot

lemma selectedPivotStep_pivot_eq_one
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    (selectedPivotStep A pivotRow col Es hcol pi hrow).1
        ⟨pivotRow, hrow⟩
        ⟨col, hcol⟩ = 1 := by
  let j : Fin n := ⟨col, hcol⟩
  let pr : Fin m := ⟨pivotRow, hrow⟩
  let Eswap : Matrix (Fin m) (Fin m) ℚ :=
    FunctionalGaussJordan.swapRowsMat pr pi
  let A₁ : Matrix (Fin m) (Fin n) ℚ := Eswap * A
  let pivotVal : ℚ := A₁ pr j
  let Escale : Matrix (Fin m) (Fin m) ℚ :=
    FunctionalGaussJordan.scaleRowMat pr pivotVal⁻¹
  let A₂ : Matrix (Fin m) (Fin n) ℚ := Escale * A₁
  have hpv : pivotVal ≠ 0 := by
    simpa only [pivotVal, A₁, Eswap, pr, j] using
      selected_pivotVal_ne_zero hcol hfind hrow
  have hscaled : A₂ pr j = 1 := by
    exact scale_selected_pivot_eq_one (A₁ := A₁) (j := j)
      (pivotVal := pivotVal) (pr := pr) rfl hpv
  have helim :
      let Elims := eliminationMatrices A₂ pr j
      let A₃ := Elims.foldr (· * ·) 1 * A₂
      A₃ pr j = 1 :=
    elimination_fold_preserves_selected_pivot A₂ pr j hscaled
  simpa [selectedPivotStep, eliminationMatrices, j, pr, Eswap,
    A₁, pivotVal, Escale, A₂] using helim

lemma addRowMat_list_preserves_absent_row
    (ks : List (Fin m))
    (pr k : Fin m)
    (hks : ∀ q ∈ ks, q ≠ pr)
    (hnot : k ∉ ks)
    (coeff : Fin m → ℚ)
    (X : Matrix (Fin m) (Fin n) ℚ)
    (j : Fin n) :
    let E : Matrix (Fin m) (Fin m) ℚ :=
      (ks.map
        (fun q =>
          FunctionalGaussJordan.addRowMat q pr (coeff q))).foldr
        (· * ·) 1
    (E * X) k j = X k j := by
  induction ks with
  | nil => simp
  | cons q qs ih =>
      have hkq : k ≠ q := by
        intro h
        apply hnot
        simp [h]
      have hnot' : k ∉ qs := by
        intro hq
        apply hnot
        simp [hq]
      have hqs : ∀ r ∈ qs, r ≠ pr := by
        intro r hr
        exact hks r (by simp [hr])
      simp only [List.map_cons, List.foldr_cons]
      rw [Matrix.mul_assoc]
      rw [addRowMat_preserves_other_row (X := _) hkq (coeff q) j]
      exact ih hqs hnot'

lemma addRowMat_list_preserves_column_of_source_zero
    (ks : List (Fin m))
    (pr : Fin m)
    (hks : ∀ q ∈ ks, q ≠ pr)
    (coeff : Fin m → ℚ)
    (X : Matrix (Fin m) (Fin n) ℚ)
    (c : Fin n)
    (hsource : X pr c = 0) :
    let E : Matrix (Fin m) (Fin m) ℚ :=
      (ks.map
        (fun q => FunctionalGaussJordan.addRowMat q pr (coeff q))).foldr
        (· * ·) 1
    ∀ k, (E * X) k c = X k c := by
  induction ks with
  | nil =>
      dsimp
      intro k
      simp
  | cons q qs ih =>
      have hqpr : q ≠ pr := hks q (by simp)
      have hqs : ∀ r ∈ qs, r ≠ pr := by
        intro r hr
        exact hks r (by simp [hr])
      have hsource_tail := addRowMat_list_preserves_source_row
        qs pr hqs coeff X c
      dsimp only at hsource_tail
      let Erest : Matrix (Fin m) (Fin m) ℚ :=
        (qs.map
          (fun r => FunctionalGaussJordan.addRowMat r pr (coeff r))).foldr
          (· * ·) 1
      have hsource_tail_zero :
          (Erest * X) pr c = 0 := by
        have hsource_tail' := hsource_tail
        change (Erest * X) pr c = X pr c at hsource_tail'
        rw [hsource_tail', hsource]
      have htail := ih hqs
      dsimp only at htail
      dsimp only
      intro k
      simp only [List.map_cons, List.foldr_cons]
      rw [Matrix.mul_assoc]
      rw [addRowMat_preserves_column_of_source_zero
        (X := Erest * X)
        hsource_tail_zero (coeff q) k]
      have htail' : (Erest * X) k c = X k c := by
        change (Erest * X) k c = X k c
        exact htail k
      exact htail'

lemma addRowMat_list_apply
    (ks : List (Fin m))
    (pr : Fin m)
    (hks : ∀ q ∈ ks, q ≠ pr)
    (hnd : ks.Nodup)
    (X : Matrix (Fin m) (Fin n) ℚ)
    (j : Fin n)
    (hpivot : X pr j = 1)
    (k : Fin m) :
    let Etotal : Matrix (Fin m) (Fin m) ℚ :=
      (ks.map
        (fun q =>
          FunctionalGaussJordan.addRowMat q pr (-(X q j)))).foldr
        (· * ·) 1
    (Etotal * X) k j = if k ∈ ks then 0 else X k j := by
  induction ks with
  | nil => simp
  | cons q qs ih =>
      have hqpr : q ≠ pr := hks q (by simp)
      have hqs : ∀ r ∈ qs, r ≠ pr := by
        intro r hr
        exact hks r (by simp [hr])
      have hndqs : qs.Nodup := hnd.of_cons
      simp only [List.map_cons, List.foldr_cons]
      rw [Matrix.mul_assoc]
      by_cases hkq : k = q
      · subst k
        have hnot : q ∉ qs := by
          intro hq
          exact (List.nodup_cons.mp hnd).1 hq
        have htail := addRowMat_list_preserves_absent_row
          qs pr q hqs hnot (fun r => -(X r j)) X j
        dsimp only at htail
        let Erest : Matrix (Fin m) (Fin m) ℚ :=
          List.foldr (fun E F => E * F) 1
            (qs.map (fun r =>
              FunctionalGaussJordan.addRowMat r pr (-(X r j))))
        have hsource := addRowMat_list_preserves_source_row
          qs pr hqs (fun r => -(X r j)) X j
        dsimp only at hsource
        have htarget := addRowMat_zeros_target_entry
          (X := Erest * X) hqpr j
          (by rw [hsource, hpivot])
        simpa [Erest, htail] using htarget
      · have htarget := ih hqs hndqs
        dsimp only at htarget
        rw [addRowMat_preserves_other_row
          (X := _) hkq (-(X q j)) j]
        simpa [hkq] using htarget

lemma elimination_fold_preserves_column_of_source_zero
    (X : Matrix (Fin m) (Fin n) ℚ)
    (pr : Fin m)
    (pivotCol oldCol : Fin n)
    (hsource : X pr oldCol = 0) :
    let E : Matrix (Fin m) (Fin m) ℚ :=
      (eliminationMatrices X pr pivotCol).foldr (· * ·) 1
    ∀ k, (E * X) k oldCol = X k oldCol := by
  classical
  let ks : List (Fin m) :=
    (Finset.filter (fun q => q ≠ pr) Finset.univ).toList
  have hks : ∀ q ∈ ks, q ≠ pr := by
    intro q hq
    simpa [ks] using
      (Finset.mem_filter.mp (Finset.mem_toList.mp hq)).2
  dsimp only
  simpa [eliminationMatrices, ks] using
    addRowMat_list_preserves_column_of_source_zero
      ks pr hks (fun q => -(X q pivotCol)) X oldCol hsource

lemma selectedPivotStep_preserves_old_left_zero
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m)
    {oldRow : Fin m} {oldCol : Fin n}
    (hOldRow : oldRow.val < pivotRow)
    (hold : A oldRow oldCol = 0)
    (hsource : A pi oldCol = 0) :
    (selectedPivotStep A pivotRow col Es hcol pi hrow).1
      oldRow oldCol = 0 := by
  let j : Fin n := ⟨col, hcol⟩
  let pr : Fin m := ⟨pivotRow, hrow⟩
  let A₁ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.swapRowsMat pr pi * A
  let pivotVal : ℚ := A₁ pr j
  let A₂ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.scaleRowMat pr pivotVal⁻¹ * A₁
  have hpi_ge : pivotRow ≤ pi.val :=
    (findPivot_spec A pivotRow j hfind).2
  have hOld_pr : oldRow ≠ pr := by
    intro h
    have hv := congrArg Fin.val h
    have hlt : oldRow.val < pr.val := by
      simpa [pr] using hOldRow
    exact (Nat.ne_of_lt hlt) hv
  have hOld_pi : oldRow ≠ pi := by
    intro h
    have hv := congrArg Fin.val h
    have hlt : oldRow.val < pi.val := lt_of_lt_of_le hOldRow hpi_ge
    exact (Nat.ne_of_lt hlt) hv
  have hswap : A₁ oldRow oldCol = A oldRow oldCol := by
    simpa [A₁] using swapRowsMat_preserves_row_entry hOld_pr hOld_pi
  have hscale : A₂ oldRow oldCol = A₁ oldRow oldCol := by
    have h := scaleRowMat_apply_other_row (A := A₁) hOld_pr pivotVal⁻¹
    exact congrFun h oldCol
  have hsource₂ : A₂ pr oldCol = 0 := by
    have hswap_pr : A₁ pr oldCol = A pi oldCol := by
      simpa [A₁] using swapRowsMat_apply pr pi pr oldCol
    have hscale_pr : A₂ pr oldCol = pivotVal⁻¹ * A₁ pr oldCol := by
      have h := scaleRowMat_apply_source_row (A := A₁) pr pivotVal⁻¹
      exact congrFun h oldCol
    rw [hscale_pr, hswap_pr, hsource]
    simp
  have htarget₂ : A₂ oldRow oldCol = 0 := by
    rw [hscale, hswap, hold]
  have hfold := elimination_fold_preserves_column_of_source_zero
    A₂ pr j oldCol hsource₂ oldRow
  let E : Matrix (Fin m) (Fin m) ℚ :=
    (eliminationMatrices A₂ pr j).foldr (· * ·) 1
  have houtput :
      (E * A₂) oldRow oldCol = 0 := by
    simpa [E, htarget₂] using hfold
  simpa [selectedPivotStep, j, pr, A₁, pivotVal, A₂, E] using houtput

lemma selectedPivotStep_preserves_unprocessed_left_zero
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m)
    {i : Fin m} {q : Fin n}
    (hi_pr : i ≠ ⟨pivotRow, hrow⟩)
    (htarget : A i q = 0)
    (hsource : A pi q = 0)
    (hactive : A ⟨pivotRow, hrow⟩ q = 0) :
    (selectedPivotStep A pivotRow col Es hcol pi hrow).1 i q = 0 := by
  let j : Fin n := ⟨col, hcol⟩
  let pr : Fin m := ⟨pivotRow, hrow⟩
  let A₁ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.swapRowsMat pr pi * A
  let pivotVal : ℚ := A₁ pr j
  let A₂ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.scaleRowMat pr pivotVal⁻¹ * A₁
  have hi_pr' : i ≠ pr := by simpa [pr] using hi_pr
  have htarget₁ : A₁ i q = 0 := by
    by_cases hi_pi : i = pi
    · subst i
      have hpi_pr : pi ≠ pr := hi_pr'
      have hswap : A₁ pi q = A pr q := by
        simpa [A₁, hpi_pr] using swapRowsMat_apply pr pi pi q
      rw [hswap]
      simpa [pr] using hactive
    · have hswap : A₁ i q = A i q := by
        simpa [A₁] using swapRowsMat_preserves_row_entry hi_pr' hi_pi
      rw [hswap, htarget]
  have htarget₂ : A₂ i q = 0 := by
    have hscale := scaleRowMat_apply_other_row
      (A := A₁) hi_pr' pivotVal⁻¹
    have hscaleq : A₂ i q = A₁ i q := by
      simpa [A₂] using congrFun hscale q
    rw [hscaleq, htarget₁]
  have hsource₂ : A₂ pr q = 0 := by
    have hswap : A₁ pr q = A pi q := by
      simpa [A₁] using swapRowsMat_apply pr pi pr q
    have hscale := scaleRowMat_apply_source_row (A := A₁) pr pivotVal⁻¹
    have hscaleq : A₂ pr q = pivotVal⁻¹ * A₁ pr q := by
      simpa [A₂] using congrFun hscale q
    rw [hscaleq, hswap, hsource]
    simp
  have hfold := elimination_fold_preserves_column_of_source_zero
    A₂ pr j q hsource₂ i
  let E : Matrix (Fin m) (Fin m) ℚ :=
    (eliminationMatrices A₂ pr j).foldr (· * ·) 1
  have houtput : (E * A₂) i q = 0 := by
    simpa [E, htarget₂] using hfold
  simpa [selectedPivotStep, j, pr, A₁, pivotVal, A₂, E] using houtput

lemma elimination_fold_preserves_zero_column
    (X : Matrix (Fin m) (Fin n) ℚ)
    (pr i : Fin m) (pivotCol oldCol : Fin n)
    (hsource : X pr oldCol = 0)
    (htarget : X i oldCol = 0) :
    let E : Matrix (Fin m) (Fin m) ℚ :=
      (eliminationMatrices X pr pivotCol).foldr (· * ·) 1
    (E * X) i oldCol = 0 := by
  have hread := elimination_fold_preserves_column_of_source_zero
    X pr pivotCol oldCol hsource i
  simpa [htarget] using hread

lemma elimination_fold_zeros_nonpivot_entry
    (X : Matrix (Fin m) (Fin n) ℚ)
    (pr k : Fin m)
    (hkp : k ≠ pr)
    (j : Fin n)
    (hpivot : X pr j = 1) :
    let E : Matrix (Fin m) (Fin m) ℚ :=
      (eliminationMatrices X pr j).foldr (· * ·) 1
    (E * X) k j = 0 := by
  classical
  let ks : List (Fin m) :=
    (Finset.filter (fun q => q ≠ pr) Finset.univ).toList
  have hks : ∀ q ∈ ks, q ≠ pr := by
    intro q hq
    simpa [ks] using
      (Finset.mem_filter.mp (Finset.mem_toList.mp hq)).2
  have hk_mem : k ∈ ks := by
    simp [ks, hkp]
  have hnd : ks.Nodup := by
    exact Finset.nodup_toList _
  dsimp only
  simpa [eliminationMatrices, ks, hk_mem] using
    addRowMat_list_apply ks pr hks hnd X j hpivot k

lemma selectedPivotStep_pivot_column_zero
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m)
    (k : Fin m)
    (hkp : k ≠ ⟨pivotRow, hrow⟩) :
    (selectedPivotStep A pivotRow col Es hcol pi hrow).1
        k ⟨col, hcol⟩ = 0 := by
  let j : Fin n := ⟨col, hcol⟩
  let pr : Fin m := ⟨pivotRow, hrow⟩
  let Eswap : Matrix (Fin m) (Fin m) ℚ :=
    FunctionalGaussJordan.swapRowsMat pr pi
  let A₁ : Matrix (Fin m) (Fin n) ℚ := Eswap * A
  let pivotVal : ℚ := A₁ pr j
  let A₂ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.scaleRowMat pr pivotVal⁻¹ * A₁
  have hpv : pivotVal ≠ 0 := by
    simpa only [pivotVal, A₁, Eswap, pr, j] using
      selected_pivotVal_ne_zero hcol hfind hrow
  have hpivot : A₂ pr j = 1 := by
    exact scale_selected_pivot_eq_one (A₁ := A₁) (j := j)
      (pivotVal := pivotVal) (pr := pr) rfl hpv
  have hzero :
      let E : Matrix (Fin m) (Fin m) ℚ :=
        (eliminationMatrices A₂ pr j).foldr (· * ·) 1
      (E * A₂) k j = 0 :=
    elimination_fold_zeros_nonpivot_entry A₂ pr k hkp j hpivot
  simpa [selectedPivotStep, eliminationMatrices, j, pr, Eswap,
    A₁, pivotVal, A₂] using hzero

lemma selectedPivotStep_pivot_column
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m) :
    ∀ k : Fin m,
      (selectedPivotStep A pivotRow col Es hcol pi hrow).1
          k ⟨col, hcol⟩ =
        if k = ⟨pivotRow, hrow⟩ then 1 else 0 := by
  intro k
  by_cases hk : k = ⟨pivotRow, hrow⟩
  · subst k
    simp only [if_pos rfl]
    exact selectedPivotStep_pivot_eq_one Es hcol hfind hrow
  · simp only [if_neg hk]
    exact selectedPivotStep_pivot_column_zero Es hcol hfind hrow k hk

lemma selectedPivotStep_preserves_pivot_column
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m)
    {oldRow : Fin m} {oldCol : Fin n}
    (hold : IsPivotColumnAt A oldRow oldCol)
    (hOldRow : oldRow.val < pivotRow) :
    IsPivotColumnAt
      (selectedPivotStep A pivotRow col Es hcol pi hrow).1
      oldRow oldCol := by
  let j : Fin n := ⟨col, hcol⟩
  let pr : Fin m := ⟨pivotRow, hrow⟩
  let A₁ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.swapRowsMat pr pi * A
  let pivotVal : ℚ := A₁ pr j
  let A₂ : Matrix (Fin m) (Fin n) ℚ :=
    FunctionalGaussJordan.scaleRowMat pr pivotVal⁻¹ * A₁
  have hswap : IsPivotColumnAt A₁ oldRow oldCol := by
    simpa [A₁, pr] using
      (swap_selected_preserves_old_pivot_column
        (A := A) hcol hfind hrow hold hOldRow)
  have hpr : pr ≠ oldRow := by
    intro h
    have : oldRow.val = pivotRow := congrArg Fin.val h.symm
    omega
  have hsource : A₁ pr oldCol = 0 := by
    have h := hswap pr
    rw [if_neg hpr] at h
    exact h
  have hscale : IsPivotColumnAt A₂ oldRow oldCol := by
    simpa [A₂] using
      (scaleRowMat_preserves_pivot_column hpr hswap pivotVal⁻¹)
  have helim := elimination_fold_preserves_column_of_source_zero
    A₂ pr j oldCol (by exact hscale pr ▸ if_neg hpr)
  intro k
  have helim_k := helim k
  have hscale_k := hscale k
  simpa [selectedPivotStep, j, pr, A₁, pivotVal, A₂] using
    helim_k.trans hscale_k

lemma selectedPivotStep_preserves_pivot_columns
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m)
    (P : List (Fin m × Fin n))
    (hP : ∀ rc ∈ P, IsPivotColumnAt A rc.1 rc.2)
    (hrows : ∀ rc ∈ P, rc.1.val < pivotRow) :
    ∀ rc ∈ P,
      IsPivotColumnAt
        (selectedPivotStep A pivotRow col Es hcol pi hrow).1
        rc.1 rc.2 := by
  intro rc hrc
  exact selectedPivotStep_preserves_pivot_column
    Es hcol hfind hrow (hP rc hrc) (hrows rc hrc)

lemma selectedPivotStep_extends_pivot_columns
    {A : Matrix (Fin m) (Fin n) ℚ}
    {pivotRow col : ℕ}
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hcol : col < n)
    {pi : Fin m}
    (hfind :
      findPivot A pivotRow ⟨col, hcol⟩ = some pi)
    (hrow : pivotRow < m)
    (P : List (Fin m × Fin n))
    (hP : ∀ rc ∈ P, IsPivotColumnAt A rc.1 rc.2)
    (hrows : ∀ rc ∈ P, rc.1.val < pivotRow) :
    ∀ rc ∈ P ++ [((⟨pivotRow, hrow⟩ : Fin m), (⟨col, hcol⟩ : Fin n))],
      IsPivotColumnAt
        (selectedPivotStep A pivotRow col Es hcol pi hrow).1
        rc.1 rc.2 := by
  intro rc hrc
  rcases List.mem_append.mp hrc with hrc | hrc
  · exact selectedPivotStep_preserves_pivot_columns
      Es hcol hfind hrow P hP hrows rc hrc
  · simp only [List.mem_singleton.mp hrc]
    exact selectedPivotStep_pivot_column Es hcol hfind hrow

lemma selectedPivotStep_extends_pivot_row_order
    {pivotRow col : ℕ}
    (hrow : pivotRow < m)
    (hcol : col < n)
    (P : List (Fin m × Fin n))
    (hrows : ∀ rc ∈ P, rc.1.val < pivotRow) :
    ∀ rc ∈ P ++ [((⟨pivotRow, hrow⟩ : Fin m), (⟨col, hcol⟩ : Fin n))],
      rc.1.val ≤ pivotRow := by
  intro rc hrc
  rcases List.mem_append.mp hrc with hrc | hrc
  · exact Nat.le_of_lt (hrows rc hrc)
  · rcases List.mem_singleton.mp hrc with rfl
    rfl

lemma selectedPivotStep_extends_pivot_row_order_old
    {pivotRow col : ℕ}
    (hrow : pivotRow < m)
    (hcol : col < n)
    (P : List (Fin m × Fin n))
    (hrows : ∀ rc ∈ P, rc.1.val < pivotRow) :
    ∀ rc ∈ P ++ [((⟨pivotRow, hrow⟩ : Fin m), (⟨col, hcol⟩ : Fin n))],
      rc ≠ ((⟨pivotRow, hrow⟩ : Fin m), (⟨col, hcol⟩ : Fin n)) →
      rc.1.val < pivotRow := by
  intro rc hrc hnew
  rcases List.mem_append.mp hrc with hrc | hrc
  · exact hrows rc hrc
  · rcases List.mem_singleton.mp hrc with rfl
    exact (hnew rfl).elim

lemma selectedPivotStep_extends_pivot_col_order
    {pivotRow col : ℕ}
    (hrow : pivotRow < m)
    (hcol : col < n)
    (P : List (Fin m × Fin n))
    (hcols : ∀ rc ∈ P, rc.2.val < col) :
    ∀ rc ∈ P ++ [((⟨pivotRow, hrow⟩ : Fin m), (⟨col, hcol⟩ : Fin n))],
      rc.2.val ≤ col := by
  intro rc hrc
  rcases List.mem_append.mp hrc with hrc | hrc
  · exact Nat.le_of_lt (hcols rc hrc)
  · rcases List.mem_singleton.mp hrc with rfl
    rfl

lemma selectedPivotStep_extends_pivot_col_order_old
    {pivotRow col : ℕ}
    (hrow : pivotRow < m)
    (hcol : col < n)
    (P : List (Fin m × Fin n))
    (hcols : ∀ rc ∈ P, rc.2.val < col) :
    ∀ rc ∈ P ++ [((⟨pivotRow, hrow⟩ : Fin m), (⟨col, hcol⟩ : Fin n))],
      rc ≠ ((⟨pivotRow, hrow⟩ : Fin m), (⟨col, hcol⟩ : Fin n)) →
      rc.2.val < col := by
  intro rc hrc hnew
  rcases List.mem_append.mp hrc with hrc | hrc
  · exact hcols rc hrc
  · rcases List.mem_singleton.mp hrc with rfl
    exact (hnew rfl).elim

lemma go_preserves_pivot_history
    (A : Matrix (Fin m) (Fin n) ℚ)
    (pivotRow col : ℕ)
    (Es : List (Matrix (Fin m) (Fin m) ℚ)) :
    ∀ P : List (Fin m × Fin n),
      (∀ rc ∈ P, IsPivotColumnAt A rc.1 rc.2) →
      (∀ rc ∈ P, rc.1.val < pivotRow) →
      (∀ rc ∈ P, rc.2.val < col) →
      ∀ rc ∈ P,
        IsPivotColumnAt
          (gaussJordanElimFull.go A pivotRow col Es).1
          rc.1 rc.2 := by
  induction A, pivotRow, col, Es using gaussJordanElimFull.go.induct
  · rename_i A pivotRow col Es hcol j hfind ih
    intro P hP hrows hcols rc hrc
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [hfind]
    simp only
    exact ih P hP hrows
      (fun q hq => Nat.lt_succ_of_lt (hcols q hq))
      rc hrc
  · rename_i A pivotRow col Es hcol j pi hfind hpr pr Eswap A1 pivotVal hpv
      Escale A2 Elims A3 ih
    intro P hP hrows hcols rc hrc
    let P' : List (Fin m × Fin n) :=
      P ++ [((⟨pivotRow, hpr⟩ : Fin m), (⟨col, hcol⟩ : Fin n))]
    have hP' : ∀ q ∈ P',
        IsPivotColumnAt
          (selectedPivotStep A pivotRow col Es hcol pi hpr).1 q.1 q.2 := by
      exact selectedPivotStep_extends_pivot_columns
        Es hcol hfind hpr P hP hrows
    have hrows' : ∀ q ∈ P', q.1.val < pivotRow + 1 := by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact Nat.lt_succ_of_lt (hrows q hq)
      · rcases List.mem_singleton.mp hq with rfl
        exact Nat.lt_succ_self pivotRow
    have hcols' : ∀ q ∈ P', q.2.val < col + 1 := by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact Nat.lt_succ_of_lt (hcols q hq)
      · rcases List.mem_singleton.mp hq with rfl
        exact Nat.lt_succ_self col
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [hfind]
    simp only
    rw [dif_pos hpr, dif_pos hpv]
    exact ih P' (by simpa [P', selectedPivotStep] using hP') hrows' hcols'
      rc (List.mem_append_left _ hrc)
  · rename_i A pivotRow col Es hcol j pi hfind hpr pr Eswap A1 pivotVal hpv ih
    intro P hP hrows hcols rc hrc
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [hfind]
    simp only
    rw [dif_pos hpr, dif_neg hpv]
    have hpv' : pivotVal ≠ 0 := by
      simpa only [pivotVal, A1, pr, j] using
        selected_pivotVal_ne_zero hcol hfind hpr
    exact (hpv hpv').elim
  · rename_i A pivotRow col Es hcol j pi hfind hpr
    intro P hP hrows hcols rc hrc
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [hfind]
    simp only
    rw [dif_neg hpr]
    exact hP rc hrc
  · rename_i A pivotRow col Es hcol
    intro P hP hrows hcols rc hrc
    rw [gaussJordanElimFull.go, dif_neg hcol]
    exact hP rc hrc

/-- The recursive pivot-row counter never exceeds the number of rows. -/
lemma go_pivotRow_le
    (A : Matrix (Fin m) (Fin n) ℚ) (pivotRow col : ℕ)
    (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hp : pivotRow ≤ m) :
    (gaussJordanElimFull.go A pivotRow col Es).2.1 ≤ m := by
  induction A, pivotRow, col, Es using gaussJordanElimFull.go.induct
  · rename_i A pivotRow col Es hcol j h_find ih
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    exact ih hp
  · rename_i A pivotRow col Es hcol j pi h_find hpr pr Eswap A1 pivotVal hpv Escale A2 Elims A3 ih
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    rw [dif_pos hpr, dif_pos hpv]
    exact ih (Nat.succ_le_of_lt hpr)
  · rename_i A pivotRow col Es hcol j pi h_find hpr pr Eswap A1 pivotVal hpv ih
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    rw [dif_pos hpr, dif_neg hpv]
    have hpv' : pivotVal ≠ 0 := by
      simpa only [pivotVal, A1, pr, j] using
        selected_pivotVal_ne_zero hcol h_find hpr
    exact (hpv hpv').elim
  · rename_i A pivotRow col Es hcol j pi h_find hpr
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    rw [dif_neg hpr]
    exact hp
  · rename_i A pivotRow col Es hcol
    rw [gaussJordanElimFull.go, dif_neg hcol]
    exact hp

/-- The recursive pivot-row counter never decreases during elimination. -/
lemma go_pivotRow_le_output
    (A : Matrix (Fin m) (Fin n) ℚ) (pivotRow col : ℕ)
    (Es : List (Matrix (Fin m) (Fin m) ℚ)) :
    pivotRow ≤ (gaussJordanElimFull.go A pivotRow col Es).2.1 := by
  induction A, pivotRow, col, Es using gaussJordanElimFull.go.induct
  · rename_i A pivotRow col Es hcol j h_find ih
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    exact ih
  · rename_i A pivotRow col Es hcol j pi h_find hpr pr Eswap A1 pivotVal hpv Escale A2 Elims A3 ih
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    rw [dif_pos hpr, dif_pos hpv]
    exact le_trans (Nat.le_succ pivotRow) ih
  · rename_i A pivotRow col Es hcol j pi h_find hpr pr Eswap A1 pivotVal hpv ih
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    rw [dif_pos hpr, dif_neg hpv]
    have hpv' : pivotVal ≠ 0 := by
      simpa only [pivotVal, A1, pr, j] using
        selected_pivotVal_ne_zero hcol h_find hpr
    exact (hpv hpv').elim
  · rename_i A pivotRow col Es hcol j pi h_find hpr
    rw [gaussJordanElimFull.go, dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    rw [dif_neg hpr]
  · rename_i A pivotRow col Es hcol
    rw [gaussJordanElimFull.go, dif_neg hcol]

noncomputable def gaussJordanElimFull (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℚ × ℕ × List (Matrix (Fin m) (Fin m) ℚ) :=
  gaussJordanElimFull.go A 0 0 []

noncomputable def gaussJordanElim (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℚ × ℕ :=
  let res := gaussJordanElimFull A
  (res.1, res.2.1)

lemma foldr_mul (L : List (Matrix (Fin m) (Fin m) ℚ)) (M : Matrix (Fin m) (Fin m) ℚ) :
    List.foldr (· * ·) M L = List.foldr (· * ·) 1 L * M := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldr_cons]
      rw [ih]
      exact (Matrix.mul_assoc x _ _).symm

theorem go_all_invertible (A : Matrix (Fin m) (Fin n) ℚ) (pivotRow col : ℕ) (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (hEs : ∀ E ∈ Es, IsUnit E) : ∀ E ∈ (gaussJordanElimFull.go A pivotRow col Es).2.2, IsUnit E := by
  induction A, pivotRow, col, Es using gaussJordanElimFull.go.induct
  · -- Case 1: findPivot = none
    rename_i A pivotRow col Es hcol j h_find ih
    intro E hE
    rw [gaussJordanElimFull.go] at hE
    rw [dif_pos hcol] at hE
    simp only at hE
    rw [h_find] at hE
    simp only at hE
    exact ih hEs E hE
  · -- Case 2: findPivot = some pi, pivotRow < m, pivotVal ≠ 0
    rename_i A pivotRow col Es hcol j pi h_find hpr pr Eswap A1 pivotVal hpv Escale A2 Elims A3 ih
    intro E hE
    rw [gaussJordanElimFull.go] at hE
    rw [dif_pos hcol] at hE
    simp only at hE
    rw [h_find] at hE
    simp only at hE
    rw [dif_pos hpr] at hE
    rw [dif_pos hpv] at hE
    apply ih _ E hE
    intro F hF
    rw [List.mem_append] at hF
    rw [List.mem_append] at hF
    cases hF with
    | inl hF_left =>
      cases hF_left with
      | inl hF_elim =>
        have h_mem : F ∈ Elims := hF_elim
        simp only [Elims, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at h_mem
        exact Exists.elim h_mem (fun k hk_and_eq => by
          rw [← hk_and_eq.right]
          exact FunctionalGaussJordan.addRowMat_isUnit k pr hk_and_eq.left _
        )
      | inr hF_scale_or_swap =>
        rw [List.mem_cons] at hF_scale_or_swap
        rw [List.mem_cons] at hF_scale_or_swap
        simp only [List.not_mem_nil, or_false] at hF_scale_or_swap
        cases hF_scale_or_swap with
        | inl hF_scale =>
          rw [hF_scale]
          exact FunctionalGaussJordan.scaleRowMat_isUnit pr (inv_ne_zero hpv)
        | inr hF_swap =>
          rw [hF_swap]
          exact FunctionalGaussJordan.swapRowsMat_isUnit pr pi
    | inr hF_es =>
      exact hEs F hF_es
  · -- Case 3: findPivot = some pi, pivotRow < m, pivotVal = 0
    rename_i A pivotRow col Es hcol j pi h_find hpr pr Eswap A1 pivotVal hpv ih
    intro E hE
    rw [gaussJordanElimFull.go] at hE
    rw [dif_pos hcol] at hE
    simp only at hE
    rw [h_find] at hE
    simp only at hE
    rw [dif_pos hpr] at hE
    rw [dif_neg hpv] at hE
    have hpv' : pivotVal ≠ 0 := by
      simpa only [pivotVal, A1, pr, j] using
        selected_pivotVal_ne_zero hcol h_find hpr
    exact (hpv hpv').elim
  · -- Case 4: findPivot = some pi, ¬pivotRow < m
    rename_i A pivotRow col Es hcol j pi h_find hpr
    intro E hE
    rw [gaussJordanElimFull.go] at hE
    rw [dif_pos hcol] at hE
    simp only at hE
    rw [h_find] at hE
    simp only at hE
    rw [dif_neg hpr] at hE
    exact hEs E hE
  · -- Case 5: ¬col < n
    rename_i A pivotRow col Es hcol
    intro E hE
    rw [gaussJordanElimFull.go] at hE
    rw [dif_neg hcol] at hE
    exact hEs E hE

theorem go_R_eq (A : Matrix (Fin m) (Fin n) ℚ) (pivotRow col : ℕ) (Es : List (Matrix (Fin m) (Fin m) ℚ))
    (A_init : Matrix (Fin m) (Fin n) ℚ) (hA : A = (Es.foldr (· * ·) 1) * A_init) :
    (gaussJordanElimFull.go A pivotRow col Es).1 = ((gaussJordanElimFull.go A pivotRow col Es).2.2.foldr (· * ·) 1) * A_init := by
  induction A, pivotRow, col, Es using gaussJordanElimFull.go.induct
  · -- Case 1: findPivot = none
    rename_i A pivotRow col Es hcol j h_find ih
    rw [gaussJordanElimFull.go]
    rw [dif_pos hcol]
    simp only
    rw [h_find]
    exact ih hA
  · -- Case 2: findPivot = some pi, pivotRow < m, pivotVal ≠ 0
    rename_i A pivotRow col Es hcol j pi h_find hpr pr Eswap A1 pivotVal hpv Escale A2 Elims A3 ih
    rw [gaussJordanElimFull.go]
    rw [dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    rw [dif_pos hpr]
    rw [dif_pos hpv]
    apply ih
    dsimp only [A3, A2, A1]
    rw [hA]
    simp only [List.foldr_append, List.foldr_cons, List.foldr_nil]
    have h_rhs : List.foldr (· * ·) (Escale * (Eswap * List.foldr (· * ·) 1 Es)) Elims =
        List.foldr (· * ·) 1 Elims * (Escale * (Eswap * List.foldr (· * ·) 1 Es)) := foldr_mul _ _
    rw [h_rhs]
    rw [Matrix.mul_assoc (List.foldr _ 1 Elims)]
    rw [Matrix.mul_assoc Escale]
    rw [Matrix.mul_assoc Eswap]
  · -- Case 3: findPivot = some pi, pivotRow < m, pivotVal = 0
    rename_i A pivotRow col Es hcol j pi h_find hpr pr Eswap A1 pivotVal hpv ih
    rw [gaussJordanElimFull.go]
    rw [dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    rw [dif_pos hpr]
    rw [dif_neg hpv]
    have hpv' : pivotVal ≠ 0 := by
      simpa only [pivotVal, A1, pr, j] using
        selected_pivotVal_ne_zero hcol h_find hpr
    exact (hpv hpv').elim
  · -- Case 4: findPivot = some pi, ¬pivotRow < m
    rename_i A pivotRow col Es hcol j pi h_find hpr
    rw [gaussJordanElimFull.go]
    rw [dif_pos hcol]
    simp only
    rw [h_find]
    simp only
    rw [dif_neg hpr]
    exact hA
  · -- Case 5: ¬col < n
    rename_i A pivotRow col Es hcol
    rw [gaussJordanElimFull.go]
    rw [dif_neg hcol]
    exact hA

/-- Every matrix in the elimination list is invertible. -/
lemma all_invertible (A : Matrix (Fin m) (Fin n) ℚ) :
    ∀ E ∈ (gaussJordanElimFull.go A 0 0 []).2.2, IsUnit E := by
  exact go_all_invertible A 0 0 [] (by simp)

theorem gaussJordanElim_decomposition
    (A : Matrix (Fin m) (Fin n) ℚ) :
    (gaussJordanElim A).1 =
      ((gaussJordanElimFull A).2.2.foldr (· * ·) 1) * A := by
  dsimp [gaussJordanElim, gaussJordanElimFull]
  exact go_R_eq A 0 0 [] A (by simp)

lemma foldr_isUnit
    (L : List (Matrix (Fin m) (Fin m) ℚ))
    (hL : ∀ E ∈ L, IsUnit E) :
    IsUnit (L.foldr (· * ·) 1) := by
  induction L with
  | nil => simp
  | cons E L ih =>
      simp only [List.foldr_cons]
      exact (hL E (by simp)).mul
        (ih (fun F hF => hL F (by simp [hF])))

theorem gaussJordanElim_composite_isUnit
    (A : Matrix (Fin m) (Fin n) ℚ) :
    IsUnit ((gaussJordanElimFull A).2.2.foldr (· * ·) 1) := by
  apply foldr_isUnit
  exact all_invertible A

theorem gaussJordan_decomposition
    (A : Matrix (Fin m) (Fin n) ℚ) :
    ∃ E : Matrix (Fin m) (Fin m) ℚ,
      IsUnit E ∧ (gaussJordanElim A).1 = E * A := by
  let E : Matrix (Fin m) (Fin m) ℚ :=
    (gaussJordanElimFull A).2.2.foldr (· * ·) 1
  refine ⟨E, ?_, ?_⟩
  · exact gaussJordanElim_composite_isUnit A
  · exact gaussJordanElim_decomposition A

/-- rank(gaussJordanElim A) = rank(A) because the composite of elementary
    operations is invertible. -/
theorem gaussJordanElim_preserves_rank (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix.rank (gaussJordanElim A).1 = Matrix.rank A := by
  dsimp [gaussJordanElim, gaussJordanElimFull]
  have h_all_unit : ∀ E ∈ (gaussJordanElimFull.go A 0 0 []).2.2, IsUnit E := all_invertible A
  have h_R_eq : (gaussJordanElimFull.go A 0 0 []).1 =
      ((gaussJordanElimFull.go A 0 0 []).2.2.foldr (· * ·) 1) * A := by
    exact go_R_eq A 0 0 [] A (by simp)
  rw [h_R_eq]
  exact FunctionalGaussJordan.elementary_composite_preserves_rank _ h_all_unit A

/-- The unconditional native rank theorem for the executable elimination core. -/
theorem gaussJordanElim_rank_eq (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix.rank (gaussJordanElim A).1 = Matrix.rank A :=
  gaussJordanElim_preserves_rank A

/-- The algorithm's counter is bounded by the number of rows. -/
theorem gaussJordanElim_pivotRow_le (A : Matrix (Fin m) (Fin n) ℚ) :
    (gaussJordanElim A).2 ≤ m := by
  simpa [gaussJordanElim, gaussJordanElimFull] using
    (go_pivotRow_le A 0 0 [] (Nat.zero_le m))

/-- The algorithm's second output is the number of pivot rows reached by the
    recursive elimination state.  Equality with `Matrix.rank` requires the
    separate RREF correctness theorem and is deliberately not asserted here. -/
theorem gaussJordanElim_output_is_pivot_row_count (A : Matrix (Fin m) (Fin n) ℚ) :
    (gaussJordanElim A).2 = (gaussJordanElimFull A).2.1 :=
  rfl

end DAG.MatrixGaussJordan
