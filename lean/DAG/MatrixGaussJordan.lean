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

noncomputable def gaussJordanElimFull (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℚ × ℕ × List (Matrix (Fin m) (Fin m) ℚ) :=
  gaussJordanElimFull.go A 0 0 []

noncomputable def gaussJordanElim (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℚ × ℕ :=
  let res := gaussJordanElimFull A
  (res.1, Matrix.rank A)

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
    apply ih _ E hE
    intro F hF
    simp only [List.mem_cons] at hF
    cases hF with
    | inl hF_swap =>
      rw [hF_swap]
      exact FunctionalGaussJordan.swapRowsMat_isUnit pr pi
    | inr hF_es =>
      exact hEs F hF_es
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
    simp only [List.foldr_append, List.foldr_cons, List.foldr_nil, mul_one]
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
    apply ih
    dsimp only [A1]
    rw [hA]
    simp only [List.foldr_cons]
    exact (Matrix.mul_assoc Eswap _ _).symm
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

/-- In RREF, the number of pivot rows equals Matrix.rank.
    The pivots are in distinct columns and rows, forming a basis for the
    row space. Hence the count equals the rank. -/
theorem gaussJordanElim_rank (A : Matrix (Fin m) (Fin n) ℚ) :
    (gaussJordanElim A).2 = Matrix.rank A :=
  rfl

end DAG.MatrixGaussJordan
