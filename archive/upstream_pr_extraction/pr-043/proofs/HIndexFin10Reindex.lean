import proofs.SplitOctonionTKK55LieEquivalence

/-! # Reindex the hyperbolic carrier by `Fin 10` -/

noncomputable section
namespace HIndexFin10Reindex

open SplitOctonionTKK55
open SplitOctonionTKK55Blocks

def hIndexToFin10 : HIndex → Fin 10
  | .minus => 0
  | .middle i => ⟨i.val + 1, by omega⟩
  | .plus => 9

def fin10ToHIndex (i : Fin 10) : HIndex :=
  if h0 : i.val = 0 then .minus
  else if h9 : i.val = 9 then .plus
  else .middle ⟨i.val - 1, by omega⟩

theorem leftInverse : Function.LeftInverse fin10ToHIndex hIndexToFin10 := by
  intro i
  cases i with
  | minus => simp [hIndexToFin10, fin10ToHIndex]
  | middle i =>
      fin_cases i <;> simp [hIndexToFin10, fin10ToHIndex]
  | plus => simp [hIndexToFin10, fin10ToHIndex]

theorem rightInverse : Function.RightInverse fin10ToHIndex hIndexToFin10 := by
  intro i
  fin_cases i <;> simp [hIndexToFin10, fin10ToHIndex]

def hIndexEquivFin10 : HIndex ≃ Fin 10 where
  toFun := hIndexToFin10
  invFun := fin10ToHIndex
  left_inv := leftInverse
  right_inv := rightInverse

def reindexHMatrix (A : HMatrix) : M10 :=
  fun i j => A (fin10ToHIndex i) (fin10ToHIndex j)

def unreindexHMatrix (A : M10) : HMatrix :=
  fun i j => A (hIndexToFin10 i) (hIndexToFin10 j)

theorem unreindex_reindex (A : HMatrix) :
    unreindexHMatrix (reindexHMatrix A) = A := by
  ext i j
  change A (fin10ToHIndex (hIndexToFin10 i))
      (fin10ToHIndex (hIndexToFin10 j)) = A i j
  rw [leftInverse i, leftInverse j]

theorem reindex_unreindex (A : M10) :
    reindexHMatrix (unreindexHMatrix A) = A := by
  ext i j
  change A (hIndexToFin10 (fin10ToHIndex i))
      (hIndexToFin10 (fin10ToHIndex j)) = A i j
  rw [rightInverse i, rightInverse j]

def hMatrixFin10LinearEquiv : HMatrix ≃ₗ[ℝ] M10 where
  toFun := reindexHMatrix
  invFun := unreindexHMatrix
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv := unreindex_reindex
  right_inv := reindex_unreindex

def hyperbolicMetric10 : M10 := reindexHMatrix metric55

end HIndexFin10Reindex
end noncomputable section
