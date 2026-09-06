import proofs.TwoSheetThreeColorWeyl

/-!
# Two-sheet operator coordinates

Every operator on `ℂ² ⊗ ℂ³` is uniquely determined by its four
`3 × 3` sheet blocks.  This owner deliberately separates that coordinate
fact from the later chiral, Nambu, CPT, and Clifford structures.
-/

noncomputable section
namespace TwoSheetOperatorCoordinates

open TwoSheetThreeColorWeyl

abbrev BlockQuad := M3C × M3C × M3C × M3C

/-- The `(α,β)` sheet block of a six-state operator. -/
def sheetBlock (A : M6C) (α β : Fin 2) : M3C :=
  fun a b => A (α, a) (β, b)

/-- Reassemble an operator from its four sheet blocks. -/
def assembleBlocks (B : BlockQuad) : M6C
  | (i, a), (j, b) =>
      match i, j with
      | 0, 0 => B.1 a b
      | 0, 1 => B.2.1 a b
      | 1, 0 => B.2.2.1 a b
      | 1, 1 => B.2.2.2 a b

/-- Extract all four sheet blocks. -/
def extractBlocks (A : M6C) : BlockQuad :=
  (sheetBlock A 0 0, sheetBlock A 0 1,
    sheetBlock A 1 0, sheetBlock A 1 1)

theorem assembleBlocks_extractBlocks (A : M6C) :
    assembleBlocks (extractBlocks A) = A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

theorem extractBlocks_assembleBlocks (B : BlockQuad) :
    extractBlocks (assembleBlocks B) = B := by
  rcases B with ⟨B00, B01, B10, B11⟩
  apply Prod.ext
  · ext a b
    rfl
  · apply Prod.ext
    · ext a b
      rfl
    · apply Prod.ext
      · ext a b
        rfl
      · ext a b
        rfl

/-- The linear equivalence between six-state operators and four colour blocks. -/
def blockLinearEquiv : M6C ≃ₗ[ℂ] BlockQuad where
  toFun := extractBlocks
  invFun := assembleBlocks
  map_add' A B := by
    apply Prod.ext
    · ext a b
      rfl
    · apply Prod.ext
      · ext a b
        rfl
      · apply Prod.ext
        · ext a b
          rfl
        · ext a b
          rfl
  map_smul' c A := by
    apply Prod.ext
    · ext a b
      rfl
    · apply Prod.ext
      · ext a b
        rfl
      · apply Prod.ext
        · ext a b
          rfl
        · ext a b
          rfl
  left_inv := assembleBlocks_extractBlocks
  right_inv := extractBlocks_assembleBlocks

@[simp] theorem blockLinearEquiv_apply (A : M6C) :
    blockLinearEquiv A = extractBlocks A := rfl

@[simp] theorem blockLinearEquiv_symm_apply (B : BlockQuad) :
    blockLinearEquiv.symm B = assembleBlocks B := rfl

end TwoSheetOperatorCoordinates
end noncomputable section
