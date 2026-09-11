import InfoGeometry.Categorical.FibonacciCompositeChannelBlocks
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Categorical.FibonacciPentagonPathCarrier

/-!
# The composite-middle Fibonacci associator block

For the four-`τ` sector, the middle object `τ ⊗ τ` is `𝟙 ⊕ τ`.
The associator with this composite middle input therefore acts by the
identity on the unit-output multiplicity block and by `1 ⊕ F` on the
three-dimensional `τ`-output block.  This owner records that block action
with explicit finite-index transports; it does not claim the full pentagon.
-/

namespace InfoGeometry.Categorical.FibonacciCompositeMiddleAssociator

open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciFusionTreeAssociator
open InfoGeometry.Categorical.FibonacciCompositeChannelBlocks
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciPentagonPathCarrier

noncomputable def compositeMiddleTauBlock (τ s : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks
      (1 : Matrix (Fin 1) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) (Fin 2) ℂ)
      (0 : Matrix (Fin 2) (Fin 1) ℂ)
      (fibonacciFusionMatrix τ s))

theorem compositeMiddleTauBlock_sq
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    compositeMiddleTauBlock τ s * compositeMiddleTauBlock τ s = 1 := by
  unfold compositeMiddleTauBlock
  rw [← InfoGeometry.Categorical.FibonacciBraidedCategory.reindex_mul]
  rw [Matrix.fromBlocks_multiply]
  rw [fibonacciFusionMatrix_sq hs hτ]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add]
  rw [Matrix.fromBlocks_one]
  simpa [Matrix.reindexLinearEquiv] using
    (Matrix.reindexLinearEquiv_one (R := ℂ) (A := ℂ) finSumFinEquiv)

/-! The first standard pentagon edge has the composite object on the left:
`a_{(τ⊗τ),τ,τ}`.  Its output multiplicity blocks use the same `1 ⊕ F`
decomposition as the middle composite edge, but its source and target are
the first two typed pentagon vertices. -/

noncomputable def outerLeftAssociator (τ s : ℂ) :
    FibHom
      (parenthesizedObject .vertex₁)
      (parenthesizedObject .vertex₂) := by
  have hsu := parenthesizedObject_counts .vertex₁
  have htu := parenthesizedObject_counts .vertex₂
  exact
    { unit_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin hsu.1.symm))
        (Equiv.cast (congrArg Fin htu.1.symm))
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
      tau_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin hsu.2.symm))
        (Equiv.cast (congrArg Fin htu.2.symm))
        (compositeMiddleTauBlock τ s) }

noncomputable def outerLeftAssociatorInv (τ s : ℂ) :
    FibHom
      (parenthesizedObject .vertex₂)
      (parenthesizedObject .vertex₁) := by
  have hsu := parenthesizedObject_counts .vertex₁
  have htu := parenthesizedObject_counts .vertex₂
  exact
    { unit_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin htu.1.symm))
        (Equiv.cast (congrArg Fin hsu.1.symm))
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
      tau_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin htu.2.symm))
        (Equiv.cast (congrArg Fin hsu.2.symm))
        (compositeMiddleTauBlock τ s) }

theorem outerLeftAssociator_comp_inv
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (outerLeftAssociator τ s)
        (outerLeftAssociatorInv τ s) =
      FibHom.id (parenthesizedObject .vertex₁) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, outerLeftAssociator,
      outerLeftAssociatorInv]
  · simp [FibHom.comp, FibHom.id, outerLeftAssociator,
      outerLeftAssociatorInv, Matrix.reindexLinearEquiv_mul,
      compositeMiddleTauBlock_sq τ s hs hτ]

theorem outerLeftAssociator_inv_comp
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (outerLeftAssociatorInv τ s)
        (outerLeftAssociator τ s) =
      FibHom.id (parenthesizedObject .vertex₂) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, outerLeftAssociator,
      outerLeftAssociatorInv]
  · simp [FibHom.comp, FibHom.id, outerLeftAssociator,
      outerLeftAssociatorInv, Matrix.reindexLinearEquiv_mul,
      compositeMiddleTauBlock_sq τ s hs hτ]

noncomputable def outerLeftAssociatorIso
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    parenthesizedObject .vertex₁ ≅ parenthesizedObject .vertex₂ :=
  { hom := outerLeftAssociator τ s
    inv := outerLeftAssociatorInv τ s
    hom_inv_id := outerLeftAssociator_comp_inv τ s hs hτ
    inv_hom_id := outerLeftAssociator_inv_comp τ s hs hτ }

/- The other composite-input edge is `a_{τ,τ,(τ⊗τ)}`.  Its inverse is
the pentagon edge from vertex five back to vertex two. -/

noncomputable def rightCompositeAssociator (τ s : ℂ) :
    FibHom
      (parenthesizedObject .vertex₂)
      (parenthesizedObject .vertex₅) := by
  have hsu := parenthesizedObject_counts .vertex₂
  have htu := parenthesizedObject_counts .vertex₅
  exact
    { unit_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin hsu.1.symm))
        (Equiv.cast (congrArg Fin htu.1.symm))
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
      tau_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin hsu.2.symm))
        (Equiv.cast (congrArg Fin htu.2.symm))
        (compositeMiddleTauBlock τ s) }

noncomputable def rightCompositeAssociatorInv (τ s : ℂ) :
    FibHom
      (parenthesizedObject .vertex₅)
      (parenthesizedObject .vertex₂) := by
  have hsu := parenthesizedObject_counts .vertex₂
  have htu := parenthesizedObject_counts .vertex₅
  exact
    { unit_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin htu.1.symm))
        (Equiv.cast (congrArg Fin hsu.1.symm))
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
      tau_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin htu.2.symm))
        (Equiv.cast (congrArg Fin hsu.2.symm))
        (compositeMiddleTauBlock τ s) }

theorem rightCompositeAssociator_comp_inv
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (rightCompositeAssociator τ s)
        (rightCompositeAssociatorInv τ s) =
      FibHom.id (parenthesizedObject .vertex₂) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, rightCompositeAssociator,
      rightCompositeAssociatorInv]
  · simp [FibHom.comp, FibHom.id, rightCompositeAssociator,
      rightCompositeAssociatorInv, Matrix.reindexLinearEquiv_mul,
      compositeMiddleTauBlock_sq τ s hs hτ]

theorem rightCompositeAssociator_inv_comp
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (rightCompositeAssociatorInv τ s)
        (rightCompositeAssociator τ s) =
      FibHom.id (parenthesizedObject .vertex₅) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, rightCompositeAssociator,
      rightCompositeAssociatorInv]
  · simp [FibHom.comp, FibHom.id, rightCompositeAssociator,
      rightCompositeAssociatorInv, Matrix.reindexLinearEquiv_mul,
      compositeMiddleTauBlock_sq τ s hs hτ]

noncomputable def rightCompositeAssociatorIso
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    parenthesizedObject .vertex₂ ≅ parenthesizedObject .vertex₅ :=
  { hom := rightCompositeAssociator τ s
    inv := rightCompositeAssociatorInv τ s
    hom_inv_id := rightCompositeAssociator_comp_inv τ s hs hτ
    inv_hom_id := rightCompositeAssociator_inv_comp τ s hs hτ }

theorem compositeMiddle_source_counts :
    (fibTensorObj (fibTensorObj tauObject compositeTau) tauObject)
        FibSimple.unit = 2 ∧
      (fibTensorObj (fibTensorObj tauObject compositeTau) tauObject)
        FibSimple.tau = 3 := by
  simp [tauObject, compositeTau, fibTensorObj]

theorem compositeMiddle_target_counts :
    (fibTensorObj tauObject (fibTensorObj compositeTau tauObject))
        FibSimple.unit = 2 ∧
      (fibTensorObj tauObject (fibTensorObj compositeTau tauObject))
        FibSimple.tau = 3 := by
  simp [tauObject, compositeTau, fibTensorObj]

noncomputable def compositeMiddleAssociator (τ s : ℂ) :
    FibHom
      (fibTensorObj (fibTensorObj tauObject compositeTau) tauObject)
      (fibTensorObj tauObject (fibTensorObj compositeTau tauObject)) := by
  have hsu := compositeMiddle_source_counts
  have htu := compositeMiddle_target_counts
  exact
    { unit_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin hsu.1.symm))
        (Equiv.cast (congrArg Fin htu.1.symm))
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
      tau_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin hsu.2.symm))
        (Equiv.cast (congrArg Fin htu.2.symm))
        (compositeMiddleTauBlock τ s) }

noncomputable def compositeMiddleAssociatorInv (τ s : ℂ) :
    FibHom
      (fibTensorObj tauObject (fibTensorObj compositeTau tauObject))
      (fibTensorObj (fibTensorObj tauObject compositeTau) tauObject) := by
  have hsu := compositeMiddle_source_counts
  have htu := compositeMiddle_target_counts
  exact
    { unit_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin htu.1.symm))
        (Equiv.cast (congrArg Fin hsu.1.symm))
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
      tau_comp := Matrix.reindex
        (Equiv.cast (congrArg Fin htu.2.symm))
        (Equiv.cast (congrArg Fin hsu.2.symm))
        (compositeMiddleTauBlock τ s) }

theorem compositeMiddleAssociator_comp_inv
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (compositeMiddleAssociator τ s)
        (compositeMiddleAssociatorInv τ s) =
      FibHom.id (fibTensorObj (fibTensorObj tauObject compositeTau) tauObject) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, compositeMiddleAssociator,
      compositeMiddleAssociatorInv]
  · simp [FibHom.comp, FibHom.id, compositeMiddleAssociator,
      compositeMiddleAssociatorInv, Matrix.reindexLinearEquiv_mul,
      compositeMiddleTauBlock_sq τ s hs hτ]

theorem compositeMiddleAssociator_inv_comp
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (compositeMiddleAssociatorInv τ s)
        (compositeMiddleAssociator τ s) =
      FibHom.id (fibTensorObj tauObject (fibTensorObj compositeTau tauObject)) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, compositeMiddleAssociator,
      compositeMiddleAssociatorInv]
  · simp [FibHom.comp, FibHom.id, compositeMiddleAssociator,
      compositeMiddleAssociatorInv, Matrix.reindexLinearEquiv_mul,
      compositeMiddleTauBlock_sq τ s hs hτ]

/-- The same composite associator, now typed at the concrete pentagon
vertex edge `v₃ → v₄`.  The equality of the two object expressions is the
existing Fibonacci fusion-rule normalization, not a new carrier. -/
noncomputable def pentagonMiddleAssociator (τ s : ℂ) :
    FibHom
      (parenthesizedObject .vertex₃)
      (parenthesizedObject .vertex₄) := by
  simpa [parenthesizedObject, fourTau, compositeTau, tauObject] using
    (compositeMiddleAssociator τ s)

noncomputable def pentagonMiddleAssociatorInv (τ s : ℂ) :
    FibHom
      (parenthesizedObject .vertex₄)
      (parenthesizedObject .vertex₃) := by
  simpa [parenthesizedObject, fourTau, compositeTau, tauObject] using
    (compositeMiddleAssociatorInv τ s)

theorem pentagonMiddleAssociator_comp_inv
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (pentagonMiddleAssociator τ s)
        (pentagonMiddleAssociatorInv τ s) =
      FibHom.id (parenthesizedObject .vertex₃) := by
  simpa [pentagonMiddleAssociator, pentagonMiddleAssociatorInv] using
    (compositeMiddleAssociator_comp_inv τ s hs hτ)

theorem pentagonMiddleAssociator_inv_comp
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (pentagonMiddleAssociatorInv τ s)
        (pentagonMiddleAssociator τ s) =
      FibHom.id (parenthesizedObject .vertex₄) := by
  simpa [pentagonMiddleAssociator, pentagonMiddleAssociatorInv] using
    (compositeMiddleAssociator_inv_comp τ s hs hτ)

end InfoGeometry.Categorical.FibonacciCompositeMiddleAssociator
