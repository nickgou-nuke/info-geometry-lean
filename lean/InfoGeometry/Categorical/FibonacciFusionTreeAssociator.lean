import InfoGeometry.Categorical.FibonacciBraidedCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/-!
# The concrete `τ ⊗ τ ⊗ τ` Fibonacci fusion-tree block

The current skeletal category has block-diagonal morphisms, while the
nontrivial Fibonacci `F`-matrix acts on the two-dimensional `τ` fusion-tree
multiplicity space.  This owner places that matrix on the concrete
`τ ⊗ τ ⊗ τ` sector (`1 ⊕ 2τ`).  It is a fixed-sector morphism, not yet a
natural associator for all objects and morphisms.
-/

namespace InfoGeometry.Categorical.FibonacciFusionTreeAssociator

open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

noncomputable def tauObject : FibCat :=
  Finsupp.single FibSimple.tau 1

theorem tau_left_tree_unit_count :
    (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
        FibSimple.unit = 1 := by
  simp [tauObject, fibTensorObj]

theorem tau_left_tree_tau_count :
    (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
        FibSimple.tau = 2 := by
  simp [tauObject, fibTensorObj]

theorem tau_right_tree_unit_count :
    (fibTensorObj tauObject (fibTensorObj tauObject tauObject))
        FibSimple.unit = 1 := by
  simp [tauObject, fibTensorObj]

theorem tau_right_tree_tau_count :
    (fibTensorObj tauObject (fibTensorObj tauObject tauObject))
        FibSimple.tau = 2 := by
  simp [tauObject, fibTensorObj]

noncomputable def tauFusionTreeAssociator (τ s : ℂ) :
    FibHom (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      (fibTensorObj tauObject (fibTensorObj tauObject tauObject)) := by
  have hu₁ : 1 = (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      FibSimple.unit := tau_left_tree_unit_count.symm
  have hu₂ : 1 = (fibTensorObj tauObject (fibTensorObj tauObject tauObject))
      FibSimple.unit := tau_right_tree_unit_count.symm
  have ht₁ : 2 = (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      FibSimple.tau := tau_left_tree_tau_count.symm
  have ht₂ : 2 = (fibTensorObj tauObject (fibTensorObj tauObject tauObject))
      FibSimple.tau := tau_right_tree_tau_count.symm
  exact
    { unit_comp := Matrix.reindex (Equiv.cast (congrArg Fin hu₁))
        (Equiv.cast (congrArg Fin hu₂))
        (1 : Matrix (Fin 1) (Fin 1) ℂ)
      tau_comp := Matrix.reindex (Equiv.cast (congrArg Fin ht₁))
        (Equiv.cast (congrArg Fin ht₂))
        (fibonacciFusionMatrix τ s) }

/-- The inverse fusion-tree morphism.  Its nontrivial block is the same
Fibonacci matrix because the finite matrix is involutive. -/
noncomputable def tauFusionTreeAssociatorInv (τ s : ℂ) :
    FibHom (fibTensorObj tauObject (fibTensorObj tauObject tauObject))
      (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) := by
  have hu₁ : 1 = (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      FibSimple.unit := tau_left_tree_unit_count.symm
  have hu₂ : 1 = (fibTensorObj tauObject (fibTensorObj tauObject tauObject))
      FibSimple.unit := tau_right_tree_unit_count.symm
  have ht₁ : 2 = (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      FibSimple.tau := tau_left_tree_tau_count.symm
  have ht₂ : 2 = (fibTensorObj tauObject (fibTensorObj tauObject tauObject))
      FibSimple.tau := tau_right_tree_tau_count.symm
  exact
    { unit_comp := Matrix.reindex (Equiv.cast (congrArg Fin hu₂))
        (Equiv.cast (congrArg Fin hu₁))
        (1 : Matrix (Fin 1) (Fin 1) ℂ)
      tau_comp := Matrix.reindex (Equiv.cast (congrArg Fin ht₂))
        (Equiv.cast (congrArg Fin ht₁))
        (fibonacciFusionMatrix τ s) }

theorem tauFusionTreeAssociator_comp_inv
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (tauFusionTreeAssociator τ s)
        (tauFusionTreeAssociatorInv τ s) =
      FibHom.id (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, tauFusionTreeAssociator,
      tauFusionTreeAssociatorInv, Matrix.reindexLinearEquiv_mul]
  · simp [FibHom.comp, FibHom.id, tauFusionTreeAssociator,
      tauFusionTreeAssociatorInv, Matrix.reindexLinearEquiv_mul,
      fibonacciFusionMatrix_sq hs hτ]

theorem tauFusionTreeAssociator_inv_comp
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (tauFusionTreeAssociatorInv τ s)
        (tauFusionTreeAssociator τ s) =
      FibHom.id (fibTensorObj tauObject (fibTensorObj tauObject tauObject)) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, tauFusionTreeAssociator,
      tauFusionTreeAssociatorInv]
  · simp [FibHom.comp, FibHom.id, tauFusionTreeAssociator,
      tauFusionTreeAssociatorInv, fibonacciFusionMatrix_sq hs hτ]

/-- The nontrivial Fibonacci associator block bundled as a genuine categorical
isomorphism in the existing finite Hom-space category. -/
noncomputable def tauFusionTreeAssociatorIso
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibTensorObj (fibTensorObj tauObject tauObject) tauObject ≅
      fibTensorObj tauObject (fibTensorObj tauObject tauObject) :=
  { hom := tauFusionTreeAssociator τ s
    inv := tauFusionTreeAssociatorInv τ s
    hom_inv_id := tauFusionTreeAssociator_comp_inv τ s hs hτ
    inv_hom_id := tauFusionTreeAssociator_inv_comp τ s hs hτ }

theorem tauFusionTreeAssociator_tau_block
    (τ s : ℂ) :
    (tauFusionTreeAssociator τ s).tau_comp =
      Matrix.reindex
        (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))
        (Equiv.cast (congrArg Fin tau_right_tree_tau_count.symm))
        (fibonacciFusionMatrix τ s) := by
  rfl

theorem tauFusionTreeAssociator_tau_block_involutive
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s = 1 :=
  fibonacciFusionMatrix_sq hs hτ

/-- The finite fusion-tree associator is genuinely non-identity whenever the
off-diagonal Fibonacci channel is nonzero.  This is a representation-level
statement; it does not promote the block to a categorical natural isomorphism.
-/
theorem fibonacciFusionMatrix_ne_one_of_tau_ne_zero
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ≠ 0) :
    fibonacciFusionMatrix τ s ≠ 1 := by
  intro h
  have h01 := congrArg (fun M => M 0 1) h
  have hs_zero : s = 0 := by
    simpa [fibonacciFusionMatrix] using h01
  apply hτ
  rw [← hs, hs_zero]
  simp

theorem tauFusionTreeAssociator_tau_block_ne_identity
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ≠ 0) :
    (tauFusionTreeAssociator τ s).tau_comp ≠
      Matrix.reindex
        (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))
        (Equiv.cast (congrArg Fin tau_right_tree_tau_count.symm))
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have hmatrix : fibonacciFusionMatrix τ s = 1 := by
    apply (Matrix.reindexLinearEquiv ℂ ℂ
    (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))
    (Equiv.cast (congrArg Fin tau_right_tree_tau_count.symm))).injective
    simpa [tauFusionTreeAssociator] using h
  exact fibonacciFusionMatrix_ne_one_of_tau_ne_zero τ s hs hτ hmatrix

end InfoGeometry.Categorical.FibonacciFusionTreeAssociator
