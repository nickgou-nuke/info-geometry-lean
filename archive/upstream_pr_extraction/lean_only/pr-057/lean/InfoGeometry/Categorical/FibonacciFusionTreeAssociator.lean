import InfoGeometry.Categorical.FibonacciBraidedCategory
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

end InfoGeometry.Categorical.FibonacciFusionTreeAssociator
