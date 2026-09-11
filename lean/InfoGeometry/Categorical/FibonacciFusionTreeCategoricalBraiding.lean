import InfoGeometry.Categorical.FibonacciFusionTreeAssociator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.FibonacciFusionTreeBraiding

/-!
# Sector-level categorical braiding on the Fibonacci fusion-tree block

The existing `bLinearEquiv` is the finite `B = F R F` action on the two
dimensional `τ ⊗ τ ⊗ τ` fusion multiplicity space.  This owner packages the
same block as a genuine `FibHom` isomorphism on that fixed sector.  It does
not claim naturality for all objects or a global `BraidedCategory` instance.
-/

namespace InfoGeometry.Categorical.FibonacciFusionTreeCategoricalBraiding

open InfoGeometry.Categorical.FibonacciBraidedCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciFusionTreeAssociator
open InfoGeometry.Categorical.FibonacciFusionTreeBraiding
open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

noncomputable def tauFusionTreeBraiding (q : Units ℂ) (τ s : ℂ) :
    FibHom (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) := by
  have hu : 1 = (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      FibSimple.unit := tau_left_tree_unit_count.symm
  have ht : 2 = (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      FibSimple.tau := tau_left_tree_tau_count.symm
  exact
    { unit_comp := Matrix.reindex (Equiv.cast (congrArg Fin hu))
        (Equiv.cast (congrArg Fin hu))
        (1 : Matrix (Fin 1) (Fin 1) ℂ)
      tau_comp := Matrix.reindex (Equiv.cast (congrArg Fin ht))
        (Equiv.cast (congrArg Fin ht))
        (fibonacciBMatrix q τ s) }

noncomputable def tauFusionTreeBraidingInv (q : Units ℂ) (τ s : ℂ) :
    FibHom (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) :=
  tauFusionTreeBraiding q⁻¹ τ s

noncomputable def tauFusionTreeR (q : Units ℂ) :
    FibHom (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) := by
  have hu : 1 = (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      FibSimple.unit := tau_left_tree_unit_count.symm
  have ht : 2 = (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      FibSimple.tau := tau_left_tree_tau_count.symm
  exact
    { unit_comp := (Matrix.reindex (Equiv.cast (congrArg Fin hu))
        (Equiv.cast (congrArg Fin hu))
      (1 : Matrix (Fin 1) (Fin 1) ℂ))
      tau_comp := (Matrix.reindex (Equiv.cast (congrArg Fin ht))
        (Equiv.cast (congrArg Fin ht))
        (fibonacciRMatrix q)) }

noncomputable def tauFusionTreeRInv (q : Units ℂ) :
    FibHom (fibTensorObj (fibTensorObj tauObject tauObject) tauObject)
      (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) :=
  tauFusionTreeR (q⁻¹)

theorem tauFusionTreeR_comp_inv (q : Units ℂ) :
    FibHom.comp (tauFusionTreeR q) (tauFusionTreeRInv q) =
      FibHom.id (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, tauFusionTreeR, tauFusionTreeRInv]
  · simp [FibHom.comp, FibHom.id, tauFusionTreeR, tauFusionTreeRInv,
      rMatrix_mul_inv, Matrix.reindexLinearEquiv_mul]

theorem tauFusionTreeR_inv_comp (q : Units ℂ) :
    FibHom.comp (tauFusionTreeRInv q) (tauFusionTreeR q) =
      FibHom.id (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, tauFusionTreeR, tauFusionTreeRInv]
  · simp [FibHom.comp, FibHom.id, tauFusionTreeR, tauFusionTreeRInv,
      rMatrix_inv_mul, Matrix.reindexLinearEquiv_mul]

noncomputable def tauFusionTreeRIso (q : Units ℂ) :
    fibTensorObj (fibTensorObj tauObject tauObject) tauObject ≅
      fibTensorObj (fibTensorObj tauObject tauObject) tauObject :=
  { hom := tauFusionTreeR q
    inv := tauFusionTreeRInv q
    hom_inv_id := tauFusionTreeR_comp_inv q
    inv_hom_id := tauFusionTreeR_inv_comp q }

theorem tauFusionTreeBraiding_comp_inv
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (tauFusionTreeBraiding q τ s)
        (tauFusionTreeBraidingInv q τ s) =
      FibHom.id (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, tauFusionTreeBraiding,
      tauFusionTreeBraidingInv]
  · simp [FibHom.comp, FibHom.id, tauFusionTreeBraiding,
      tauFusionTreeBraidingInv, bMatrix_mul_inv, hs, hτ,
      Matrix.reindexLinearEquiv_mul]

theorem tauFusionTreeBraiding_inv_comp
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (tauFusionTreeBraidingInv q τ s)
        (tauFusionTreeBraiding q τ s) =
      FibHom.id (fibTensorObj (fibTensorObj tauObject tauObject) tauObject) := by
  apply FibHom.ext
  · simp [FibHom.comp, FibHom.id, tauFusionTreeBraiding,
      tauFusionTreeBraidingInv]
  · simp [FibHom.comp, FibHom.id, tauFusionTreeBraiding,
      tauFusionTreeBraidingInv, bMatrix_inv_mul, hs, hτ,
      Matrix.reindexLinearEquiv_mul]

noncomputable def tauFusionTreeBraidingIso
    (q : Units ℂ) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibTensorObj (fibTensorObj tauObject tauObject) tauObject ≅
      fibTensorObj (fibTensorObj tauObject tauObject) tauObject :=
  { hom := tauFusionTreeBraiding q τ s
    inv := tauFusionTreeBraidingInv q τ s
    hom_inv_id := tauFusionTreeBraiding_comp_inv q τ s hs hτ
    inv_hom_id := tauFusionTreeBraiding_inv_comp q τ s hs hτ }

theorem tauFusionTreeBraiding_tau_block
    (q : Units ℂ) (τ s : ℂ) :
    (tauFusionTreeBraiding q τ s).tau_comp =
      Matrix.reindex
        (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))
        (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))
        (fibonacciBMatrix q τ s) := by
  rfl

theorem fibonacciRMatrix_ne_one_of_first_phase_ne_one
    (q : Units ℂ) (hphase : (q ^ (-4 : ℤ) : ℂ) ≠ 1) :
    fibonacciRMatrix q ≠ 1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  apply hphase
  simpa [fibonacciRMatrix] using h00

theorem tauFusionTreeR_tau_block_ne_identity
    (q : Units ℂ) (hphase : (q ^ (-4 : ℤ) : ℂ) ≠ 1) :
    (tauFusionTreeR q).tau_comp ≠
      Matrix.reindex
        (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))
        (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have hmatrix : fibonacciRMatrix q = 1 := by
    apply (Matrix.reindexLinearEquiv ℂ ℂ
      (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))
      (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))).injective
    simpa [tauFusionTreeR] using h
  exact fibonacciRMatrix_ne_one_of_first_phase_ne_one q hphase hmatrix

/-- The finite Artin relation lifted to the `1 ⊕ 2τ` fusion-tree block. -/
theorem tauFusionTree_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    FibHom.comp (FibHom.comp (tauFusionTreeR q)
      (tauFusionTreeBraiding q τ s)) (tauFusionTreeR q) =
      FibHom.comp (FibHom.comp (tauFusionTreeBraiding q τ s)
        (tauFusionTreeR q)) (tauFusionTreeBraiding q τ s) := by
  apply FibHom.ext
  · simp [FibHom.comp, tauFusionTreeR, tauFusionTreeBraiding]
  · simp [FibHom.comp, tauFusionTreeR, tauFusionTreeBraiding,
      Matrix.reindexLinearEquiv_mul]
    simpa using congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
        Matrix.reindex
          (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm))
          (Equiv.cast (congrArg Fin tau_left_tree_tau_count.symm)) M)
      (fibonacci_fourAnyon_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs)

/-! The same finite coherence is exposed in both orientations as a genuine
`FibHom` equality on the fixed fusion-tree sector.  This is the sector-level
hexagon readout; it is not a global natural hexagon for the skeletal category.
-/

theorem tauFusionTree_hexagon
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    FibHom.comp (FibHom.comp (tauFusionTreeBraiding q τ s)
      (tauFusionTreeR q)) (tauFusionTreeBraiding q τ s) =
      FibHom.comp (FibHom.comp (tauFusionTreeR q)
        (tauFusionTreeBraiding q τ s)) (tauFusionTreeR q) := by
  exact tauFusionTree_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs |>.symm

theorem tauFusionTree_hexagon_reverse
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    FibHom.comp (FibHom.comp (tauFusionTreeR q)
      (tauFusionTreeBraiding q τ s)) (tauFusionTreeR q) =
      FibHom.comp (FibHom.comp (tauFusionTreeBraiding q τ s)
        (tauFusionTreeR q)) (tauFusionTreeBraiding q τ s) := by
  exact tauFusionTree_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs

end InfoGeometry.Categorical.FibonacciFusionTreeCategoricalBraiding
