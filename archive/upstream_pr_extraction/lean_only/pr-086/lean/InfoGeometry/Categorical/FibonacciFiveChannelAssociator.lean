import InfoGeometry.Categorical.FibonacciFourAnyonCarrier
import InfoGeometry.Categorical.FibonacciBraidedCategory
import InfoGeometry.Categorical.FibonacciFusionTreeAssociator

/-!
# Five-channel Fibonacci fusion-path associator

This owner adds the next finite carrier above the two-dimensional fusion-tree
block.  The five channels are presented as a `2 ⊕ 3` path decomposition: the
nontrivial Fibonacci `F` block acts on the first two channels and the remaining
three channels are unchanged.  This is a local associator datum; it does not
yet identify all five parenthesized path bases or assert the global pentagon.
-/

namespace InfoGeometry.Categorical.FibonacciFiveChannelAssociator

open CategoryTheory
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciFourAnyonCarrier
open InfoGeometry.Categorical.FibonacciFusionTreeAssociator

abbrev FiveChannel := Fin 5 → ℂ

noncomputable def fiveChannelAssociatorMatrix (τ s : ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks
      (fibonacciFusionMatrix τ s)
      (0 : Matrix (Fin 2) (Fin 3) ℂ)
      (0 : Matrix (Fin 3) (Fin 2) ℂ)
      (1 : Matrix (Fin 3) (Fin 3) ℂ))

theorem fiveChannelAssociatorMatrix_sq
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fiveChannelAssociatorMatrix τ s * fiveChannelAssociatorMatrix τ s = 1 := by
  unfold fiveChannelAssociatorMatrix
  rw [← InfoGeometry.Categorical.FibonacciBraidedCategory.reindex_mul]
  rw [Matrix.fromBlocks_multiply]
  rw [fibonacciFusionMatrix_sq hs hτ]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add]
  rw [Matrix.fromBlocks_one]
  simpa [Matrix.reindexLinearEquiv] using
    (Matrix.reindexLinearEquiv_one (R := ℂ) (A := ℂ) finSumFinEquiv)

noncomputable def fiveChannelAssociatorIso
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    ModuleCat.of ℂ FiveChannel ≅ ModuleCat.of ℂ FiveChannel :=
  matrixIso
    (fiveChannelAssociatorMatrix τ s)
    (fiveChannelAssociatorMatrix τ s)
    (fiveChannelAssociatorMatrix_sq τ s hs hτ)
    (fiveChannelAssociatorMatrix_sq τ s hs hτ)

theorem fiveChannelAssociatorIso_hom
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (fiveChannelAssociatorIso τ s hs hτ).hom =
      matrixHom (fiveChannelAssociatorMatrix τ s) := by
  rfl

theorem fiveChannelAssociatorMatrix_ne_one
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ≠ 0) :
    fiveChannelAssociatorMatrix τ s ≠ 1 := by
  intro h
  have hblock :
      Matrix.fromBlocks
          (fibonacciFusionMatrix τ s)
          (0 : Matrix (Fin 2) (Fin 3) ℂ)
          (0 : Matrix (Fin 3) (Fin 2) ℂ)
          (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        1 := by
    apply (Matrix.reindexLinearEquiv ℂ ℂ finSumFinEquiv finSumFinEquiv).injective
    simpa [fiveChannelAssociatorMatrix] using h
  have hF : fibonacciFusionMatrix τ s = 1 := by
    rw [← Matrix.fromBlocks_one] at hblock
    exact (Matrix.fromBlocks_inj.mp hblock).1
  exact fibonacciFusionMatrix_ne_one_of_tau_ne_zero τ s hs hτ hF

end InfoGeometry.Categorical.FibonacciFiveChannelAssociator
