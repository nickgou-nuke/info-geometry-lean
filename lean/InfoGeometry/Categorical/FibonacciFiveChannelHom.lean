import InfoGeometry.Categorical.FibonacciFiveChannelAssociator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.FibonacciPentagonPathCarrier

/-!
# The five-channel block as an actual Fibonacci Hom-space morphism

The `2 ⊕ 3` matrix is now also packaged in the existing `FibHom` carrier.
This is a finite Hom-space result only.  It does not identify this morphism
with one of the five parenthesized pentagon edges; that requires an explicit
choice of fusion-tree bases.
-/

namespace InfoGeometry.Categorical.FibonacciFiveChannelHom

open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciFiveChannelAssociator
open InfoGeometry.Categorical.FibonacciFusionTreeAssociator
open InfoGeometry.Categorical.FibonacciPentagonPathCarrier

noncomputable def fourTauFiveChannelHom (τ s : ℂ) :
    FibHom (parenthesizedObject .vertex₁) (parenthesizedObject .vertex₁) :=
  by
    have hu : 2 = (parenthesizedObject .vertex₁) FibSimple.unit :=
      (parenthesizedObject_counts .vertex₁).1.symm
    have ht : 3 = (parenthesizedObject .vertex₁) FibSimple.tau :=
      (parenthesizedObject_counts .vertex₁).2.symm
    exact
      { unit_comp := Matrix.reindex (Equiv.cast (congrArg Fin hu))
          (Equiv.cast (congrArg Fin hu)) (fibonacciFusionMatrix τ s)
        tau_comp := Matrix.reindex (Equiv.cast (congrArg Fin ht))
          (Equiv.cast (congrArg Fin ht)) (1 : Matrix (Fin 3) (Fin 3) ℂ) }

noncomputable def fourTauFiveChannelHomInv (τ s : ℂ) :
    FibHom (parenthesizedObject .vertex₁) (parenthesizedObject .vertex₁) :=
  fourTauFiveChannelHom τ s

theorem fourTauFiveChannelHom_comp_inv
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (fourTauFiveChannelHom τ s)
        (fourTauFiveChannelHomInv τ s) =
      FibHom.id (parenthesizedObject .vertex₁) := by
  apply FibHom.ext
  · simp [fourTauFiveChannelHom, fourTauFiveChannelHomInv, FibHom.comp,
      FibHom.id,
      fibonacciFusionMatrix_sq hs hτ]
  · simp [fourTauFiveChannelHom, fourTauFiveChannelHomInv, FibHom.comp,
      FibHom.id]

theorem fourTauFiveChannelHom_inv_comp
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FibHom.comp (fourTauFiveChannelHomInv τ s)
        (fourTauFiveChannelHom τ s) =
      FibHom.id (parenthesizedObject .vertex₁) := by
  exact fourTauFiveChannelHom_comp_inv τ s hs hτ

noncomputable def fourTauFiveChannelIso
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    parenthesizedObject .vertex₁ ≅ parenthesizedObject .vertex₁ :=
  { hom := fourTauFiveChannelHom τ s
    inv := fourTauFiveChannelHomInv τ s
    hom_inv_id := fourTauFiveChannelHom_comp_inv τ s hs hτ
    inv_hom_id := fourTauFiveChannelHom_inv_comp τ s hs hτ }

theorem fourTauFiveChannelHom_unit_block_ne_identity
    (τ s : ℂ) (hs : s ^ 2 = τ) (hτ : τ ≠ 0) :
    (fourTauFiveChannelHom τ s).unit_comp ≠ 1 := by
  intro h
  apply fibonacciFusionMatrix_ne_one_of_tau_ne_zero τ s hs hτ
  apply (Matrix.reindexLinearEquiv ℂ ℂ
    (Equiv.cast (congrArg Fin
      (parenthesizedObject_counts .vertex₁).1.symm))
    (Equiv.cast (congrArg Fin
      (parenthesizedObject_counts .vertex₁).1.symm))).injective
  simpa [fourTauFiveChannelHom] using h

end InfoGeometry.Categorical.FibonacciFiveChannelHom
