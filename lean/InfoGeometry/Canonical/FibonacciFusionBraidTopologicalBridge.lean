import InfoGeometry.Canonical.ContinuousLeftActionTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/-!
# Topological Fibonacci fusion-space braid transport

The finite two-channel fusion carrier is a matrix algebra with its native
product topology.  Algebraic Artin and fusion involution identities therefore
transport to `TopCat` through the regular continuous action.  This is only the
finite matrix realization; it does not assert an analytic conformal-block
construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.FibonacciFusionBraidTopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical.ContinuousLeftActionTopCat
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

abbrev FusionCarrier := Matrix (Fin 2) (Fin 2) ℂ

abbrev fusionRegularAction : ContinuousLeftAction FusionCarrier FusionCarrier :=
  regularLeftAction

theorem fusion_braid_artin_topCat
    (R B : FusionCarrier)
    (hArtin : R * B * R = B * R * B) :
    translation fusionRegularAction R ≫
        translation fusionRegularAction B ≫
        translation fusionRegularAction R =
      translation fusionRegularAction B ≫
        translation fusionRegularAction R ≫
        translation fusionRegularAction B := by
  rw [translation_word, translation_word]
  exact congrArg (fun z : FusionCarrier => translation fusionRegularAction z)
    hArtin

theorem fusion_involution_topCat
    (F : FusionCarrier) (hF : F * F = 1) :
    translation fusionRegularAction F ≫
        translation fusionRegularAction F =
      𝟙 (TopCat.of FusionCarrier) := by
  rw [translation_comp, hF]
  exact translation_one fusionRegularAction

theorem fibonacci_fusion_involution_topCat
    {τ s : ℂ} (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    translation fusionRegularAction (fibonacciFusionMatrix τ s) ≫
        translation fusionRegularAction (fibonacciFusionMatrix τ s) =
      𝟙 (TopCat.of FusionCarrier) := by
  apply fusion_involution_topCat
  exact fibonacciFusionMatrix_sq hs hτ

theorem fibonacci_middle_braid_conjugation_topCat (q : Units ℂ) (τ s : ℂ) :
    translation fusionRegularAction (fibonacciBMatrix q τ s) =
      translation fusionRegularAction (fibonacciFusionMatrix τ s) ≫
        translation fusionRegularAction (fibonacciRMatrix q) ≫
        translation fusionRegularAction (fibonacciFusionMatrix τ s) := by
  rw [translation_word]
  rfl

theorem fibonacci_fourAnyon_artin_topCat
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    translation fusionRegularAction (fibonacciRMatrix q) ≫
        translation fusionRegularAction (fibonacciBMatrix q τ s) ≫
        translation fusionRegularAction (fibonacciRMatrix q) =
      translation fusionRegularAction (fibonacciBMatrix q τ s) ≫
        translation fusionRegularAction (fibonacciRMatrix q) ≫
        translation fusionRegularAction (fibonacciBMatrix q τ s) := by
  apply fusion_braid_artin_topCat
  exact fibonacci_fourAnyon_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs

end InfoGeometry.Canonical.FibonacciFusionBraidTopologicalBridge
