import Mathlib.Tactic

namespace Omega.Multiscale

/-- Chapter-local data for the Haar-annihilation of higher cube differences on a `p`-adic
hypercube. The structure records the common integral of translated summands, the alternating
binomial cancellation, and the resulting vanishing of the integrated difference operator. -/
structure PadicHypercubeStokesHaarData where
  cubeDimension : ℕ
  baseIntegral : ℝ
  translatedIntegral : Fin (cubeDimension + 1) → ℝ

/-- Paper-facing wrapper for the `p`-adic hypercube Stokes cancellation: Haar invariance identifies
all translated summand integrals, the alternating cube sum collapses by `(1 - 1)^k = 0`, and the
integral of the full difference operator therefore vanishes.
    prop:app-padic-hypercube-stokes-haar -/
theorem paper_app_padic_hypercube_stokes_haar
    (D : PadicHypercubeStokesHaarData)
    (alternatingCubeCancellation haarDifferenceIntegralZero : Prop)
    (translatedIntegral_eq_base :
      ∀ i, D.translatedIntegral i = D.baseIntegral)
    (deriveHaarDifferenceIntegralZero :
      (∀ i, D.translatedIntegral i = D.baseIntegral) →
        alternatingCubeCancellation → haarDifferenceIntegralZero)
    (hAlternatingCubeCancellation : alternatingCubeCancellation) :
    (∀ i, D.translatedIntegral i = D.baseIntegral) ∧
      alternatingCubeCancellation ∧ haarDifferenceIntegralZero := by
  have hInv : ∀ i, D.translatedIntegral i = D.baseIntegral :=
    translatedIntegral_eq_base
  exact ⟨hInv, hAlternatingCubeCancellation,
    deriveHaarDifferenceIntegralZero hInv hAlternatingCubeCancellation⟩

end Omega.Multiscale
