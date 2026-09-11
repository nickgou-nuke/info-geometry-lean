import InfoGeometry.Canonical.LeeYangAsanoFullReduction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LeeYangAsanoScaleNeighborhood

/-!
# Full Asano reduction from the explicit Möbius scale endpoint

This owner composes the explicit pole-scale bounded-escape theorem with the
native algebraic `D = 0` and determinant-zero branches.  It removes the
abstract nondegenerate `hTop` premise for the concrete closed-left/
bounded-right setting.  No colimit, compactification, or Weyl-gauge claim is
introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoNativeCore

open InfoGeometry.Canonical.LeeYangAsanoScaleNeighborhood

theorem asano_contraction_full_of_explicit_scale
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hBdd₂ : Bornology.IsBounded K₂)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hzOff : z ∉ negProductSet K₁ K₂) :
    A + D * z ≠ 0 := by
  have hzf :
      InfoGeometry.Analysis.AsanoContractionNative.ZeroFreeOutside
        K₁ K₂ A B C D := by
    intro z₁ z₂ hz₁ hz₂
    simpa [InfoGeometry.Analysis.AsanoContractionNative.ZeroFreeOutside,
      InfoGeometry.Analysis.AsanoContractionNative.asanoPoly, asanoPhi] using
      hPhi z₁ z₂ hz₁ hz₂
  by_cases hD : D = 0
  · subst D
    have hA :=
      InfoGeometry.Analysis.AsanoContractionNative.coeff_A_ne_zero_of_zeroFreeOutside
        h0K₁ h0K₂ hzf
    intro hz
    apply hA
    simpa using hz
  · by_cases hdet : A * D - B * C = 0
    · exact asano_det_zero_contraction_nonzero_off_negProductSet
        h0K₁ h0K₂ hD hdet hzf hzOff
    · intro hroot
      have hend :
          (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨
            (B ≠ 0 ∧ -(B / D) ∈ K₂) :=
        asano_endpoint_disjunction_left_of_explicit_scale
          A B C D K₁ K₂ hD hdet hClosed₁ hBdd₂ h0K₁ hPhi
      exact hzOff
        (asano_nondegenerate_root_mem_negProductSet_of_endpoint
          h0K₁ h0K₂ hD hPhi hroot hend)

theorem asano_contraction_root_mem_negProductSet_of_explicit_scale
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hBdd₂ : Bornology.IsBounded K₂)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hroot : A + D * z = 0) :
    z ∈ negProductSet K₁ K₂ := by
  by_contra hzOff
  exact
    (asano_contraction_full_of_explicit_scale
      h0K₁ h0K₂ hClosed₁ hBdd₂ hPhi hzOff) hroot

end InfoGeometry.Canonical.LeeYangAsanoNativeCore
