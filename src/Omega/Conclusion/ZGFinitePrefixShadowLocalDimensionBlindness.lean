/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import Omega.Conclusion.FiniteObservationCollisionObstruction

namespace Omega.Conclusion

/-- Concrete finite certificate package for the finite-prefix shadow blindness statement. The
finite types `Certificate` and `Shadow` model the observable prefix data, while `realize` exhibits
that every local-dimension value occurs inside every certificate atom. -/
structure ZGFinitePrefixShadowLocalDimensionBlindnessData where
  Point : Type
  Certificate : Type
  Shadow : Type
  LocalDimensionValue : Type
  certificateFintype : Fintype Certificate
  shadowFintype : Fintype Shadow
  certificate : Point → Certificate
  shadow : Point → Shadow
  localDimension : Point → LocalDimensionValue
  localDimensionDefined : Point → Prop
  baseCertificate : Certificate
  baseShadow : Shadow
  alpha₀ : LocalDimensionValue
  alpha₁ : LocalDimensionValue
  alpha_ne : alpha₀ ≠ alpha₁
  realize : Certificate → Shadow → LocalDimensionValue → Point
  realize_certificate :
    ∀ C η α, certificate (realize C η α) = C
  realize_shadow :
    ∀ C η α, shadow (realize C η α) = η
  realize_defined :
    ∀ C η α, localDimensionDefined (realize C η α)
  realize_localDimension :
    ∀ C η α, localDimension (realize C η α) = α

attribute [instance] ZGFinitePrefixShadowLocalDimensionBlindnessData.certificateFintype
attribute [instance] ZGFinitePrefixShadowLocalDimensionBlindnessData.shadowFintype

namespace ZGFinitePrefixShadowLocalDimensionBlindnessData

/-- The atom selected by a finite certificate and a finite shadow prefix. -/
def certificateAtom (D : ZGFinitePrefixShadowLocalDimensionBlindnessData)
    (C : D.Certificate) (η : D.Shadow) : Set D.Point :=
  {z | D.certificate z = C ∧ D.shadow z = η}

end ZGFinitePrefixShadowLocalDimensionBlindnessData

open ZGFinitePrefixShadowLocalDimensionBlindnessData

/-- Paper label:
`thm:conclusion-zg-finite-prefix-shadow-local-dimension-blindness`. -/
theorem paper_conclusion_zg_finite_prefix_shadow_local_dimension_blindness
    (D : ZGFinitePrefixShadowLocalDimensionBlindnessData) :
    (¬ ∃ Φ : D.Certificate → D.LocalDimensionValue,
      ∀ z, D.localDimensionDefined z → D.localDimension z = Φ (D.certificate z)) ∧
      (∀ C η α, ∃ z, z ∈ D.certificateAtom C η ∧ D.localDimension z = α) := by
  refine ⟨?_, ?_⟩
  · intro hΦ
    rcases hΦ with ⟨Φ, hΦ⟩
    have hcertificate :
        D.certificate (D.realize D.baseCertificate D.baseShadow D.alpha₀) =
          D.certificate (D.realize D.baseCertificate D.baseShadow D.alpha₁) := by
      simp only [D.realize_certificate]
    have hvalues :
        D.localDimension (D.realize D.baseCertificate D.baseShadow D.alpha₀) ≠
          D.localDimension (D.realize D.baseCertificate D.baseShadow D.alpha₁) := by
      simp only [D.realize_localDimension]
      exact D.alpha_ne
    exact no_valid_decoder_of_observation_collision D.certificate D.localDimension
      D.localDimensionDefined
      (D.realize_defined D.baseCertificate D.baseShadow D.alpha₀)
      (D.realize_defined D.baseCertificate D.baseShadow D.alpha₁)
      hcertificate hvalues ⟨Φ, hΦ⟩
  · intro C η α
    refine ⟨D.realize C η α, ?_, D.realize_localDimension C η α⟩
    simp [ZGFinitePrefixShadowLocalDimensionBlindnessData.certificateAtom,
      D.realize_certificate, D.realize_shadow]

end Omega.Conclusion
