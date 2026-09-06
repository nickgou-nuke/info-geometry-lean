/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.LeeYangAsanoKleinV4Compactification

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.LeeYangAsanoNativeCore

set_option linter.unusedVariables false



/-- Canonical projection capstone for the Lee-Yang Asano Klein-V4 compactification certificate. -/
theorem lee_yang_asano_klein_v4_compactification_canonical_capstone
    (hPole : ∀ {K₁ K₂ : Set ℂ} {A B C D z : ℂ},
      (0 : ℂ) ∉ K₁ → (0 : ℂ) ∉ K₂ → IsClosed K₁ → IsClosed K₂ → D ≠ 0 → A * D - B * C ≠ 0 →
      (∀ z₁ z₂ : ℂ, z₁ ∉ K₁ → z₂ ∉ K₂ → asanoPhi A B C D z₁ z₂ ≠ 0) → A + D * z = 0 →
      C ≠ 0 ∧ -(C / D) ∈ K₁) :
    let cert := AsanoKleinV4CompactificationCertificate.ofLeftPoleModel hPole
    ∀ {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
      (h0K₁ : (0 : ℂ) ∉ K₁)
      (h0K₂ : (0 : ℂ) ∉ K₂)
      (hClosed₁ : IsClosed K₁)
      (hClosed₂ : IsClosed K₂)
      (hD : D ≠ 0)
      (hDet : A * D - B * C ≠ 0)
      (hPhi : ∀ z₁ z₂ : ℂ, z₁ ∉ K₁ → z₂ ∉ K₂ → asanoPhi A B C D z₁ z₂ ≠ 0)
      (hroot : A + D * z = 0),
      (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂) := by
  intro cert K₁ K₂ A B C D z h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot
  exact endpoint_disjunction_of_kleinV4_compactification cert h0K₁ h0K₂ hClosed₁ hClosed₂ hD hDet hPhi hroot

end InfoGeometry.Canonical
