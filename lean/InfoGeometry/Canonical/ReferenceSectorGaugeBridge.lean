import InfoGeometry.Canonical.CanonicalGaugeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ReferenceSectorGaugeBridge

Projector-level refinement of the spectroscopic gauge-fixing bridge.

This file keeps the same low-ontology discipline as `CanonicalGaugeBridge`:
it introduces no new ensemble shell. Instead it makes explicit the theorem
surface saying that if two reference anchors lie in a common degenerate
projector sector, then the anchored relative potential is independent of which
reference anchor is chosen.
-/

namespace InfoGeometry.Canonical.ReferenceSectorGaugeBridge

open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.CanonicalGaugeBridge
open InfoGeometry.Krein

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
If two reference anchors have the same potential value, then anchoring the
comparison state against either one produces the same relative gap.
-/
@[rep_depth transport] theorem twoStateGap_eq_of_referenceValueEq
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hRef : value (E := E) P reference₀ = value (E := E) P reference₁) :
    twoStateGap (E := E) P reference₀ comparison
      =
    twoStateGap (E := E) P reference₁ comparison := by
  unfold twoStateGap
  rw [hRef]

/--
The relational functional shift is independent of the chosen anchor whenever
the two anchors have the same potential value.
-/
@[rep_depth transport] theorem functionalShift_eq_of_referenceValueEq
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hRef : value (E := E) P reference₀ = value (E := E) P reference₁) :
    functionalShift (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    functionalShift (toRelationalInformationDatum (E := E) P reference₁ comparison) := by
  repeat rw [toRelationalInformationDatum_functionalShift]
  exact twoStateGap_eq_of_referenceValueEq (E := E) P reference₀ reference₁ comparison hRef

/--
Projector-sector degeneracy hypothesis: the potential datum takes the same
value on every pair of fixed points of the projector.
-/
@[rep_depth transport] theorem twoStateGap_eq_of_projectorSectorDegeneracy
    (P : PotentialDatum (E := E))
    (Proj : EndH)
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, Proj ψ = ψ → Proj χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : Proj reference₀ = reference₀)
    (h₁ : Proj reference₁ = reference₁) :
    twoStateGap (E := E) P reference₀ comparison
      =
    twoStateGap (E := E) P reference₁ comparison := by
  apply twoStateGap_eq_of_referenceValueEq (E := E) P reference₀ reference₁ comparison
  exact hDeg reference₀ reference₁ h₀ h₁

/--
Under projector-sector degeneracy, the relational functional shift is
independent of which fixed reference anchor is chosen.
-/
@[rep_depth transport] theorem functionalShift_eq_of_projectorSectorDegeneracy
    (P : PotentialDatum (E := E))
    (Proj : EndH)
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, Proj ψ = ψ → Proj χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : Proj reference₀ = reference₀)
    (h₁ : Proj reference₁ = reference₁) :
    functionalShift (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    functionalShift (toRelationalInformationDatum (E := E) P reference₁ comparison) := by
  apply functionalShift_eq_of_referenceValueEq (E := E) P reference₀ reference₁ comparison
  exact hDeg reference₀ reference₁ h₀ h₁

/--
The comparison-state metric readout is reference-independent even after
expressing the statement through a degenerate projector sector.
-/
@[rep_depth transport] theorem comparisonMetricReadout_eq_of_projectorSectorDegeneracy
    (P : PotentialDatum (E := E))
    (Proj : EndH)
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (_hDeg :
      ∀ ψ χ : H₂, Proj ψ = ψ → Proj χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (_h₀ : Proj reference₀ = reference₀)
    (_h₁ : Proj reference₁ = reference₁) :
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  simpa using
    comparisonMetricReadout_referenceInvariant
      (E := E) P reference₀ reference₁ comparison A

/--
The comparison-state phase readout is reference-independent even after
expressing the statement through a degenerate projector sector.
-/
@[rep_depth transport] theorem comparisonPhaseReadout_eq_of_projectorSectorDegeneracy
    (P : PotentialDatum (E := E))
    (Proj : EndH)
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (_hDeg :
      ∀ ψ χ : H₂, Proj ψ = ψ → Proj χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (_h₀ : Proj reference₀ = reference₀)
    (_h₁ : Proj reference₁ = reference₁) :
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  simpa using
    comparisonPhaseReadout_referenceInvariant
      (E := E) P reference₀ reference₁ comparison A

end Core

end InfoGeometry.Canonical.ReferenceSectorGaugeBridge
