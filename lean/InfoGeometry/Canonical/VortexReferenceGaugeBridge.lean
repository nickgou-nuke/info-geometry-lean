import InfoGeometry.Canonical.ReferenceSectorGaugeBridge
import InfoGeometry.Canonical.VortexAnomalyLink

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.VortexReferenceGaugeBridge

Canonical source/sink specialization of the spectroscopic gauge-fixing bridge.

This file is a thin consumer of the generic projector-sector gauge bridge and
the canonical vortex pair. It makes the degenerate-reference story explicit in
the doubled Majorana source/sink language.
-/

namespace InfoGeometry.Canonical.VortexReferenceGaugeBridge

open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.ReferenceSectorGaugeBridge
open InfoGeometry.Canonical.VortexAnomalyLink
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable def sourceProj : EndH := (canonicalVortexPair (E := E)).source
noncomputable def sinkProj : EndH := (canonicalVortexPair (E := E)).sink

/--
If the potential datum is degenerate on the canonical source sector, then the
anchored comparison gap is independent of which source-sector anchor is chosen.
-/
@[rep_depth transport] theorem twoStateGap_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    twoStateGap (E := E) P reference₀ comparison
      =
    twoStateGap (E := E) P reference₁ comparison := by
  exact twoStateGap_eq_of_projectorSectorDegeneracy
    (E := E) P (sourceProj (E := E)) reference₀ reference₁ comparison hDeg h₀ h₁

/--
If the potential datum is degenerate on the canonical sink sector, then the
anchored comparison gap is independent of which sink-sector anchor is chosen.
-/
@[rep_depth transport] theorem twoStateGap_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    twoStateGap (E := E) P reference₀ comparison
      =
    twoStateGap (E := E) P reference₁ comparison := by
  exact twoStateGap_eq_of_projectorSectorDegeneracy
    (E := E) P (sinkProj (E := E)) reference₀ reference₁ comparison hDeg h₀ h₁

/--
Under source-sector degeneracy, the relational functional shift is independent
of which source anchor is chosen.
-/
@[rep_depth transport] theorem functionalShift_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    functionalShift (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    functionalShift (toRelationalInformationDatum (E := E) P reference₁ comparison) := by
  exact functionalShift_eq_of_projectorSectorDegeneracy
    (E := E) P (sourceProj (E := E)) reference₀ reference₁ comparison hDeg h₀ h₁

/--
Under sink-sector degeneracy, the relational functional shift is independent of
which sink anchor is chosen.
-/
@[rep_depth transport] theorem functionalShift_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    functionalShift (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    functionalShift (toRelationalInformationDatum (E := E) P reference₁ comparison) := by
  exact functionalShift_eq_of_projectorSectorDegeneracy
    (E := E) P (sinkProj (E := E)) reference₀ reference₁ comparison hDeg h₀ h₁

/--
The comparison-state metric readout can be stated directly in source-sector
gauge language.
-/
@[rep_depth transport] theorem comparisonMetricReadout_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  exact ReferenceSectorGaugeBridge.comparisonMetricReadout_eq_of_projectorSectorDegeneracy
    (E := E) P (sourceProj (E := E)) reference₀ reference₁ comparison A hDeg h₀ h₁

/--
The comparison-state phase readout can be stated directly in source-sector
gauge language.
-/
@[rep_depth transport] theorem comparisonPhaseReadout_eq_of_sourceSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (hDeg :
      ∀ ψ χ : H₂, sourceProj (E := E) ψ = ψ → sourceProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sourceProj (E := E) reference₀ = reference₀)
    (h₁ : sourceProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  exact ReferenceSectorGaugeBridge.comparisonPhaseReadout_eq_of_projectorSectorDegeneracy
    (E := E) P (sourceProj (E := E)) reference₀ reference₁ comparison A hDeg h₀ h₁

/--
The comparison-state metric readout can be stated directly in sink-sector
gauge language.
-/
@[rep_depth transport] theorem comparisonMetricReadout_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  exact ReferenceSectorGaugeBridge.comparisonMetricReadout_eq_of_projectorSectorDegeneracy
    (E := E) P (sinkProj (E := E)) reference₀ reference₁ comparison A hDeg h₀ h₁

/--
The comparison-state phase readout can be stated directly in sink-sector
gauge language.
-/
@[rep_depth transport] theorem comparisonPhaseReadout_eq_of_sinkSectorDegeneracy
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂)
    (A : EndH)
    (hDeg :
      ∀ ψ χ : H₂, sinkProj (E := E) ψ = ψ → sinkProj (E := E) χ = χ →
        value (E := E) P ψ = value (E := E) P χ)
    (h₀ : sinkProj (E := E) reference₀ = reference₀)
    (h₁ : sinkProj (E := E) reference₁ = reference₁) :
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  exact ReferenceSectorGaugeBridge.comparisonPhaseReadout_eq_of_projectorSectorDegeneracy
    (E := E) P (sinkProj (E := E)) reference₀ reference₁ comparison A hDeg h₀ h₁

end Core

end InfoGeometry.Canonical.VortexReferenceGaugeBridge
