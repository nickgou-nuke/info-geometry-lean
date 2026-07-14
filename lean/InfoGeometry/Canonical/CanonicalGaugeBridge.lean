import InfoGeometry.Canonical.RelativeModularPotential

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CanonicalGaugeBridge

Thin bridge file making the spectroscopic gauge-fixing surface explicit on top
of the existing relative modular potential owners.

The key point is that changing the reference state only shifts the anchored
potential by a constant cocycle, while the operatorial first-response and
comparison-state metric/phase readouts remain unchanged.
-/

namespace CanonicalGaugeBridge

open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Anchoring the comparison state against itself yields zero relative gap. -/
@[rep_depth transport, simp] theorem twoStateGap_self_eq_zero
    (P : PotentialDatum (E := E)) (reference : H₂) :
    twoStateGap (E := E) P reference reference = 0 := by
  unfold twoStateGap
  ring

/--
Changing the reference state shifts the anchored gap by a constant cocycle
independent of the comparison-state readout.
-/
@[rep_depth transport] theorem twoStateGap_reference_cocycle
    (P : PotentialDatum (E := E)) (reference₀ reference₁ comparison : H₂) :
    twoStateGap (E := E) P reference₀ comparison
      =
    twoStateGap (E := E) P reference₁ comparison
      +
    twoStateGap (E := E) P reference₀ reference₁ := by
  unfold twoStateGap
  ring

/-- The relational functional shift vanishes when the anchor and comparison agree. -/
@[rep_depth transport, simp] theorem functionalShift_self_eq_zero
    (P : PotentialDatum (E := E)) (reference : H₂) :
    functionalShift (toRelationalInformationDatum (E := E) P reference reference) = 0 := by
  rw [toRelationalInformationDatum_functionalShift]
  simp

/--
Changing the reference state only adds the anchored reference-to-reference
cocycle to the relational functional shift.
-/
@[rep_depth transport] theorem functionalShift_reference_cocycle
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂) :
    functionalShift (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    functionalShift (toRelationalInformationDatum (E := E) P reference₁ comparison)
      +
    twoStateGap (E := E) P reference₀ reference₁ := by
  repeat rw [toRelationalInformationDatum_functionalShift]
  exact twoStateGap_reference_cocycle (E := E) P reference₀ reference₁ comparison

/--
The comparison-state transport generator is invariant under a change of
reference anchor.
-/
@[rep_depth transport, simp] theorem comparisonTransportGenerator_referenceInvariant
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂) :
    comparisonTransportGenerator
        (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    comparisonTransportGenerator
        (toRelationalInformationDatum (E := E) P reference₁ comparison) := by
  rfl

/--
The comparison-state induced dynamics is invariant under a change of reference
anchor.
-/
@[rep_depth transport, simp] theorem comparisonInducedDynamics_referenceInvariant
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂) (A : EndH) :
    comparisonInducedDynamics
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    comparisonInducedDynamics
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  rfl

/--
The operatorial first variation depends only on the underlying potential datum,
not on the chosen reference anchor used to package the relational datum.
-/
@[rep_depth transport, simp] theorem firstVariation_referenceInvariant
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison ψ : H₂) (A : EndH) :
    (toRelationalInformationDatum (E := E) P reference₀ comparison).firstVariation ψ A
      =
    (toRelationalInformationDatum (E := E) P reference₁ comparison).firstVariation ψ A := by
  rfl

/--
The comparison-state second-variation metric is invariant under a change of
reference anchor.
-/
@[rep_depth transport, simp] theorem comparisonGeneratorMetric_referenceInvariant
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂) :
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference₁ comparison) := by
  rfl

/--
The comparison-state phase form is invariant under a change of reference
anchor.
-/
@[rep_depth transport, simp] theorem comparisonGeneratorPhase_referenceInvariant
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂) :
    comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference₀ comparison)
      =
    comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference₁ comparison) := by
  rfl

/--
The comparison-state metric readout is invariant under a change of reference
anchor.
-/
@[rep_depth transport, simp] theorem comparisonMetricReadout_referenceInvariant
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂) (A : EndH) :
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  rfl

/--
The comparison-state phase readout is invariant under a change of reference
anchor.
-/
@[rep_depth transport, simp] theorem comparisonPhaseReadout_referenceInvariant
    (P : PotentialDatum (E := E))
    (reference₀ reference₁ comparison : H₂) (A : EndH) :
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₀ comparison) A
      =
    RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference₁ comparison) A := by
  rfl

end Core

end CanonicalGaugeBridge
