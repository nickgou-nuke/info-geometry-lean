import InfoGeometry.Canonical.ModularTwoStateCorrelation
import Mathlib.Tactic.Ring

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CorrelationSymmetrization

Algebraic symmetrization layer for the owned two-state perturbation-channel
correlation surface.

This file deliberately stays weak:

- it does not introduce a new derivative or Hessian primitive;
- it only decomposes the existing `twoStateChannelCorrelation` into symmetric
  and antisymmetric parts;
- it records the same-state collapse of that decomposition; and
- it bridges the same-state symmetric surface to the already-owned
  comparison-state channel metric.
-/

namespace CorrelationSymmetrization

open InfoGeometry.Canonical.ModularTwoStateCorrelation
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- Symmetric compression of the raw two-state channel correlation at fixed states. -/
@[rep_depth krein]
noncomputable def symmetricTwoStateChannelCorrelation
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) : ℝ :=
  (twoStateChannelCorrelation (E := E) reference comparison X Y
    + twoStateChannelCorrelation (E := E) reference comparison Y X) / 2

/-- Antisymmetric compression of the raw two-state channel correlation at fixed states. -/
@[rep_depth krein]
noncomputable def antisymmetricTwoStateChannelCorrelation
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) : ℝ :=
  (twoStateChannelCorrelation (E := E) reference comparison X Y
    - twoStateChannelCorrelation (E := E) reference comparison Y X) / 2

/-- `K = Jε`-twisted two-state channel correlation at fixed states. -/
@[rep_depth krein]
noncomputable def phaseShiftedTwoStateChannelCorrelation
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) : ℝ :=
  twoStateChannelCorrelation (E := E) reference comparison
    (channelPhaseAxis (E := E) X) Y

/-- The raw two-state channel correlation decomposes into its symmetric and antisymmetric parts. -/
@[rep_depth krein]
theorem twoStateChannelCorrelation_eq_symmetric_add_antisymmetric
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    twoStateChannelCorrelation (E := E) reference comparison X Y
      =
    symmetricTwoStateChannelCorrelation (E := E) reference comparison X Y
      +
    antisymmetricTwoStateChannelCorrelation (E := E) reference comparison X Y := by
  unfold symmetricTwoStateChannelCorrelation antisymmetricTwoStateChannelCorrelation
  ring

/-- The symmetric compression is symmetric in the channel slots by construction. -/
@[rep_depth krein]
theorem symmetricTwoStateChannelCorrelation_swap
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    symmetricTwoStateChannelCorrelation (E := E) reference comparison X Y
      =
    symmetricTwoStateChannelCorrelation (E := E) reference comparison Y X := by
  unfold symmetricTwoStateChannelCorrelation
  ring

/-- The antisymmetric compression flips sign when the channel slots are swapped. -/
@[rep_depth krein]
theorem antisymmetricTwoStateChannelCorrelation_swap_neg
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    antisymmetricTwoStateChannelCorrelation (E := E) reference comparison X Y
      =
    -antisymmetricTwoStateChannelCorrelation (E := E) reference comparison Y X := by
  unfold antisymmetricTwoStateChannelCorrelation
  ring

/-- On a same-state slice, the symmetric compression reduces to the raw channel correlation. -/
@[rep_depth krein]
theorem symmetricTwoStateChannelCorrelation_self_eq_raw
    (comparison : H₂)
    (X Y : PerturbationChannel E) :
    symmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y
      =
    twoStateChannelCorrelation (E := E) comparison comparison X Y := by
  unfold symmetricTwoStateChannelCorrelation
  rw [twoStateChannelCorrelation_swap (E := E) comparison comparison X Y]
  ring

/-- On a same-state slice, the antisymmetric compression vanishes. -/
@[rep_depth krein]
theorem antisymmetricTwoStateChannelCorrelation_self_eq_zero
    (comparison : H₂)
    (X Y : PerturbationChannel E) :
    antisymmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y = 0 := by
  unfold antisymmetricTwoStateChannelCorrelation
  rw [twoStateChannelCorrelation_swap (E := E) comparison comparison X Y]
  ring

/-- The owned comparison-state metric is exactly the same-state symmetric correlation surface. -/
@[rep_depth krein]
theorem comparisonStateGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self
    (comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonStateGeneratorMetric (E := E) comparison X Y
      =
    symmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
  calc
    comparisonStateGeneratorMetric (E := E) comparison X Y
        =
      twoStateChannelCorrelation (E := E) comparison comparison X Y := by
          exact
            InfoGeometry.Canonical.ModularTwoStateCorrelation.comparisonGeneratorMetric_eq_twoStateChannelCorrelation_self
                (E := E) comparison X Y
    _ =
      symmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
          rw [symmetricTwoStateChannelCorrelation_self_eq_raw (E := E) comparison X Y]

/-- The owned comparison-state phase form is exactly the same-state `K`-twisted channel correlation surface. -/
@[rep_depth krein]
theorem comparisonStateGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
    (comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonStateGeneratorPhase (E := E) comparison X Y
      =
    phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
  simp [phaseShiftedTwoStateChannelCorrelation, comparisonStateGeneratorPhase_apply_eq_comp_complex_i,
    twoStateChannelCorrelation_apply, channelPhaseAxis_apply, ContinuousLinearMap.comp_apply]

/--
For relational data constructed from the primitive potential package, the
comparison-state metric is the same-state symmetric channel correlation.
-/
@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      =
    symmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
  calc
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
        =
      twoStateChannelCorrelation (E := E) comparison comparison X Y := by
          simp [twoStateChannelCorrelation_apply]
    _ =
      symmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
          rw [symmetricTwoStateChannelCorrelation_self_eq_raw (E := E) comparison X Y]

/--
For relational data constructed from the primitive potential package, the
comparison-state phase form is the same-state `K`-twisted channel correlation.
-/
@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      =
    phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
  simp [phaseShiftedTwoStateChannelCorrelation, twoStateChannelCorrelation_apply,
    channelPhaseAxis_apply, ContinuousLinearMap.comp_apply]

end Core

end CorrelationSymmetrization
