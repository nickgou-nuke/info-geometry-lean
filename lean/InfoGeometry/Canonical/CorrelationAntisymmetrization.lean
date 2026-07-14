import InfoGeometry.Canonical.CorrelationSymmetrization
import Mathlib.Tactic.Ring

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CorrelationAntisymmetrization

Antisymmetric / phase-side development of the owned two-state perturbation-channel
correlation surface.

This file does not duplicate the raw antisymmetric compression already owned in
`CorrelationSymmetrization`. Instead it develops the nontrivial skew lane:

- symmetric and antisymmetric compression of the `K = Jε`-shifted phase
  correlation;
- the corresponding decomposition laws;
- and the same-state alternating bridge to the owned comparison-state phase form
  under explicit phase-linearity hypotheses.
-/

namespace CorrelationAntisymmetrization

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.CorrelationSymmetrization
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- Symmetric compression of the `K = Jε`-shifted two-state channel correlation. -/
@[rep_depth krein]
noncomputable def symmetricPhaseShiftedTwoStateChannelCorrelation
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) : ℝ :=
  (phaseShiftedTwoStateChannelCorrelation (E := E) reference comparison X Y
    + phaseShiftedTwoStateChannelCorrelation (E := E) reference comparison Y X) / 2

/-- Antisymmetric compression of the `K = Jε`-shifted two-state channel correlation. -/
@[rep_depth krein]
noncomputable def antisymmetricPhaseShiftedTwoStateChannelCorrelation
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) : ℝ :=
  (phaseShiftedTwoStateChannelCorrelation (E := E) reference comparison X Y
    - phaseShiftedTwoStateChannelCorrelation (E := E) reference comparison Y X) / 2

/--
The `K = Jε`-shifted two-state channel correlation decomposes into its symmetric
and antisymmetric phase compressions.
-/
@[rep_depth krein]
theorem phaseShiftedTwoStateChannelCorrelation_eq_symmetric_add_antisymmetric
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    phaseShiftedTwoStateChannelCorrelation (E := E) reference comparison X Y
      =
    symmetricPhaseShiftedTwoStateChannelCorrelation (E := E) reference comparison X Y
      +
    antisymmetricPhaseShiftedTwoStateChannelCorrelation (E := E) reference comparison X Y := by
  unfold symmetricPhaseShiftedTwoStateChannelCorrelation
    antisymmetricPhaseShiftedTwoStateChannelCorrelation
  ring

/-- The symmetric phase compression is symmetric in the channel slots by construction. -/
@[rep_depth krein]
theorem symmetricPhaseShiftedTwoStateChannelCorrelation_swap
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    symmetricPhaseShiftedTwoStateChannelCorrelation (E := E) reference comparison X Y
      =
    symmetricPhaseShiftedTwoStateChannelCorrelation (E := E) reference comparison Y X := by
  unfold symmetricPhaseShiftedTwoStateChannelCorrelation
  ring

/-- The antisymmetric phase compression flips sign when the channel slots are swapped. -/
@[rep_depth krein]
theorem antisymmetricPhaseShiftedTwoStateChannelCorrelation_swap_neg
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    antisymmetricPhaseShiftedTwoStateChannelCorrelation (E := E) reference comparison X Y
      =
    -antisymmetricPhaseShiftedTwoStateChannelCorrelation (E := E) reference comparison Y X := by
  unfold antisymmetricPhaseShiftedTwoStateChannelCorrelation
  ring

/--
On the same-state slice, the `K = Jε`-shifted channel correlation is alternating
under phase-linearity of both channels.
-/
@[rep_depth krein]
theorem phaseShiftedTwoStateChannelCorrelation_self_swap_neg_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hY : IsPhaseLinear (E := E) Y) :
    phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y
      =
    -phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison Y X := by
  rw [← comparisonStateGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
      (E := E) comparison X Y]
  rw [← comparisonStateGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
      (E := E) comparison Y X]
  exact comparisonGeneratorPhase_swap_neg_of_IsPhaseLinear
    (E := E) comparison X Y hX hY

/--
On the same-state slice, the symmetric compression of the `K = Jε`-shifted
channel correlation vanishes under phase-linearity.
-/
@[rep_depth krein]
theorem symmetricPhaseShiftedTwoStateChannelCorrelation_self_eq_zero_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hY : IsPhaseLinear (E := E) Y) :
    symmetricPhaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y = 0 := by
  unfold symmetricPhaseShiftedTwoStateChannelCorrelation
  rw [phaseShiftedTwoStateChannelCorrelation_self_swap_neg_of_IsPhaseLinear
    (E := E) comparison X Y hX hY]
  ring

/--
On the same-state slice, the antisymmetric compression of the `K = Jε`-shifted
channel correlation reduces to the raw phase-shifted correlation under
phase-linearity.
-/
@[rep_depth krein]
theorem antisymmetricPhaseShiftedTwoStateChannelCorrelation_self_eq_raw_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hY : IsPhaseLinear (E := E) Y) :
    antisymmetricPhaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y
      =
    phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
  unfold antisymmetricPhaseShiftedTwoStateChannelCorrelation
  rw [phaseShiftedTwoStateChannelCorrelation_self_swap_neg_of_IsPhaseLinear
    (E := E) comparison X Y hX hY]
  ring

/--
The owned comparison-state phase form is exactly the same-state antisymmetric
`K = Jε`-shifted channel-correlation surface under phase-linearity.
-/
@[rep_depth krein]
theorem comparisonStateGeneratorPhase_eq_antisymmetricPhaseShiftedTwoStateChannelCorrelation_self_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hY : IsPhaseLinear (E := E) Y) :
    comparisonStateGeneratorPhase (E := E) comparison X Y
      =
    antisymmetricPhaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
  calc
    comparisonStateGeneratorPhase (E := E) comparison X Y
        =
      phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
          exact comparisonStateGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
            (E := E) comparison X Y
    _ =
      antisymmetricPhaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
          rw [antisymmetricPhaseShiftedTwoStateChannelCorrelation_self_eq_raw_of_IsPhaseLinear
            (E := E) comparison X Y hX hY]

/--
Constructive relational-data form of the same-state antisymmetric `K = Jε`-shifted
channel-correlation bridge under phase-linearity.
-/
@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonGeneratorPhase_eq_antisymmetricPhaseShiftedTwoStateChannelCorrelation_self_of_IsPhaseLinear
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hY : IsPhaseLinear (E := E) Y) :
    comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      =
    antisymmetricPhaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
  calc
    comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
        =
      phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
          exact
            toRelationalInformationDatum_comparisonGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
              (E := E) P reference comparison X Y
    _ =
      antisymmetricPhaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y := by
          rw [antisymmetricPhaseShiftedTwoStateChannelCorrelation_self_eq_raw_of_IsPhaseLinear
            (E := E) comparison X Y hX hY]

end Core

end CorrelationAntisymmetrization
