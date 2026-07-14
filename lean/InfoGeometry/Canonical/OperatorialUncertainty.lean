import InfoGeometry.Canonical.CorrelationSymmetrization
import InfoGeometry.Canonical.OperatorialCramerRao

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialUncertainty

Noncommutative uncertainty layer derived from the operatorial comparison-state
channel metric.

This file stays on the owned doubled-carrier theorem spine:

- the primitive comparison-state channel metric,
- the `K = Jε` phase axis acting on perturbation channels,
- the operatorial Cramer-Rao / Cauchy-Schwarz bound, and
- the same-state phase-shifted two-channel correlation surface.

No scalar Fisher replacement, diagonal Hessian model, or external spacetime
phase space is introduced here.
-/

namespace OperatorialUncertainty

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.CorrelationSymmetrization
open InfoGeometry.Canonical.OperatorialCramerRao
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Robertson-Schrödinger area bound on the doubled carrier for the internal phase
axis `K = Jε`.
-/
@[rep_depth krein]
theorem inner_sq_add_modularComplexI_inner_sq_le
    (x y : H₂) :
    (⟪x, y⟫_ℝ) ^ 2 + (⟪modularComplexI (E := E) x, y⟫_ℝ) ^ 2
      ≤
    ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  let kx : H₂ := complex_i (E := E) x
  have hKnormSq : ‖kx‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simpa [kx] using complex_i_inner_comp (E := E) x x
  have hKnorm : ‖kx‖ = ‖x‖ := by
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hKnormSq
  have hNormNe : ‖x‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hx
  have hkx : kx ≠ 0 := by
    have hKnormNe : ‖kx‖ ≠ 0 := by
      simpa [hKnorm] using hNormNe
    exact norm_ne_zero_iff.mp hKnormNe
  have hOrth : ⟪x, kx⟫_ℝ = 0 := by
    have hSkew := complex_i_inner_skew (E := E) x x
    have hEqNegBase :
        ⟪x, complex_i (E := E) x⟫_ℝ
          =
        -⟪x, complex_i (E := E) x⟫_ℝ := by
      calc
        ⟪x, complex_i (E := E) x⟫_ℝ
            = ⟪complex_i (E := E) x, x⟫_ℝ := by rw [real_inner_comm]
        _ = -⟪x, complex_i (E := E) x⟫_ℝ := hSkew
    have hEqNeg : ⟪x, kx⟫_ℝ = -⟪x, kx⟫_ℝ := by
      simpa [kx] using hEqNegBase
    have hZeroSum : ⟪x, kx⟫_ℝ + ⟪x, kx⟫_ℝ = 0 := by
      exact eq_neg_iff_add_eq_zero.mp hEqNeg
    have hTwo : (2 : ℝ) * ⟪x, kx⟫_ℝ = 0 := by
      simpa [two_mul] using hZeroSum
    linarith
  have hOrthNorm :
      ⟪NormedSpace.normalize x, NormedSpace.normalize kx⟫_ℝ = 0 := by
    rw [NormedSpace.normalize, NormedSpace.normalize,
      real_inner_smul_left, real_inner_smul_right, hOrth]
    ring
  let v : Fin 2 → H₂ := ![NormedSpace.normalize x, NormedSpace.normalize kx]
  have hv : Orthonormal ℝ v := by
    constructor
    · intro i
      fin_cases i
      · simpa [v] using NormedSpace.norm_normalize hx
      · simpa [v] using NormedSpace.norm_normalize hkx
    · intro i j hij
      fin_cases i <;> fin_cases j
      · contradiction
      · simpa [v] using hOrthNorm
      · simpa [v, real_inner_comm] using hOrthNorm
      · contradiction
  have hBessel :
      ‖⟪NormedSpace.normalize x, y⟫_ℝ‖ ^ 2
        + ‖⟪NormedSpace.normalize kx, y⟫_ℝ‖ ^ 2
      ≤
      ‖y‖ ^ 2 := by
    simpa [v] using hv.sum_inner_products_le (x := y) (s := Finset.univ)
  have hScaled :=
    mul_le_mul_of_nonneg_left hBessel (by positivity : 0 ≤ ‖x‖ ^ 2)
  have hLhs :
      ‖x‖ ^ 2
          *
        (‖⟪NormedSpace.normalize x, y⟫_ℝ‖ ^ 2
          + ‖⟪NormedSpace.normalize kx, y⟫_ℝ‖ ^ 2)
        =
      (⟪x, y⟫_ℝ) ^ 2 + (⟪kx, y⟫_ℝ) ^ 2 := by
    rw [NormedSpace.normalize, NormedSpace.normalize, real_inner_smul_left, real_inner_smul_left]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, hKnorm]
    field_simp [pow_two, hNormNe]
  rw [hLhs] at hScaled
  simpa [kx, InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i,
    mul_assoc, mul_left_comm, mul_comm] using hScaled

@[rep_depth krein]
theorem inner_sq_add_complex_i_inner_sq_le
    (x y : H₂) :
    (⟪x, y⟫_ℝ) ^ 2 + (⟪InfoGeometry.Krein.complex_i (E := E) x, y⟫_ℝ) ^ 2
      ≤
    ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  simpa [modularComplexI_eq_complex_i] using
    inner_sq_add_modularComplexI_inner_sq_le (E := E) x y

/-- The comparison-state phase form is the metric with a left `K = Jε` channel twist. -/
@[rep_depth krein, simp]
theorem comparisonStateGeneratorMetric_channelPhaseAxis_left_eq_phase
    (comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonStateGeneratorMetric (E := E) comparison (channelPhaseAxis (E := E) X) Y
      =
    comparisonStateGeneratorPhase (E := E) comparison X Y := by
  simp [comparisonStateGeneratorMetric_apply, comparisonStateGeneratorPhase_apply_eq_comp_complex_i,
    channelPhaseAxis_apply, ContinuousLinearMap.comp_apply]

/--
For a phase-linear perturbation channel, the `K = Jε` channel twist preserves
the diagonal comparison-state metric.
-/
@[rep_depth krein]
theorem comparisonStateGeneratorMetric_channelPhaseAxis_self_eq_self_of_IsPhaseLinear
    (comparison : H₂)
    (X : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X) :
    comparisonStateGeneratorMetric (E := E) comparison
        (channelPhaseAxis (E := E) X) (channelPhaseAxis (E := E) X)
      =
    comparisonStateGeneratorMetric (E := E) comparison X X := by
  have hEval :
      (channelPhaseAxis (E := E) X) comparison
        =
      InfoGeometry.Krein.complex_i (E := E) (X comparison) := by
    simpa [channelPhaseAxis_apply, IsPhaseLinear,
      ContinuousLinearMap.comp_apply, modularComplexI_eq_complex_i] using
      congrArg (fun T : EndH => T comparison) hX
  calc
    comparisonStateGeneratorMetric (E := E) comparison
        (channelPhaseAxis (E := E) X) (channelPhaseAxis (E := E) X)
        =
      ‖(channelPhaseAxis (E := E) X) comparison‖ ^ 2 := by
          exact comparisonStateGeneratorMetric_self_eq_norm_sq
            (E := E) comparison (channelPhaseAxis (E := E) X)
    _ = ‖InfoGeometry.Krein.complex_i (E := E) (X comparison)‖ ^ 2 := by rw [hEval]
    _ = ‖X comparison‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
          exact complex_i_inner_comp (E := E) (X comparison) (X comparison)
    _ = comparisonStateGeneratorMetric (E := E) comparison X X := by
          symm
          exact comparisonStateGeneratorMetric_self_eq_norm_sq (E := E) comparison X

/--
Phase response is bounded by the diagonal comparison-state channel costs when
the left channel is `K = Jε`-equivariant.
-/
@[rep_depth krein]
theorem comparisonStateGeneratorPhase_sq_le_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X) :
    (comparisonStateGeneratorPhase (E := E) comparison X Y) ^ 2
      ≤
    comparisonStateGeneratorMetric (E := E) comparison X X
      * comparisonStateGeneratorMetric (E := E) comparison Y Y := by
  have hCS :=
    comparisonStateGeneratorMetric_sq_le (E := E) comparison
      (channelPhaseAxis (E := E) X) Y
  calc
    (comparisonStateGeneratorPhase (E := E) comparison X Y) ^ 2
        =
      (comparisonStateGeneratorMetric (E := E) comparison
        (channelPhaseAxis (E := E) X) Y) ^ 2 := by
          rw [comparisonStateGeneratorMetric_channelPhaseAxis_left_eq_phase]
    _ ≤
      comparisonStateGeneratorMetric (E := E) comparison
        (channelPhaseAxis (E := E) X) (channelPhaseAxis (E := E) X)
        *
      comparisonStateGeneratorMetric (E := E) comparison Y Y := hCS
    _ =
      comparisonStateGeneratorMetric (E := E) comparison X X
        *
      comparisonStateGeneratorMetric (E := E) comparison Y Y := by
          rw [comparisonStateGeneratorMetric_channelPhaseAxis_self_eq_self_of_IsPhaseLinear
            (E := E) (comparison := comparison) (X := X) hX]

/--
Robertson-Schrödinger area law on the operatorial comparison-state channel
surface.
-/
@[rep_depth krein]
theorem comparisonStateGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X) :
    (comparisonStateGeneratorMetric (E := E) comparison X Y) ^ 2
      +
    (comparisonStateGeneratorPhase (E := E) comparison X Y) ^ 2
      ≤
    comparisonStateGeneratorMetric (E := E) comparison X X
      * comparisonStateGeneratorMetric (E := E) comparison Y Y := by
  have hEval :
      (channelPhaseAxis (E := E) X) comparison
        =
      InfoGeometry.Krein.complex_i (E := E) (X comparison) := by
    simpa [channelPhaseAxis_apply, IsPhaseLinear,
      ContinuousLinearMap.comp_apply, modularComplexI_eq_complex_i] using
      congrArg (fun T : EndH => T comparison) hX
  have hPhaseEval :
      comparisonStateGeneratorPhase (E := E) comparison X Y
        =
      ⟪InfoGeometry.Krein.complex_i (E := E) (X comparison), Y comparison⟫_ℝ := by
    rw [← comparisonStateGeneratorMetric_channelPhaseAxis_left_eq_phase]
    rw [comparisonStateGeneratorMetric_apply, hEval]
  have hVec :=
    inner_sq_add_complex_i_inner_sq_le (E := E) (X comparison) (Y comparison)
  calc
    (comparisonStateGeneratorMetric (E := E) comparison X Y) ^ 2
        +
      (comparisonStateGeneratorPhase (E := E) comparison X Y) ^ 2
      =
    (⟪X comparison, Y comparison⟫_ℝ) ^ 2
        +
      (⟪InfoGeometry.Krein.complex_i (E := E) (X comparison), Y comparison⟫_ℝ) ^ 2 := by
          rw [comparisonStateGeneratorMetric_apply, hPhaseEval]
    _ ≤ ‖X comparison‖ ^ 2 * ‖Y comparison‖ ^ 2 := hVec
    _ = comparisonStateGeneratorMetric (E := E) comparison X X
          * comparisonStateGeneratorMetric (E := E) comparison Y Y := by
          rw [comparisonStateGeneratorMetric_self_eq_norm_sq,
            comparisonStateGeneratorMetric_self_eq_norm_sq]

/--
Unit phase response forces the same inverse lower bound as the operatorial
Cramer-Rao inequality, provided the left channel is phase-linear.
-/
@[rep_depth krein]
theorem inv_comparisonStateGeneratorMetric_self_le_of_unit_phase_response_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hUnit : comparisonStateGeneratorPhase (E := E) comparison X Y = 1)
    (hY : Y comparison ≠ 0) :
    1 / comparisonStateGeneratorMetric (E := E) comparison Y Y
      ≤
    comparisonStateGeneratorMetric (E := E) comparison X X := by
  have hUnitMetric :
      comparisonStateGeneratorMetric (E := E) comparison
          (channelPhaseAxis (E := E) X) Y
        = 1 := by
    simpa [comparisonStateGeneratorMetric_channelPhaseAxis_left_eq_phase] using hUnit
  have hInv :=
    inv_comparisonStateGeneratorMetric_self_le_of_unit_response
      (E := E) comparison (channelPhaseAxis (E := E) X) Y hUnitMetric hY
  calc
    1 / comparisonStateGeneratorMetric (E := E) comparison Y Y
      ≤
    comparisonStateGeneratorMetric (E := E) comparison
      (channelPhaseAxis (E := E) X) (channelPhaseAxis (E := E) X) := hInv
    _ = comparisonStateGeneratorMetric (E := E) comparison X X := by
          rw [comparisonStateGeneratorMetric_channelPhaseAxis_self_eq_self_of_IsPhaseLinear
            (E := E) (comparison := comparison) (X := X) hX]

/--
On the same-state slice, the `K = Jε`-shifted channel-correlation surface
satisfies the same uncertainty bound.
-/
@[rep_depth krein]
theorem phaseShiftedTwoStateChannelCorrelation_self_sq_le_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X) :
    (phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y) ^ 2
      ≤
    symmetricTwoStateChannelCorrelation (E := E) comparison comparison X X
      * symmetricTwoStateChannelCorrelation (E := E) comparison comparison Y Y := by
  have hPhase :
      phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y
        =
      comparisonStateGeneratorPhase (E := E) comparison X Y := by
    simpa using
      (comparisonStateGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
        (E := E) comparison X Y).symm
  have hSymmX :
      symmetricTwoStateChannelCorrelation (E := E) comparison comparison X X
        =
      comparisonStateGeneratorMetric (E := E) comparison X X := by
    simpa using
      (comparisonStateGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self
        (E := E) comparison X X).symm
  have hSymmY :
      symmetricTwoStateChannelCorrelation (E := E) comparison comparison Y Y
        =
      comparisonStateGeneratorMetric (E := E) comparison Y Y := by
    simpa using
      (comparisonStateGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self
        (E := E) comparison Y Y).symm
  rw [hPhase, hSymmX, hSymmY]
  exact comparisonStateGeneratorPhase_sq_le_of_IsPhaseLinear
    (E := E) comparison X Y hX

/--
Same-state correlation form of the Robertson-Schrödinger area law on the
`K = Jε`-shifted channel surface.
-/
@[rep_depth krein]
theorem symmetricTwoStateChannelCorrelation_sq_add_phaseShifted_sq_le_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X) :
    (symmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y) ^ 2
      +
    (phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y) ^ 2
      ≤
    symmetricTwoStateChannelCorrelation (E := E) comparison comparison X X
      * symmetricTwoStateChannelCorrelation (E := E) comparison comparison Y Y := by
  have hMetric :
      symmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y
        =
      comparisonStateGeneratorMetric (E := E) comparison X Y := by
    simpa using
      (comparisonStateGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self
        (E := E) comparison X Y).symm
  have hPhase :
      phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y
        =
      comparisonStateGeneratorPhase (E := E) comparison X Y := by
    simpa using
      (comparisonStateGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
        (E := E) comparison X Y).symm
  have hDiagX :
      symmetricTwoStateChannelCorrelation (E := E) comparison comparison X X
        =
      comparisonStateGeneratorMetric (E := E) comparison X X := by
    simpa using
      (comparisonStateGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self
        (E := E) comparison X X).symm
  have hDiagY :
      symmetricTwoStateChannelCorrelation (E := E) comparison comparison Y Y
        =
      comparisonStateGeneratorMetric (E := E) comparison Y Y := by
    simpa using
      (comparisonStateGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self
        (E := E) comparison Y Y).symm
  rw [hMetric, hPhase, hDiagX, hDiagY]
  exact comparisonStateGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear
    (E := E) comparison X Y hX

/--
Induced relational-data form of the phase-response uncertainty bound.
-/
@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonGeneratorPhase_sq_le_of_IsPhaseLinear
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X) :
    (comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y) ^ 2
      ≤
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X X
      *
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) Y Y := by
  simpa [RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorMetric_apply,
    RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i] using
    comparisonStateGeneratorPhase_sq_le_of_IsPhaseLinear
      (E := E) comparison X Y hX

/--
Induced relational-data form of the Robertson-Schrödinger area law.
-/
@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X) :
    (comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y) ^ 2
      +
    (comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y) ^ 2
      ≤
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X X
      *
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) Y Y := by
  simpa [RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorMetric_apply,
    RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i] using
    comparisonStateGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear
      (E := E) comparison X Y hX

/--
Induced relational-data form of the inverse lower bound under unit phase
response.
-/
@[rep_depth transport]
theorem toRelationalInformationDatum_inv_comparisonGeneratorMetric_self_le_of_unit_phase_response_of_IsPhaseLinear
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hUnit :
      comparisonGeneratorPhase
          (toRelationalInformationDatum (E := E) P reference comparison) X Y
        = 1)
    (hY : Y comparison ≠ 0) :
    1 /
        comparisonGeneratorMetric
          (toRelationalInformationDatum (E := E) P reference comparison) Y Y
      ≤
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X X := by
  simpa [RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorMetric_apply,
    RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i] using
    inv_comparisonStateGeneratorMetric_self_le_of_unit_phase_response_of_IsPhaseLinear
      (E := E) comparison X Y hX hUnit hY

end Core

end OperatorialUncertainty
