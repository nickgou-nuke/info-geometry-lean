import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialCramerRao

Noncommutative Cramer-Rao layer for the operatorial doubled-carrier theory.

This file stays entirely on the current operatorial theorem spine:

- the primitive comparison-state channel metric,
- its realization as a positive doubled-space inner-product pairing,
- the resulting Cauchy-Schwarz inequality on perturbation channels,
- and the derived inverse lower bound when a channel pair has unit response.

No scalar Fisher metric, diagonal Hessian model, or spacetime coordinate surface
is introduced here. The bound is derived directly from the owned
noncommutative channel-correlation layer.
-/

namespace InfoGeometry.Canonical.OperatorialCramerRao

open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- The diagonal comparison-state channel metric is the squared channel norm. -/
@[rep_depth krein, simp]
theorem comparisonStateGeneratorMetric_self_eq_norm_sq
    (comparison : H₂)
    (X : PerturbationChannel E) :
    comparisonStateGeneratorMetric (E := E) comparison X X
      =
    ‖X comparison‖ ^ 2 := by
  simp [comparisonStateGeneratorMetric_apply]

/-- The diagonal comparison-state channel metric is nonnegative. -/
@[rep_depth krein]
theorem comparisonStateGeneratorMetric_self_nonneg
    (comparison : H₂)
    (X : PerturbationChannel E) :
    0 ≤ comparisonStateGeneratorMetric (E := E) comparison X X := by
  simp [comparisonStateGeneratorMetric_apply]

/-- The comparison-state channel metric satisfies Cauchy-Schwarz. -/
@[rep_depth krein]
theorem comparisonStateGeneratorMetric_sq_le
    (comparison : H₂)
    (X Y : PerturbationChannel E) :
    (comparisonStateGeneratorMetric (E := E) comparison X Y) ^ 2
      ≤
    comparisonStateGeneratorMetric (E := E) comparison X X
      * comparisonStateGeneratorMetric (E := E) comparison Y Y := by
  simpa [comparisonStateGeneratorMetric_apply, pow_two] using
    real_inner_mul_inner_self_le (X comparison) (Y comparison)

/-- A nonzero channel at the comparison state has strictly positive diagonal metric. -/
@[rep_depth krein]
theorem comparisonStateGeneratorMetric_self_pos_of_apply_ne_zero
    (comparison : H₂)
    (X : PerturbationChannel E)
    (hX : X comparison ≠ 0) :
    0 < comparisonStateGeneratorMetric (E := E) comparison X X := by
  simpa [comparisonStateGeneratorMetric_self_eq_norm_sq] using
    sq_pos_of_pos (norm_pos_iff.mpr hX)

/--
Unit response in the comparison-state channel metric forces the product of the
two diagonal channel costs to be at least one.
-/
@[rep_depth krein]
theorem one_le_comparisonStateGeneratorMetric_self_mul_self_of_unit_response
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hUnit : comparisonStateGeneratorMetric (E := E) comparison X Y = 1) :
    1
      ≤
    comparisonStateGeneratorMetric (E := E) comparison X X
      * comparisonStateGeneratorMetric (E := E) comparison Y Y := by
  have hCS := comparisonStateGeneratorMetric_sq_le (E := E) comparison X Y
  simpa [hUnit, pow_two] using hCS

/--
Operatorial Cramer-Rao lower bound on the comparison-state channel metric.

If the channel pair `(X,Y)` has unit response and the reference channel `Y`
acts nontrivially on the comparison state, then the diagonal cost of `X`
dominates the inverse diagonal cost of `Y`.
-/
@[rep_depth krein]
theorem inv_comparisonStateGeneratorMetric_self_le_of_unit_response
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hUnit : comparisonStateGeneratorMetric (E := E) comparison X Y = 1)
    (hY : Y comparison ≠ 0) :
    1 / comparisonStateGeneratorMetric (E := E) comparison Y Y
      ≤
    comparisonStateGeneratorMetric (E := E) comparison X X := by
  have hYYpos :
      0 < comparisonStateGeneratorMetric (E := E) comparison Y Y :=
    comparisonStateGeneratorMetric_self_pos_of_apply_ne_zero (E := E) comparison Y hY
  have hProd :
      1
        ≤
      comparisonStateGeneratorMetric (E := E) comparison X X
        * comparisonStateGeneratorMetric (E := E) comparison Y Y :=
    one_le_comparisonStateGeneratorMetric_self_mul_self_of_unit_response
      (E := E) comparison X Y hUnit
  rw [div_le_iff₀ hYYpos]
  simpa [mul_comm] using hProd

/-- The induced relational datum inherits the same diagonal channel norm formula. -/
@[rep_depth transport, simp]
theorem toRelationalInformationDatum_comparisonGeneratorMetric_self_eq_norm_sq
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X : PerturbationChannel E) :
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X X
      =
    ‖X comparison‖ ^ 2 := by
  simp [RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorMetric_apply]

/--
The induced relational datum satisfies the same noncommutative Cauchy-Schwarz
bound on its comparison-state channel metric.
-/
@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonGeneratorMetric_sq_le
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    (comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y) ^ 2
      ≤
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X X
      *
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) Y Y := by
  simpa [RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorMetric_apply,
    pow_two] using
    real_inner_mul_inner_self_le (X comparison) (Y comparison)

/--
Induced relational-data form of the operatorial Cramer-Rao lower bound.
-/
@[rep_depth transport]
theorem toRelationalInformationDatum_inv_comparisonGeneratorMetric_self_le_of_unit_response
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E)
    (hUnit :
      comparisonGeneratorMetric
          (toRelationalInformationDatum (E := E) P reference comparison) X Y
        = 1)
    (hY : Y comparison ≠ 0) :
    1 /
        comparisonGeneratorMetric
          (toRelationalInformationDatum (E := E) P reference comparison) Y Y
      ≤
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X X := by
  have hYYpos :
      0 <
        comparisonGeneratorMetric
          (toRelationalInformationDatum (E := E) P reference comparison) Y Y := by
    simpa [toRelationalInformationDatum_comparisonGeneratorMetric_self_eq_norm_sq (E := E)
      (P := P) (reference := reference) (comparison := comparison) (X := Y)] using
      sq_pos_of_pos (norm_pos_iff.mpr hY)
  have hProd :
      1
        ≤
      comparisonGeneratorMetric
          (toRelationalInformationDatum (E := E) P reference comparison) X X
        *
      comparisonGeneratorMetric
          (toRelationalInformationDatum (E := E) P reference comparison) Y Y := by
    have hCS :=
      toRelationalInformationDatum_comparisonGeneratorMetric_sq_le
        (E := E) P reference comparison X Y
    simpa [hUnit, pow_two] using hCS
  rw [div_le_iff₀ hYYpos]
  simpa [mul_comm] using hProd

end Core

end InfoGeometry.Canonical.OperatorialCramerRao
