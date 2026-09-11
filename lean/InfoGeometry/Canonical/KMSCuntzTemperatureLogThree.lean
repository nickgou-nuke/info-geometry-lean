import InfoGeometry.Canonical.CuntzGeneratorKMSLogThree
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzKMSCondition
import InfoGeometry.Physics.B3PresentedGroup
import InfoGeometry.Physics.JonesBraidB3

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzKMSCondition
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Physics.JonesBraidB3

/-!
# KMS temperature bridge at `log 3`

This file stays on the actual algebraic Cuntz quotient and the actual braid
presentation already formalized in the repository.

It only packages the generator-level temperature conclusion:
the standard gauge normalization `α_t(Sᵢ) = e^{i t} Sᵢ` forces the critical
inverse temperature `β = log 3` for three generators.

The positive-state completion and analytic-strip KMS extension remain a later
owner file.
-/

/-- Generator-level temperature consequence for the algebraic Cuntz quotient. -/
theorem cuntz3_generator_temperature_log_three
    (φ : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3 →ₗ[ℂ] ℂ) (β : ℝ)
    (hKMS : GeneratorKMSAt φ β) :
    β = Real.log 3 :=
  generatorKMS_beta_eq_log_three hKMS

/-- The normalized generator two-point function at the critical temperature. -/
theorem cuntz3_generator_temperature_two_point
    (φ : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3 →ₗ[ℂ] ℂ)
    (hKMS : GeneratorKMSAt φ (Real.log 3)) (i j : Fin 3) :
    φ (cuntzS 3 i * cuntzSdag 3 j) =
      if i = j then (1 / 3 : ℂ) else 0 :=
  generatorKMS_twoPoint_at_log_three φ hKMS i j

/-- The actual Artin braid relation already formalized in the repository. -/
theorem b3_artin_relation_formalized :
    s0 * s1 * s0 = s1 * s0 * s1 :=
  artin_braid_relation

/-- The presented braid-group relation already formalized in the repository. -/
theorem b3_presented_group_relation_formalized :
    FreeGroup.lift braidMap b3Relation = 1 :=
  b3_relation_holds

end InfoGeometry.Canonical
