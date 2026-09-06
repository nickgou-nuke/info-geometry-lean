import InfoGeometry.Canonical.CuntzGeneratorKMSLogThree
import InfoGeometry.Canonical.G2HolonomyGaugeConnections
import InfoGeometry.Canonical.KMSSubstateKMSCondition
import InfoGeometry.Canonical.SplitG2HodgeDualFourForm
import InfoGeometry.Canonical.SplitG2StructureOnImaginaryOctonions

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Native quantum/KMS bridge over the split `G₂` carrier

This file is an integration owner, not a definition of the homogeneous space
`G₂(2) / SO(4)`.  The latter requires a Lie-group action, an orbit theorem and
an explicit stabilizer calculation, none of which is present in the current
native owners.  The declarations below therefore expose only the existing
split-`G₂` transport data and the existing noncommutative KMS owners.
-/

/-- The seven-dimensional rational carrier used by the split-`G₂` branch. -/
noncomputable abbrev QuantumKMSCarrier := imaginarySplitOctonion

theorem quantumKMSCarrier_finrank :
    Module.finrank ℚ QuantumKMSCarrier = 7 :=
  imaginarySplitOctonion_finrank_eq_seven

/-- Existing split-`G₂` transport preserves the canonical three-form. -/
theorem quantumKMS_transport_preserves_threeForm
    (φ : SplitG2Automorphism)
    (x y z : QuantumKMSCarrier) :
    canonicalSplitG2ThreeFormValue
        (φ.toLinearEquiv x) (φ.toLinearEquiv y) (φ.toLinearEquiv z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact φ.preservesThreeForm x y z

/-- Native finite-dimensional KMS state used by the existing matrix owner. -/
noncomputable def finiteKMSState {n : Type*} [Fintype n] [DecidableEq n]
    (ρ A : Matrix n n ℂ) : ℂ :=
  thermalState ρ A

theorem finiteKMSState_kms {n : Type*} [Fintype n] [DecidableEq n]
    (ρ ρ_inv : Matrix n n ℂ)
    (A B : Matrix n n ℂ)
    (h_inv_left : ρ_inv * ρ = 1)
    (h_inv_right : ρ * ρ_inv = 1) :
    finiteKMSState ρ (A * modularAutomorphism_i ρ ρ_inv B) =
      finiteKMSState ρ (B * A) := by
  exact kms_condition_beta_one ρ ρ_inv A B h_inv_left h_inv_right

/-- The already-defined native generator-level KMS condition at `log 3`. -/
theorem cuntz_three_generator_temperature
    (φ : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3 →ₗ[ℂ] ℂ)
    (β : ℝ)
    (hKMS : GeneratorKMSAt φ β) :
    β = Real.log 3 := by
  exact generatorKMS_beta_eq_log_three hKMS

theorem cuntz_three_generator_two_point
    (φ : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3 →ₗ[ℂ] ℂ)
    (hKMS : GeneratorKMSAt φ (Real.log 3))
    (i j : Fin 3) :
    φ (cuntzS 3 i * cuntzSdag 3 j) =
      if i = j then (1 / 3 : ℂ) else 0 := by
  exact generatorKMS_twoPoint_at_log_three φ hKMS i j

/-!
The following geometric assertions are intentionally not introduced here:

* `G₂(2) / SO(4)` or `G₂(2) / SO₀(2,2)` as a quotient;
* maximal compactness of a stabilizer;
* a Hadamard metric or geodesic flow;
* an entropy/first-law identity.

They need additional Lie-group, orbit, metric and analytic owners.  Keeping
them out of this bridge prevents the former scalar and `True`-carrier
scaffolds from being mistaken for proofs.
-/

end InfoGeometry.Canonical
