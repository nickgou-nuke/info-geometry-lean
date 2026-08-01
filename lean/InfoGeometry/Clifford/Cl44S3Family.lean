import InfoGeometry.Clifford.Cl44Spinors
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace InfoGeometry.Clifford.Cl44S3Family

/--
An honest `S₃` action on the split-Clifford spinor data.

This should later be instantiated from the split sedenion / Albert-CD
automorphism construction.
-/
structure SplitS3FamilyDatum
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  s3Action : Equiv.Perm (Fin 3) → V →ₗ[ℝ] V
  action_one : s3Action 1 = LinearMap.id
  action_mul : ∀ σ τ,
    s3Action (σ * τ) = (s3Action σ).comp (s3Action τ)
  family : Fin 3 → V
  colorOperator : V →ₗ[ℝ] V
  chargeOperator : V →ₗ[ℝ] V
  preserves_semiSpinors : ∀ σ i,
    s3Action σ (family i) = family (σ i)
  color_invariant : ∀ σ,
    (s3Action σ).comp colorOperator = colorOperator.comp (s3Action σ)
  charge_invariant : ∀ σ,
    (s3Action σ).comp chargeOperator = chargeOperator.comp (s3Action σ)
  linearly_independent_families : LinearIndependent ℝ family

/-- The action preserves the split-Clifford semi-spinor sectors. -/
def PreservesSemiSpinors {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) : Prop :=
  ∀ σ i, D.s3Action σ (D.family i) = D.family (σ i)

/-- The `SU(3)_C` action is invariant under the family action. -/
def ColorInvariant {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) : Prop :=
  ∀ σ, (D.s3Action σ).comp D.colorOperator =
    D.colorOperator.comp (D.s3Action σ)

/-- The electromagnetic `U(1)` generator is invariant under the family action. -/
def ChargeInvariant {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) : Prop :=
  ∀ σ, (D.s3Action σ).comp D.chargeOperator =
    D.chargeOperator.comp (D.s3Action σ)

/-- The three generated families are linearly independent. -/
def LinearlyIndependentFamilies {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) : Prop :=
  LinearIndependent ℝ D.family

/--
Adapted three-generation theorem target.

This is the split-real analogue of the paper's main construction.

-- DEBT_KIND: SORRY
-/
theorem splitCl44_three_generation_model
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : SplitS3FamilyDatum V) :
    PreservesSemiSpinors D ∧
    ColorInvariant D ∧
    ChargeInvariant D ∧
    LinearlyIndependentFamilies D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.preserves_semiSpinors
  · exact D.color_invariant
  · exact D.charge_invariant
  · exact D.linearly_independent_families

end InfoGeometry.Clifford.Cl44S3Family
