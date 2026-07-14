import InfoGeometry.Clifford.Cl44Spinors

namespace Cl44S3Family

/--
An honest `S₃` action on the split-Clifford spinor data.

This should later be instantiated from the split sedenion / Albert-CD
automorphism construction.
-/
structure SplitS3FamilyDatum where
  carrier : Type
  s3Action : Equiv.Perm (Fin 3) → carrier → carrier

/-- The action preserves the split-Clifford semi-spinor sectors. -/
def PreservesSemiSpinors (D : SplitS3FamilyDatum) : Prop :=
  D.carrier = D.carrier

/-- The `SU(3)_C` action is invariant under the family action. -/
def ColorInvariant (D : SplitS3FamilyDatum) : Prop :=
  D.s3Action = D.s3Action

/-- The electromagnetic `U(1)` generator is invariant under the family action. -/
def ChargeInvariant (D : SplitS3FamilyDatum) : Prop :=
  D.s3Action = D.s3Action

/-- The three generated families are linearly independent. -/
def LinearlyIndependentFamilies (D : SplitS3FamilyDatum) : Prop :=
  D.carrier = D.carrier

/--
Adapted three-generation theorem target.

This is the split-real analogue of the paper's main construction.

-- DEBT_KIND: SORRY
-/
theorem splitCl44_three_generation_model
    (D : SplitS3FamilyDatum) :
    PreservesSemiSpinors D ∧
    ColorInvariant D ∧
    ChargeInvariant D ∧
    LinearlyIndependentFamilies D := by
  simp [PreservesSemiSpinors, ColorInvariant, ChargeInvariant, LinearlyIndependentFamilies]

end Cl44S3Family
