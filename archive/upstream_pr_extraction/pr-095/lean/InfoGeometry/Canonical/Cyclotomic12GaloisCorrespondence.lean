import Mathlib.FieldTheory.Galois.Basic
import InfoGeometry.Canonical.TwelveFoldCyclotomicNative

/-!
# Fixed fields and the cyclotomic-12 interface

This owner records the native Mathlib part of the proposed cyclotomic-12
layer.  The files `TwelveFoldGaloisCharacterSets` and
`TwelveFoldGaloisPowerAction` already contain the finite exponent actions of
the units `5`, `7`, and `11` modulo `12`.  They do *not* construct a number
field `ℚ(ζ₁₂)` or a semilinear action on the matrix carrier.  Consequently
this file deliberately exposes the Galois correspondence parametrically,
rather than claiming the three concrete fixed-field computations before
their number-field owner exists.

The theorems below are direct uses of Mathlib's finite Galois
correspondence: no wrappers, axioms, or witness propositions are introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cyclotomic12GaloisCorrespondence

open IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-! The native fixed-field and fixing-subgroup maps. -/

def subgroupToFixedField (H : Subgroup Gal(E / F)) : IntermediateField F E :=
  IntermediateField.fixedField H

def fieldToFixingSubgroup (K : IntermediateField F E) : Subgroup Gal(E / F) :=
  K.fixingSubgroup

theorem fixedField_antitone {H K : Subgroup Gal(E / F)} (h : H ≤ K) :
    subgroupToFixedField K ≤ subgroupToFixedField H := by
  intro x hx
  change x ∈ IntermediateField.fixedField K at hx
  change x ∈ IntermediateField.fixedField H
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro f hf
  exact hx f (h hf)

section FiniteGalois

variable [FiniteDimensional F E] [IsGalois F E]

/-! The order-reversing correspondence supplied by Mathlib. -/
noncomputable def correspondence :
    IntermediateField F E ≃o (Subgroup Gal(E / F))ᵒᵈ :=
  IsGalois.intermediateFieldEquivSubgroup

theorem field_fixedField_fixingSubgroup (K : IntermediateField F E) :
    subgroupToFixedField (fieldToFixingSubgroup K) = K := by
  exact IsGalois.fixedField_fixingSubgroup K

omit [IsGalois F E] in
theorem subgroup_fixingSubgroup_fixedField (H : Subgroup Gal(E / F)) :
    fieldToFixingSubgroup (subgroupToFixedField H) = H := by
  exact IntermediateField.fixingSubgroup_fixedField H

theorem correspondence_symm_apply_toDual (H : Subgroup Gal(E / F)) :
    correspondence.symm (OrderDual.toDual H) = subgroupToFixedField H := by
  exact IsGalois.intermediateFieldEquivSubgroup_symm_apply_toDual H

end FiniteGalois

/-! Normal subgroups yield the quotient symmetry of their fixed field. -/
section NormalFixedField

variable [IsGalois F E]

section FiniteNormal

noncomputable def normalQuotientEquiv (H : Subgroup Gal(E / F))
    [FiniteDimensional F E] [Subgroup.Normal H] :
    Gal(E / F) ⧸ H ≃* Gal(subgroupToFixedField H / F) :=
  IsGalois.normalAutEquivQuotient H

end FiniteNormal

theorem fixedField_of_normal_isGalois (H : Subgroup Gal(E / F))
    [Subgroup.Normal H] : IsGalois F (subgroupToFixedField H) := by
  exact IsGalois.of_fixedField_normal_subgroup H

end NormalFixedField

/-! ### The concrete cyclotomic-12 specialization

The arithmetic owner proves that this extension has four automorphisms and
Klein-four exponent.  The definitions below connect that concrete field to
the native fixed-field correspondence above.  No identification of the three
quadratic fields is asserted here; those are separate arithmetic equalities.
-/

abbrev Cyclotomic12Field := CyclotomicField 12 ℚ
abbrev Cyclotomic12Group := Gal(Cyclotomic12Field / ℚ)

/-! Mathlib's native cyclotomic extension instance supplies the finite Galois
    hypothesis for the concrete twelfth cyclotomic field. -/
noncomputable instance cyclotomic12_isGalois : IsGalois ℚ Cyclotomic12Field :=
  IsCyclotomicExtension.isGalois {12} ℚ Cyclotomic12Field

theorem cyclotomic12_native_isGalois : IsGalois ℚ Cyclotomic12Field :=
  inferInstance

/-!
The cyclotomic specialization is intentionally parameterized by the native
Mathlib hypotheses.  The current TwelveFold arithmetic owner does not provide
an `IsGalois ℚ (CyclotomicField 12 ℚ)` instance, so these declarations do not
silently manufacture one.
-/
noncomputable def cyclotomic12Correspondence
    [FiniteDimensional ℚ Cyclotomic12Field]
    [IsGalois ℚ Cyclotomic12Field] :
    IntermediateField ℚ Cyclotomic12Field ≃o
      (Subgroup Cyclotomic12Group)ᵒᵈ :=
  correspondence

noncomputable def cyclotomic12NativeCorrespondence :
    IntermediateField ℚ Cyclotomic12Field ≃o
      (Subgroup Cyclotomic12Group)ᵒᵈ :=
  correspondence

theorem cyclotomic12NativeCorrespondence_symm_apply_toDual
    (H : Subgroup Cyclotomic12Group) :
    cyclotomic12NativeCorrespondence.symm (OrderDual.toDual H) =
      subgroupToFixedField H := by
  exact correspondence_symm_apply_toDual H

theorem cyclotomic12_fixedField_fixingSubgroup
    [FiniteDimensional ℚ Cyclotomic12Field]
    [IsGalois ℚ Cyclotomic12Field]
    (K : IntermediateField ℚ Cyclotomic12Field) :
    subgroupToFixedField (fieldToFixingSubgroup K) = K := by
  exact field_fixedField_fixingSubgroup K

theorem cyclotomic12_fixingSubgroup_fixedField
    [FiniteDimensional ℚ Cyclotomic12Field]
    [IsGalois ℚ Cyclotomic12Field]
    (H : Subgroup Cyclotomic12Group) :
    fieldToFixingSubgroup (subgroupToFixedField H) = H := by
  exact subgroup_fixingSubgroup_fixedField H

theorem cyclotomic12_fixedField_antitone
    {H K : Subgroup Cyclotomic12Group} (h : H ≤ K) :
    subgroupToFixedField K ≤ subgroupToFixedField H := by
  exact fixedField_antitone h

end InfoGeometry.Canonical.Cyclotomic12GaloisCorrespondence
