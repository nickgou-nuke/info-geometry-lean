import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact coverage criterion for the 189 native quotient representatives

This owner isolates the genuine remaining statement behind
`quotientRepresentative_surjective`.

It does not enumerate `SplitOctF2Aut`, does not use `native_decide` on the
noncomputable `flagRepresentative` evaluator, and does not assume the ambient
automorphism-group order.  Instead it proves that surjectivity of the existing
map

`quotientRepresentative : Fin 189 → CarrierQuotient`

is exactly equivalent to the concrete right-coset coverage statement that
every automorphism differs from one of the 189 representatives by an element
of the native unipotent subgroup.
-/

namespace InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeCoverage

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-- Concrete carrier-level coverage of the quotient by the 189 native flag
representatives. -/
def QuotientRepresentativeCover : Prop :=
  ∀ g : SplitOctF2Aut, ∃ i : Fin 189,
    (flagRepresentative i)⁻¹ * g ∈ unipotentSubgroup

/-- Surjectivity of `quotientRepresentative` is exactly the concrete group-level
coverage statement.  This is the non-circular proof frontier: proving either
side proves the other. -/
theorem quotientRepresentative_surjective_iff_group_cover :
    Function.Surjective quotientRepresentative ↔ QuotientRepresentativeCover := by
  constructor
  · intro hsurj g
    obtain ⟨i, hi⟩ := hsurj (QuotientGroup.mk g : CarrierQuotient)
    refine ⟨i, ?_⟩
    change (QuotientGroup.mk (flagRepresentative i) : CarrierQuotient) =
      QuotientGroup.mk g at hi
    rw [QuotientGroup.eq] at hi
    exact hi
  · intro hcover q
    induction q using Quotient.inductionOn' with
    | h g =>
        obtain ⟨i, hi⟩ := hcover g
        refine ⟨i, ?_⟩
        change (QuotientGroup.mk (flagRepresentative i) : CarrierQuotient) =
          QuotientGroup.mk g
        rw [QuotientGroup.eq]
        exact hi

/-- Concrete group-level coverage immediately yields the requested quotient
surjectivity theorem. -/
theorem quotientRepresentative_surjective_of_group_cover
    (hcover : QuotientRepresentativeCover) :
    Function.Surjective quotientRepresentative :=
  quotientRepresentative_surjective_iff_group_cover.mpr hcover

/-- Conversely, a proof of quotient surjectivity gives the exact native
right-coset coverage certificate. -/
theorem group_cover_of_quotientRepresentative_surjective
    (hsurj : Function.Surjective quotientRepresentative) :
    QuotientRepresentativeCover :=
  quotientRepresentative_surjective_iff_group_cover.mp hsurj

/-- Once injectivity and surjectivity are both established, the 189 native
representatives give the canonical finite equivalence with the quotient. -/
noncomputable def quotientRepresentativeEquiv
    (hinj : Function.Injective quotientRepresentative)
    (hsurj : Function.Surjective quotientRepresentative) :
    Fin 189 ≃ CarrierQuotient :=
  Equiv.ofBijective quotientRepresentative ⟨hinj, hsurj⟩

@[simp] theorem quotientRepresentativeEquiv_apply
    (hinj : Function.Injective quotientRepresentative)
    (hsurj : Function.Surjective quotientRepresentative)
    (i : Fin 189) :
    quotientRepresentativeEquiv hinj hsurj i = quotientRepresentative i :=
  rfl

end InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeCoverage
