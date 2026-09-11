import InfoGeometry.Algebra.Zorn.G2TitsRepresentativeInjectivity
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The concrete Weyl representative carrier

`WeylG2` is the finite parameter carrier and `SplitOctF2Aut` is the concrete
automorphism carrier.  This file exposes the missing typed bridge between the
twelve orbit labels and the range of their concrete representatives.  It does
not assert that the normal-form map is a monoid homomorphism.
-/

namespace InfoGeometry.Algebra.Zorn.G2WeylRepresentativeEquiv

open InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
open InfoGeometry.Algebra.Zorn.G2TitsRepresentativeInjectivity

noncomputable def orbitWeylRepresentativeEquiv :
    Fin 12 ≃ Set.range orbitWeylRepresentative :=
  Equiv.ofBijective (fun k =>
      (⟨orbitWeylRepresentative k, ⟨k, rfl⟩⟩ : Set.range orbitWeylRepresentative))
    ⟨by
      intro k l h
      exact orbitWeylRepresentative_injective (Subtype.ext_iff.mp h), by
      intro x
      rcases x.property with ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩⟩

@[simp] theorem orbitWeylRepresentativeEquiv_apply (k : Fin 12) :
    orbitWeylRepresentativeEquiv k = orbitWeylRepresentative k :=
  rfl

theorem orbitWeylRepresentativeEquiv_symm_apply
    (x : Set.range orbitWeylRepresentative) :
    orbitWeylRepresentativeEquiv.symm x = Classical.choose x.property := by
  apply orbitWeylRepresentative_injective
  have hx :
      orbitWeylRepresentative (orbitWeylRepresentativeEquiv.symm x) = x := by
    exact congrArg Subtype.val
      (orbitWeylRepresentativeEquiv.apply_symm_apply x)
  exact hx.trans (Classical.choose_spec x.property).symm

end InfoGeometry.Algebra.Zorn.G2WeylRepresentativeEquiv
