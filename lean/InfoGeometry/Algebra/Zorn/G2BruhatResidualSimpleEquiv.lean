import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact
import InfoGeometry.Algebra.Zorn.G2ReducedWords
import InfoGeometry.GroupTheory.G2BruhatInversions

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleEquiv

open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2ResidualSimpleExact
open InfoGeometry.GroupTheory.G2BruhatInversions
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords
open InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleCase
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def canonicalResidualImage : Set (residualSubgroup (2, true)) :=
  Set.range (fun e : CanonicalResidualExponent (weylElementOfNF (2, true)) =>
    (⟨canonicalResidualPCWord (weylElementOfNF (2, true)) e,
      canonicalResidualPCWord_simple_mem_residualSubgroup e⟩ :
        residualSubgroup (2, true)))

noncomputable def canonicalResidualGeneratedSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure (Set.range (fun e :
    CanonicalResidualExponent (weylElementOfNF (2, true)) =>
      (canonicalResidualPCWord (weylElementOfNF (2, true)) e)))

theorem canonicalResidualGeneratedSubgroup_le_residualSubgroup :
    canonicalResidualGeneratedSubgroup ≤ residualSubgroup (2, true) := by
  rw [canonicalResidualGeneratedSubgroup, Subgroup.closure_le]
  rintro x ⟨e, rfl⟩
  exact canonicalResidualPCWord_simple_mem_residualSubgroup e

noncomputable def canonicalResidualImageEquiv :
    CanonicalResidualExponent (weylElementOfNF (2, true)) ≃
      {x : residualSubgroup (2, true) // x ∈ canonicalResidualImage} := by
  let f : CanonicalResidualExponent (weylElementOfNF (2, true)) →
      {x : residualSubgroup (2, true) // x ∈ canonicalResidualImage} := fun e =>
    ⟨⟨canonicalResidualPCWord (weylElementOfNF (2, true)) e,
      canonicalResidualPCWord_simple_mem_residualSubgroup e⟩,
      ⟨e, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro e₁ e₂ h
    apply canonicalResidualPCWord_injective (weylElementOfNF (2, true))
    exact congrArg (fun x : {y : residualSubgroup (2, true) //
      y ∈ canonicalResidualImage} => (x.1 : SplitOctF2Aut)) h
  · intro x
    rcases x.2 with ⟨e, he⟩
    refine ⟨e, Subtype.ext ?_⟩
    exact he

theorem canonicalResidualImage_card :
    Nat.card {x : residualSubgroup (2, true) // x ∈ canonicalResidualImage} = 8 := by
  rw [← Nat.card_congr canonicalResidualImageEquiv]
  rw [Nat.card_eq_fintype_card, canonicalResidualExponent_card]
  have hlen : weylLength (weylElementOfNF (2, true)) = 3 := by decide
  rw [hlen]
  norm_num

theorem canonicalResidualImage_ne_univ :
    canonicalResidualImage ≠ Set.univ := by
  intro h
  letI : Fintype (residualSubgroup (2, true)) := Fintype.ofFinite _
  let e : {x : residualSubgroup (2, true) // x ∈ canonicalResidualImage} ≃
      residualSubgroup (2, true) :=
    { toFun := fun x => x.1
      invFun := fun x => ⟨x, by simp [h]⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hc := Nat.card_congr e
  rw [canonicalResidualImage_card] at hc
  have hsub : Nat.card (residualSubgroup (2, true)) = 32 :=
    residualSubgroup_simple_card_eq_32
  rw [hsub] at hc
  norm_num at hc

theorem no_residualExponent_equiv_simple :
    ¬ Nonempty (BruhatResidualExponent (2, true) ≃ residualSubgroup (2, true)) := by
  letI : Fintype (residualSubgroup (2, true)) := Fintype.ofFinite _
  rintro ⟨e⟩
  have hcard := Fintype.card_congr e
  rw [bruhatResidualExponent_card] at hcard
  have hlen : dihedralLength (2, true) = 3 := by decide
  rw [hlen] at hcard
  have hres : Fintype.card (residualSubgroup (2, true)) = 32 := by
    simpa only [Nat.card_eq_fintype_card] using residualSubgroup_simple_card_eq_32
  rw [hres] at hcard
  norm_num at hcard

end InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleEquiv
