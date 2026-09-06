import InfoGeometry.Algebra.Zorn.G2OrderedRootProduct
import InfoGeometry.Algebra.Zorn.G2RootPCAlignment
import InfoGeometry.Algebra.Zorn.G2BruhatResidualTopEquiv

namespace InfoGeometry.Algebra.Zorn.G2TopOrderedRootProduct

open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2BruhatResidualEquiv
open InfoGeometry.Algebra.Zorn.G2RootPCAlignment
open InfoGeometry.Algebra.Zorn.G2RootResidualGenerators
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.GroupTheory.G2BruhatInversions

/-- The top residual roots in the same order as the verified six PC coordinates. -/
noncomputable def topRootAt (i : Fin 6) :
  { α : InfoGeometry.Algebra.Zorn.G2Combinatorics.G2PositiveRoot //
      α ∈ bruhatInversionRoots (3, false) } :=
  ⟨rootPCAlignment.symm i, by
    have htop : bruhatInversionRoots (3, false) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [bruhatInversionRoots_card_eq_length]
      decide
    simp [htop]⟩

/-- Transport top residual Boolean coordinates to the verified PC order. -/
noncomputable def topBits
    (e : BruhatResidualExponent (3, false)) : PCWordExp :=
  fun i => e (topRootAt i)

@[simp] theorem topBits_apply
    (e : BruhatResidualExponent (3, false)) (i : Fin 6) :
    topBits e i = e (topRootAt i) := rfl

noncomputable def topOrderedRootProduct
    (e : BruhatResidualExponent (3, false)) : SplitOctF2Aut :=
  pcWord (topBits e)

theorem topOrderedRootProduct_mem_residualSubgroup
    (e : BruhatResidualExponent (3, false)) :
    topOrderedRootProduct e ∈ residualSubgroup (3, false) := by
  rw [residualSubgroup_top_parameter]
  rw [← sylowTwoSubgroup_eq_unipotentSubgroup]
  exact pcWord_mem_sylow (topBits e)

theorem topOrderedRootProduct_injective :
    Function.Injective topOrderedRootProduct := by
  intro e₁ e₂ h
  apply funext
  intro α
  have hpc : topBits e₁ = topBits e₂ := by
    apply pcWord_injective
    simpa [topOrderedRootProduct] using h
  have hα := congrFun hpc (rootPCAlignment α.1)
  rw [topBits, topBits] at hα
  have hs : topRootAt (rootPCAlignment α.1) = α := by
    apply Subtype.ext
    change rootPCAlignment.symm (rootPCAlignment α.1) = α.1
    exact rootPCAlignment.symm_apply_apply α.1
  rw [hs] at hα
  exact hα

noncomputable def topOrderedRootProductEquiv :
    BruhatResidualExponent (3, false) ≃ residualSubgroup (3, false) := by
  letI : Fintype (residualSubgroup (3, false)) := Fintype.ofFinite _
  let f : BruhatResidualExponent (3, false) → residualSubgroup (3, false) :=
    fun e => ⟨topOrderedRootProduct e,
      topOrderedRootProduct_mem_residualSubgroup e⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  constructor
  · intro e₁ e₂ h
    apply topOrderedRootProduct_injective
    exact congrArg Subtype.val h
  · rw [bruhatResidualExponent_card]
    have hlen : dihedralLength (3, false) = 6 := by decide
    rw [hlen]
    have hres : Fintype.card (residualSubgroup (3, false)) = 64 := by
      simpa only [Nat.card_eq_fintype_card] using residualSubgroup_top_parameter_card
    norm_num [hres]

theorem topOrderedRootProduct_surjective :
    Function.Surjective (fun e =>
      (⟨topOrderedRootProduct e,
        topOrderedRootProduct_mem_residualSubgroup e⟩ :
        residualSubgroup (3, false))) := by
  exact (topOrderedRootProductEquiv).surjective

theorem topOrderedRootProductEquiv_card :
    Nat.card (BruhatResidualExponent (3, false)) =
      Nat.card (residualSubgroup (3, false)) :=
  Nat.card_congr topOrderedRootProductEquiv

theorem topOrderedRootProduct_residual_card :
    Nat.card (residualSubgroup (3, false)) = 64 :=
  residualSubgroup_top_parameter_card

end InfoGeometry.Algebra.Zorn.G2TopOrderedRootProduct
