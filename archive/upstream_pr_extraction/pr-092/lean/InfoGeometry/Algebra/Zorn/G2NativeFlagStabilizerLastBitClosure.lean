import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel

/-!
# Native flag-stabilizer closure from the final residual readbacks

This owner isolates the exact last two native obligations left by the peeling
pipeline. It does not manufacture either obligation from cardinality,
subgroup generation, or an external certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerLastBitClosure

open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-- Once the residual fixes `basis8 7`, the unconditional `basis8 5`
readback forces the residual to fix `basis8 3`. -/
theorem fullPeel_basis8_three_fixed_of_seven
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    (fullPeel g).1 (basis8 3) = basis8 3 := by
  exact fullPeel_basis8_three_readback_of_generators
    (fullPeel_basis8_five_readback hg) h7

/-- The last unresolved `basis8 2` bit is exactly the `y0` coordinate of the
residual image of `basis8 6`. -/
theorem fullPeel_basis8_two_x1_false_of_six_y0_false
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h6y0 : ((fullPeel g).1 (basis8 6)).y0 = false) :
    ((fullPeel g).1 (basis8 2)).x1 = false := by
  exact (fullPeel_basis8_two_x1_false_iff_basis8_six_y0_false hg).2 h6y0

/-- `basis8 7` plus the final `basis8 6.y0` bit force the complete residual
readback on `basis8 2`. -/
theorem fullPeel_basis8_two_fixed_of_seven_and_six_y0
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ((fullPeel g).1 (basis8 6)).y0 = false) :
    (fullPeel g).1 (basis8 2) = basis8 2 := by
  have h3 : (fullPeel g).1 (basis8 3) = basis8 3 :=
    fullPeel_basis8_three_fixed_of_seven hg h7
  have hx1 : ((fullPeel g).1 (basis8 2)).x1 = false :=
    fullPeel_basis8_two_x1_false_of_six_y0_false hg h6y0
  exact fullPeel_basis8_two_readback_of_reduced_shape hg h3 h7 hx1

/-- The two final residual readbacks force the residual into the native
unipotent subgroup. -/
theorem fullPeel_mem_unipotent_of_seven_and_six_y0
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ((fullPeel g).1 (basis8 6)).y0 = false) :
    fullPeel g ∈ unipotentSubgroup := by
  have h3 : (fullPeel g).1 (basis8 3) = basis8 3 :=
    fullPeel_basis8_three_fixed_of_seven hg h7
  have h4 : (fullPeel g).1 (basis8 4) = basis8 4 :=
    fullPeel_basis8_four_fixed_of_preceding_readback
      (preceding_peel34_basis8_four_readback hg)
  have h5 : (fullPeel g).1 (basis8 5) = basis8 5 :=
    fullPeel_basis8_five_readback hg
  have hx1 : ((fullPeel g).1 (basis8 2)).x1 = false :=
    fullPeel_basis8_two_x1_false_of_six_y0_false hg h6y0
  exact fullPeel_mem_unipotent_of_generators_and_x1 hg h3 h4 h5 h7 hx1

/-- The residual is not merely unipotent: native PC recovery makes its full
peel equal to `1`. -/
theorem fullPeel_eq_one_of_seven_and_six_y0
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ((fullPeel g).1 (basis8 6)).y0 = false) :
    fullPeel g = 1 := by
  apply fullPeel_eq_one_of_mem_directGeneratorClosure
  let H := Subgroup.closure directFlagPCGenerators
  have hpc : G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈ H := by
    change G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈
      Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact ⟨extractAllBits g, rfl⟩
  have hres : fullPeel g ∈ H := by
    change fullPeel g ∈ Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact fullPeel_mem_unipotent_of_seven_and_six_y0 hg h7 h6y0
  rw [← fullPeel_pcWord_factorization g]
  exact H.mul_mem hpc hres

/-- Universal final residual readbacks imply the reverse stabilizer inclusion. -/
theorem nativeFlagStabilizer_le_unipotent_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    nativeFlagStabilizer ≤ unipotentSubgroup := by
  intro g hg
  exact mem_unipotentSubgroup_of_fullPeel_eq_one
    (fullPeel_eq_one_of_seven_and_six_y0 hg (h7 g hg) (h6y0 g hg))

/-- The existing forward inclusion and the final residual readbacks give the
constructive stabilizer equality, with no cardinality argument. -/
theorem nativeFlagStabilizer_eq_unipotent_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    nativeFlagStabilizer = unipotentSubgroup := by
  apply le_antisymm
  · exact nativeFlagStabilizer_le_unipotent_of_final_readbacks h7 h6y0
  · exact unipotentSubgroup_le_nativeFlagStabilizer

/-- The two residual readbacks suffice for the native quotient-to-flag
 equivalence already assembled by the full-peel owner. -/
noncomputable def quotientIntrinsicFlagEquiv_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    (SplitOctF2Aut ⧸ unipotentSubgroup) ≃
      G2IntrinsicFlagAction.IntrinsicFlag := by
  exact G2NativeFlagStabilizerFullPeel.quotientIntrinsicFlagEquiv_of_fullPeel_mem
    (fun g hg => fullPeel_mem_unipotent_of_seven_and_six_y0 hg (h7 g hg) (h6y0 g hg))

/-- Native quotient cardinality from the two final residual readbacks. -/
theorem quotient_card_eq_189_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    Nat.card (SplitOctF2Aut ⧸ unipotentSubgroup) = 189 := by
  let e : (SplitOctF2Aut ⧸ unipotentSubgroup) ≃
      G2IntrinsicFlagAction.IntrinsicFlag :=
    quotientIntrinsicFlagEquiv_of_final_readbacks h7 h6y0
  rw [Nat.card_congr e]
  simpa only [Nat.card_eq_fintype_card] using
    G2IntrinsicFlagCardinality.intrinsicFlag_card

/-- Native ambient group order from the two final residual readbacks. -/
theorem ambient_card_eq_12096_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    Nat.card SplitOctF2Aut = 12096 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
    quotient_card_eq_189_of_final_readbacks h7 h6y0,
    G2TwoPCSubgroupClosure.unipotentSubgroup_card]

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerLastBitClosure
