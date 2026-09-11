import InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerCardinality
import InfoGeometry.Algebra.Zorn.G2NativeFlagIntrinsicEquiv
import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagCardinality

/-!
# Full-peel closure of the native flag stabilizer

This owner only assembles the already proved forward and reverse inclusion
interfaces.  The full-peel certificate remains an explicit hypothesis.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel

open InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
open InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem nativeFlagStabilizer_eq_unipotent_of_fullPeel_eq_one
    (hpeel : ∀ g : SplitOctF2Aut,
      g ∈ nativeFlagStabilizer → fullPeel g = 1) :
    nativeFlagStabilizer = unipotentSubgroup := by
  apply le_antisymm
  · exact nativeFlagStabilizer_le_unipotent_of_fullPeel_eq_one hpeel
  · exact unipotentSubgroup_le_nativeFlagStabilizer

theorem nativeFlagStabilizer_eq_unipotent_of_fullPeel_mem
    (hpeel : ∀ g : SplitOctF2Aut,
      g ∈ nativeFlagStabilizer → fullPeel g ∈ unipotentSubgroup) :
    nativeFlagStabilizer = unipotentSubgroup := by
  apply le_antisymm
  · exact nativeFlagStabilizer_le_unipotent_of_fullPeel_mem hpeel
  · exact unipotentSubgroup_le_nativeFlagStabilizer

/-! The ambient-order route supplies the universal readback under its
explicit census premise.  This remains conditional and does not promote an
external or structural order claim to an unconditional native theorem. -/
theorem fullPeel_basis_readback_of_ambient_card
    (h_enum : Fintype.card SplitOctF2Aut = 12096)
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) (j : Fin 8) :
    (fullPeel g).1 (basis8 j) = basis8 j := by
  have hstab :=
    G2NativeFlagStabilizerCardinality.nativeFlagStabilizer_eq_unipotentSubgroup_of_ambient_card
      h_enum
  have hU : g ∈ unipotentSubgroup := by
    rw [← hstab]
    exact hg
  exact fullPeel_basis8_readback_of_mem_directGeneratorClosure
    (by
      rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
      exact hU) j

/-! The quotient bridge uses the verified full-peel readback and intrinsic
orbit coverage; it does not use an ambient cardinality hypothesis. -/
noncomputable def quotientIntrinsicFlagEquiv_of_fullPeel_mem
    (hpeel : ∀ g : SplitOctF2Aut,
      g ∈ nativeFlagStabilizer → fullPeel g ∈ unipotentSubgroup) :
    (SplitOctF2Aut ⧸ unipotentSubgroup) ≃ IntrinsicFlag := by
  apply G2StructuralFlagQuotient.quotientFlagEquivOfStabilizerEq
    baseIntrinsicFlag unipotentSubgroup
  · exact nativeFlagStabilizer_eq_unipotent_of_fullPeel_mem hpeel
  · simpa only [smul_eq_mul] using
      InfoGeometry.Algebra.Zorn.G2NativeFlagIntrinsicEquiv.intrinsicFlag_orbit_surjective

/-! The basis-readback contract is the direct input expected by the native
    quotient bridge.  This wrapper keeps the missing universal readback
    explicit while eliminating a repeated conversion through membership of
    `unipotentSubgroup`. -/
noncomputable def quotientIntrinsicFlagEquiv_of_fullPeel_basis_readback
    (hreadback : ∀ g : SplitOctF2Aut,
      g ∈ nativeFlagStabilizer →
      ∀ j : Fin 8, (fullPeel g).1 (basis8 j) = basis8 j) :
    (SplitOctF2Aut ⧸ unipotentSubgroup) ≃ IntrinsicFlag :=
  quotientIntrinsicFlagEquiv_of_fullPeel_mem (fun g hg =>
    (fullPeel_mem_unipotent_of_basis_readback (hreadback g hg)))

theorem quotient_card_eq_189_of_fullPeel_basis_readback
    (hreadback : ∀ g : SplitOctF2Aut,
      g ∈ nativeFlagStabilizer →
      ∀ j : Fin 8, (fullPeel g).1 (basis8 j) = basis8 j) :
    Nat.card (SplitOctF2Aut ⧸ unipotentSubgroup) = 189 := by
  let e := quotientIntrinsicFlagEquiv_of_fullPeel_basis_readback hreadback
  rw [Nat.card_congr e]
  simpa only [Nat.card_eq_fintype_card] using
    G2IntrinsicFlagCardinality.intrinsicFlag_card

theorem ambient_card_eq_12096_of_fullPeel_basis_readback
    (hreadback : ∀ g : SplitOctF2Aut,
      g ∈ nativeFlagStabilizer →
      ∀ j : Fin 8, (fullPeel g).1 (basis8 j) = basis8 j) :
    Nat.card SplitOctF2Aut = 12096 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
    quotient_card_eq_189_of_fullPeel_basis_readback hreadback,
    G2TwoPCSubgroupClosure.unipotentSubgroup_card]

theorem fullPeel_basis8_six_y0_false_of_stabilizer
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 6)).y0 = false := by
  rw [← fullPeel_basis8_two_x1_eq_basis8_six_y0 hg]
  exact fullPeel_basis8_two_x1_false_of_stabilizer hg

theorem basis8_seven_a_false_of_left_product
    {X : SplitOctF2}
    (htrace : X.a = X.b)
    (h4X : (mul (basis8 4) X).x2 = false) :
    X.a = false := by
  have hb : X.b = false := by
    have hcoords := congrArg SplitOctF2.x2 (mul_basis8_four_apply_coordinates X)
    rw [h4X] at hcoords
    exact hcoords.symm
  rw [htrace, hb]

theorem basis8_seven_eq_of_coordinate_relations
    {X : SplitOctF2}
    (hx0 : X.x0 = false)
    (hx1 : X.x1 = false)
    (hy1 : X.y1 = false)
    (hy2 : X.y2 = true)
    (htrace : X.a = X.b)
    (h4X : (mul (basis8 4) X).x2 = false)
    (h2X : (mul (basis8 2) X).a = false)
    (hx2_rel : X.x2 = Bool.xor X.a (X.x1 && X.y1)) :
    X = basis8 7 := by
  have ha : X.a = false := basis8_seven_a_false_of_left_product htrace h4X
  have hx2 : X.x2 = false := by
    rw [hx2_rel, ha, hx1, hy1]
    rfl
  have hy0 : X.y0 = false := by
    rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
    simpa [mul, dot3, cross0, cross1, cross2, basis8, ePlus, eMinus,
      up0, up1, up2, down0, down1, down2, add2, mul2] using h2X
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  simp_all [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel
