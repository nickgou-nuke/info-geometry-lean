import InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
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

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel
