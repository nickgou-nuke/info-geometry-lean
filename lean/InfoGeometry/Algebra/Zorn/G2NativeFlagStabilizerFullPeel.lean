import InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagIntrinsicEquiv

/-!
# Full-peel closure of the native flag stabilizer

This owner only assembles the already proved forward and reverse inclusion
interfaces.  The full-peel certificate remains an explicit hypothesis.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel

open InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
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

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel
