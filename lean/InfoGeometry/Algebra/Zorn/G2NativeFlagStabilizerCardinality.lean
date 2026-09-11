import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagCardinality
import InfoGeometry.Algebra.Zorn.G2NativeFlagIntrinsicEquiv

/-!
# Cardinality bridge for the native flag stabilizer

The transport owner proves `unipotentSubgroup ≤ nativeFlagStabilizer`.
This file records the remaining, honest census interface: ambient order,
flag coverage, and transitivity imply the reverse inclusion by orbit--stabilizer.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerCardinality

open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2NativeFlagIntrinsicEquiv
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_census_sigma
    (h_enum : Fintype.card SplitOctF2Aut = 12096)
    (h_flag_card : Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189)
    (h_trans : Function.Surjective
      (fun g : SplitOctF2Aut => g • baseIntrinsicFlag)) :
    nativeFlagStabilizer = unipotentSubgroup := by
  apply nativeFlagStabilizer_eq_unipotentSubgroup_of_card_eq
  have hstab := nativeFlagStabilizer_card_eq_64_of_flag_transitive_sigma
    h_enum h_flag_card h_trans
  have hu : Fintype.card unipotentSubgroup = 64 := by
    simpa only [Nat.card_eq_fintype_card] using unipotentSubgroup_card
  rw [hstab, hu]

theorem nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_census
    (h_enum : Fintype.card SplitOctF2Aut = 12096)
    (h_flag_card : Fintype.card IntrinsicFlag = 189)
    (h_trans : Function.Surjective
      (fun g : SplitOctF2Aut => g • baseIntrinsicFlag)) :
    nativeFlagStabilizer = unipotentSubgroup := by
  simpa [IntrinsicFlag] using
    nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_census_sigma
      h_enum h_flag_card h_trans

theorem nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_transitive
    (h_enum : Fintype.card SplitOctF2Aut = 12096)
    (h_trans : Function.Surjective
      (fun g : SplitOctF2Aut => g • baseIntrinsicFlag)) :
    nativeFlagStabilizer = unipotentSubgroup :=
  nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_census
    h_enum G2IntrinsicFlagCardinality.intrinsicFlag_card h_trans

theorem nativeFlagStabilizer_eq_unipotentSubgroup_of_ambient_card
    (h_enum : Fintype.card SplitOctF2Aut = 12096) :
    nativeFlagStabilizer = unipotentSubgroup := by
  apply nativeFlagStabilizer_eq_unipotentSubgroup_of_flag_transitive h_enum
  simpa only [smul_eq_mul] using intrinsicFlag_orbit_surjective

noncomputable def quotientIntrinsicFlagEquiv_of_ambient_card
    (h_enum : Fintype.card SplitOctF2Aut = 12096) :
    (SplitOctF2Aut ⧸ unipotentSubgroup) ≃ IntrinsicFlag := by
  apply G2StructuralFlagQuotient.quotientFlagEquivOfStabilizerEq
    baseIntrinsicFlag unipotentSubgroup
  · exact nativeFlagStabilizer_eq_unipotentSubgroup_of_ambient_card h_enum
  · simpa only [smul_eq_mul] using intrinsicFlag_orbit_surjective

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerCardinality
