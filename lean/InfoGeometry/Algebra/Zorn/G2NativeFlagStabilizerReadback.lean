import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
import InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv
import InfoGeometry.Algebra.Zorn.G2StructuralFlagQuotient

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback

open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2PCWordSubgroupEquiv
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable instance nativeFlagStabilizer_fintype :
    Fintype nativeFlagStabilizer := Fintype.ofFinite _

noncomputable instance unipotentSubgroup_fintype :
    Fintype G2TwoPCSubgroupClosure.unipotentSubgroup :=
  Fintype.ofEquiv G2TwoSylowSubgroup.PCWordExp
    G2PCWordSubgroupEquiv.pcWordEquivUnipotent

theorem nativeFlagStabilizer_smul_baseIntrinsicFlag
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    g • baseIntrinsicFlag = baseIntrinsicFlag :=
  hg

theorem nativeFlagStabilizer_fixes_base_point
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    octImPointPerm g G2NativeOnePointStabilizer.nativeBaseIsotropicPoint =
      G2NativeOnePointStabilizer.nativeBaseIsotropicPoint := by
  have hflag := nativeFlagStabilizer_smul_baseIntrinsicFlag hg
  simpa [smul_intrinsicFlag, intrinsicFlagMap, baseIntrinsicFlag] using
    congrArg Sigma.fst hflag

theorem nativeFlagStabilizer_le_nativePointStabilizer :
    nativeFlagStabilizer ≤ nativePointStabilizer := by
  intro g hg
  change g • nativeBasePointData = nativeBasePointData
  have hp := nativeFlagStabilizer_fixes_base_point hg
  rw [octImPointPerm_apply] at hp
  change pointToOctIm (g • nativeBasePointData) = nativeBaseIsotropicPoint at hp
  have hp' := congrArg octImToPoint hp
  rw [pointToOctIm_left_inverse] at hp'
  simpa [nativeBasePointData] using hp'

theorem nativeFlagStabilizer_eq_unipotentSubgroup_of_card_eq
    (hcard : Fintype.card nativeFlagStabilizer =
      Fintype.card G2TwoPCSubgroupClosure.unipotentSubgroup) :
    nativeFlagStabilizer = G2TwoPCSubgroupClosure.unipotentSubgroup := by
  apply le_antisymm
  · have hle : G2TwoPCSubgroupClosure.unipotentSubgroup ≤
        nativeFlagStabilizer :=
      G2NativeFlagStabilizerTransport.unipotentSubgroup_le_nativeFlagStabilizer
    let f : G2TwoPCSubgroupClosure.unipotentSubgroup →
      nativeFlagStabilizer := fun u =>
      ⟨u.1, hle u.2⟩
    have hf_inj : Function.Injective f := by
      intro u v huv
      apply Subtype.ext
      exact congrArg (fun z : nativeFlagStabilizer =>
        (z : SplitOctF2Aut)) huv
    have hf_surj : Function.Surjective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr
        ⟨hf_inj, hcard.symm⟩ |>.2
    intro g hg
    obtain ⟨u, hu⟩ := hf_surj ⟨g, hg⟩
    have hval : (u : SplitOctF2Aut) = g :=
      congrArg (fun z : nativeFlagStabilizer =>
        (z : SplitOctF2Aut)) hu
    have hu_mem : (u : SplitOctF2Aut) ∈
        G2TwoPCSubgroupClosure.unipotentSubgroup := u.property
    rw [hval] at hu_mem
    exact hu_mem
  · exact unipotentSubgroup_le_nativeFlagStabilizer

set_option maxRecDepth 100000 in
theorem nativeFlagStabilizer_card_eq_64_of_flag_transitive_sigma
    (h_enum : Fintype.card SplitOctF2Aut = 12096)
    (h_flag_card : Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189)
    (h_trans : Function.Surjective
      (fun g : SplitOctF2Aut => g • baseIntrinsicFlag)) :
    Fintype.card nativeFlagStabilizer = 64 := by
  letI : Fintype (MulAction.orbit SplitOctF2Aut baseIntrinsicFlag) :=
    Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer SplitOctF2Aut baseIntrinsicFlag) := by
    change Fintype nativeFlagStabilizer
    exact nativeFlagStabilizer_fintype
  have horbit : Fintype.card
      (MulAction.orbit SplitOctF2Aut baseIntrinsicFlag) = 189 := by
    let e := InfoGeometry.Algebra.Zorn.G2StructuralFlagQuotient.orbitToTarget
      baseIntrinsicFlag h_trans
    have htarget : Fintype.card IntrinsicFlag = 189 := by
      simpa [IntrinsicFlag] using h_flag_card
    rw [← htarget]
    exact Fintype.card_congr e
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    SplitOctF2Aut baseIntrinsicFlag
  have hcardStab : Fintype.card
      (MulAction.stabilizer SplitOctF2Aut baseIntrinsicFlag) = 64 := by
    rw [horbit, h_enum] at h
    omega
  simpa [nativeFlagStabilizer] using hcardStab

set_option maxRecDepth 100000 in
theorem nativeFlagStabilizer_card_eq_64_of_flag_transitive
    (h_enum : Fintype.card SplitOctF2Aut = 12096)
    (h_flag_card : Fintype.card IntrinsicFlag = 189)
    (h_trans : Function.Surjective
      (fun g : SplitOctF2Aut => g • baseIntrinsicFlag)) :
    Fintype.card nativeFlagStabilizer = 64 := by
  simpa [IntrinsicFlag] using
    nativeFlagStabilizer_card_eq_64_of_flag_transitive_sigma h_enum h_flag_card h_trans

theorem nativeFlagStabilizer_preserves_base_line
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    HEq (intrinsicLineMap g baseIntrinsicLine) baseIntrinsicLine := by
  have hflag := nativeFlagStabilizer_smul_baseIntrinsicFlag hg
  exact (Sigma.ext_iff.mp hflag).2

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
