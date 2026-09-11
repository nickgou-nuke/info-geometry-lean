import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

private theorem eqRec_intrinsicLine_val
    {p q : OctImIsotropicPoint} (h : p = q)
    (L : IntrinsicLine p) :
    (h ▸ L).val = L.val := by
  cases h
  rfl

noncomputable def nativeFlagStabilizer : Subgroup SplitOctF2Aut :=
  MulAction.stabilizer SplitOctF2Aut baseIntrinsicFlag

theorem pcWord_mem_nativeFlagStabilizer (e : Fin 6 → Bool) :
    G2TwoSylowSubgroup.pcWord e ∈ nativeFlagStabilizer := by
  change G2TwoSylowSubgroup.pcWord e • baseIntrinsicFlag = baseIntrinsicFlag
  have hp : octImPointPerm (G2TwoSylowSubgroup.pcWord e)
      nativeBaseIsotropicPoint = nativeBaseIsotropicPoint :=
    pcWord_point_fix e
  apply Sigma.ext_iff.mpr
  constructor
  · exact hp
  · have htransport :=
      (eqRec_heq hp
        (intrinsicLineMap (G2TwoSylowSubgroup.pcWord e)
          baseIntrinsicFlag.2)).symm
    exact htransport.trans (by
      apply heq_of_eq
      apply Subtype.ext
      rw [eqRec_intrinsicLine_val hp]
      simp only [intrinsicLineMap_val]
      change zornZeroTripleMap (G2TwoSylowSubgroup.pcWord e)
          baseIntrinsicLine.1 = baseIntrinsicLine.1
      ext v
      rw [mem_zornZeroTripleMap_iff]
      constructor <;> intro hv
      · have hv' : ((octImPointPerm
            (G2TwoSylowSubgroup.pcWord e)).symm v).1 ∈
            nativeBaseLineWitness :=
          (mem_baseIntrinsicLine_iff _).mp hv
        have hmap := pcWord_fixes_nativeBaseLineWitness e
        have himage : v.1 ∈ nativeBaseLineWitness.image
            (octImAction (G2TwoSylowPCAutomorphisms.pcWord e)) := by
          refine Finset.mem_image.mpr
            ⟨((octImPointPerm
                (G2TwoSylowPCAutomorphisms.pcWord e)).symm v).1,
              hv', ?_⟩
          change (octImPointPerm
            (G2TwoSylowPCAutomorphisms.pcWord e)
            ((octImPointPerm
              (G2TwoSylowPCAutomorphisms.pcWord e)).symm v)).1 = v.1
          exact congrArg Subtype.val
            ((octImPointPerm
              (G2TwoSylowPCAutomorphisms.pcWord e)).apply_symm_apply v)
        rw [hmap] at himage
        exact (mem_baseIntrinsicLine_iff v).mpr himage
      · have hv' : v.1 ∈ nativeBaseLineWitness :=
          (mem_baseIntrinsicLine_iff v).mp hv
        have hmap := pcWord_fixes_nativeBaseLineWitness e
        have himage : v.1 ∈ nativeBaseLineWitness.image
            (octImAction (G2TwoSylowPCAutomorphisms.pcWord e)) := by
          rw [hmap]
          exact hv'
        rcases Finset.mem_image.mp himage with ⟨w, hw, hwv⟩
        let hwpt : OctImIsotropicPoint :=
          ⟨w, (nativeBaseLineWitness_points_valid w hw).1,
            (nativeBaseLineWitness_points_valid w hw).2⟩
        have hpt : octImPointPerm
            (G2TwoSylowPCAutomorphisms.pcWord e) hwpt = v := by
          apply Subtype.ext
          rw [octImPointPerm_apply]
          dsimp [pointToOctIm, octImToPoint, hwpt, octImAction]
          exact hwv
        have hpre :
            (octImPointPerm
              (G2TwoSylowPCAutomorphisms.pcWord e)).symm v = hwpt := by
          rw [← hpt]
          simp
        have : (octImPointPerm
            (G2TwoSylowPCAutomorphisms.pcWord e)).symm v ∈
            baseIntrinsicLine.1 := by
          rw [hpre]
          have hwpoint : hwpt.1 ∈ nativeBaseLineWitness := by
            have hval : hwpt.1 = w := rfl
            rw [hval]
            exact hw
          exact (mem_baseIntrinsicLine_iff _).mpr hwpoint
        simpa only [G2TwoSylowSubgroup.pcWord] using this)

theorem unipotentSubgroup_le_nativeFlagStabilizer :
    unipotentSubgroup ≤ nativeFlagStabilizer := by
  intro u hu
  change u ∈ Set.range G2TwoSylowSubgroup.pcWord at hu
  obtain ⟨e, rfl⟩ := hu
  exact pcWord_mem_nativeFlagStabilizer e

/-- Left multiplication by a unipotent element preserves the flag
    stabilizer.  This is the subgroup-theoretic transport used when applying
    the successive peeling operators to a stabilizer element. -/
theorem unipotent_mul_mem_nativeFlagStabilizer
    {u g : SplitOctF2Aut}
    (hu : u ∈ unipotentSubgroup)
    (hg : g ∈ nativeFlagStabilizer) :
    u * g ∈ nativeFlagStabilizer := by
  exact nativeFlagStabilizer.mul_mem
    (unipotentSubgroup_le_nativeFlagStabilizer hu) hg

/-- The same transport for two successive unipotent factors. -/
theorem unipotent_mul_mul_mem_nativeFlagStabilizer
    {u v g : SplitOctF2Aut}
    (hu : u ∈ unipotentSubgroup)
    (hv : v ∈ unipotentSubgroup)
    (hg : g ∈ nativeFlagStabilizer) :
    u * v * g ∈ nativeFlagStabilizer := by
  exact unipotent_mul_mem_nativeFlagStabilizer
    (unipotentSubgroup.mul_mem hu hv) hg

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
