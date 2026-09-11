import InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixCoordinateBridge

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber

private theorem eqRec_intrinsicLine_val
    {p q : OctImIsotropicPoint} (h : p = q)
    (L : IntrinsicLine p) :
    (h ▸ L).val = L.val := by
  cases h
  rfl

theorem autMatrix_action_octImToImaginary
    (g : SplitOctF2Aut)
    (v : G2ParabolicLineFiber.OctImF2) :
    matrixAction (autMatrix g⁻¹) (octImToImaginary v).1 =
      (g • octImToImaginary v).1 := by
  rw [autMatrix_action]
  change (g⁻¹).1 (octImToImaginary v).1 =
    (g⁻¹).1 (octImToImaginary v).1
  rfl

theorem autMatrix_inv_action_fixed_of_octImAction_fixed
    (g : SplitOctF2Aut)
    (v : G2ParabolicLineFiber.OctImF2)
    (hv : octImAction g v = v) :
    matrixAction (autMatrix g⁻¹) (octImToImaginary v).1 =
      (octImToImaginary v).1 := by
  have himag : g • octImToImaginary v = octImToImaginary v := by
    apply imaginaryOctImEquiv.injective
    change imaginaryToOctIm (g • octImToImaginary v) =
      imaginaryToOctIm (octImToImaginary v)
    exact hv.trans (imaginaryOctImEquiv.right_inv v).symm
  rw [autMatrix_action_octImToImaginary, himag]

theorem nativeFlagStabilizer_matrix_fixed_nativeBasePoint
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    matrixAction (autMatrix g⁻¹)
        (octImToImaginary nativeBaseIsotropicPoint.1).1 =
      (octImToImaginary nativeBaseIsotropicPoint.1).1 := by
  apply autMatrix_inv_action_fixed_of_octImAction_fixed
  have hp := nativeFlagStabilizer_fixes_base_point hg
  have hp' := congrArg Subtype.val hp
  simpa [octImPointPerm_apply, octImAction,
    nativeBaseIsotropicPoint] using hp'

theorem nativeFlagStabilizer_matrix_fixed_nativeBasePoint_vec
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (autMatrix g⁻¹).mulVec
        (carrierToVec (octImToImaginary nativeBaseIsotropicPoint.1).1) =
      carrierToVec (octImToImaginary nativeBaseIsotropicPoint.1).1 := by
  have h := congrArg carrierToVec
    (nativeFlagStabilizer_matrix_fixed_nativeBasePoint hg)
  simpa [matrixAction, carrierToVec_vecToCarrier] using h

theorem nativeFlagStabilizer_matrix_fixed_nativeBasePoint_entry
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) (i : Fin 8) :
    ((autMatrix g⁻¹).mulVec
        (carrierToVec (octImToImaginary nativeBaseIsotropicPoint.1).1)) i =
      (carrierToVec
        (octImToImaginary nativeBaseIsotropicPoint.1).1) i := by
  rw [nativeFlagStabilizer_matrix_fixed_nativeBasePoint_vec hg]

theorem nativeFlagStabilizer_baseLine_map
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    zornZeroTripleMap g baseIntrinsicLine.1 = baseIntrinsicLine.1 := by
  have hp := nativeFlagStabilizer_fixes_base_point hg
  have hflag := nativeFlagStabilizer_smul_baseIntrinsicFlag hg
  have hline := (Sigma.ext_iff.mp hflag).2
  have htransport :=
    (eqRec_heq hp
      (intrinsicLineMap g baseIntrinsicFlag.2)).symm
  have hline' :
      HEq (hp ▸ (intrinsicLineMap g baseIntrinsicFlag.2))
        baseIntrinsicLine := by
    exact htransport.symm.trans hline
  have heqLine : hp ▸ (intrinsicLineMap g baseIntrinsicFlag.2) =
      baseIntrinsicLine := eq_of_heq hline'
  have hval := congrArg Subtype.val heqLine
  rw [eqRec_intrinsicLine_val hp] at hval
  simpa [intrinsicLineMap_val, baseIntrinsicFlag] using hval

theorem nativeFlagStabilizer_baseLine_mem_iff
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (v : OctImIsotropicPoint) :
    v ∈ baseIntrinsicLine.1 ↔
      (octImPointPerm g).symm v ∈ baseIntrinsicLine.1 := by
  have hline := nativeFlagStabilizer_baseLine_map hg
  constructor
  · intro hv
    have hv' : v ∈ zornZeroTripleMap g baseIntrinsicLine.1 := by
      rw [hline]
      exact hv
    exact (mem_zornZeroTripleMap_iff g baseIntrinsicLine.1 v).mp hv'
  · intro hv
    have hv' : v ∈ zornZeroTripleMap g baseIntrinsicLine.1 :=
      (mem_zornZeroTripleMap_iff g baseIntrinsicLine.1 v).mpr hv
    rw [hline] at hv'
    exact hv'

theorem nativeFlagStabilizer_nativeBaseLine_map
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    nativeBaseLineWitness.image (octImAction g) = nativeBaseLineWitness := by
  have hline := nativeFlagStabilizer_baseLine_map hg
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨u, hu, huv⟩
    let uPoint : OctImIsotropicPoint :=
      ⟨u, (nativeBaseLineWitness_points_valid u hu).1,
        (nativeBaseLineWitness_points_valid u hu).2⟩
    have huPoint : uPoint ∈ baseIntrinsicLine.1 :=
      (mem_baseIntrinsicLine_iff uPoint).mpr hu
    have hvPoint : octImPointPerm g uPoint ∈ baseIntrinsicLine.1 := by
      have hmem : octImPointPerm g uPoint ∈
          zornZeroTripleMap g baseIntrinsicLine.1 :=
        by
          simpa [zornZeroTripleMap] using
            (Finset.mem_image.mpr ⟨uPoint, huPoint, rfl⟩ :
              octImPointPerm g uPoint ∈
                Finset.image (octImPointPerm g).toEmbedding
                  baseIntrinsicLine.1)
      rw [hline] at hmem
      exact hmem
    have hvPoint' := (mem_baseIntrinsicLine_iff _).mp hvPoint
    have hmem : octImAction g u ∈ nativeBaseLineWitness := by
      simpa [octImPointPerm_apply, octImAction] using hvPoint'
    simpa [← huv] using hmem
  · intro hv
    let vPoint : OctImIsotropicPoint :=
      ⟨v, (nativeBaseLineWitness_points_valid v hv).1,
        (nativeBaseLineWitness_points_valid v hv).2⟩
    have hvPoint : vPoint ∈ baseIntrinsicLine.1 :=
      (mem_baseIntrinsicLine_iff vPoint).mpr hv
    have hpre : (octImPointPerm g).symm vPoint ∈ baseIntrinsicLine.1 :=
      (nativeFlagStabilizer_baseLine_mem_iff hg vPoint).mp hvPoint
    have hpre' := (mem_baseIntrinsicLine_iff _).mp hpre
    have hmem : (octImAction g⁻¹ v) ∈ nativeBaseLineWitness := by
      simpa [vPoint, octImPointPerm_apply, octImAction] using hpre'
    refine Finset.mem_image.mpr ⟨octImAction g⁻¹ v, hmem, ?_⟩
    simp [← octImAction_mul, mul_inv_cancel, octImAction_one]

theorem nativeFlagStabilizer_maps_baseLineVector
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    octImAction g baseLineVector ∈ nativeBaseLineWitness := by
  have hline := nativeFlagStabilizer_nativeBaseLine_map hg
  have hmem : baseLineVector ∈ nativeBaseLineWitness := by
    simp [nativeBaseLineWitness, lineSet, nativeLineSetAt]
  rw [← hline]
  exact Finset.mem_image.mpr ⟨baseLineVector, hmem, rfl⟩

theorem nativeFlagStabilizer_baseLineVector_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    octImAction g baseLineVector = baseLineVector ∨
      octImAction g baseLineVector = nativeBasePoint + baseLineVector := by
  have hmem := nativeFlagStabilizer_maps_baseLineVector hg
  have hcases :
      octImAction g baseLineVector = nativeBasePoint ∨
        octImAction g baseLineVector = baseLineVector ∨
        octImAction g baseLineVector = nativeBasePoint + baseLineVector := by
    simpa [nativeBaseLineWitness, lineSet, nativeLineSetAt] using hmem
  rcases hcases with hzero | hone | hsum
  · exfalso
    have hfix := nativeFlagStabilizer_fixes_base_point hg
    have hfix' : octImAction g nativeBasePoint = nativeBasePoint := by
      rw [octImPointPerm_apply] at hfix
      simpa [octImAction] using congrArg Subtype.val hfix
    have hinj := octImAction_injective g
    have hneq : baseLineVector ≠ nativeBasePoint := by
      intro h
      have hcoord := congrFun h 3
      simp [baseLineVector, nativeBasePoint] at hcoord
    apply hneq
    apply hinj
    rw [hzero, hfix']
  · exact Or.inl hone
  · exact Or.inr hsum

theorem nativeFlagStabilizer_matrix_baseLineVector_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    matrixAction (autMatrix g⁻¹) (octImToImaginary baseLineVector).1 =
        (octImToImaginary baseLineVector).1 ∨
      matrixAction (autMatrix g⁻¹) (octImToImaginary baseLineVector).1 =
        (octImToImaginary (nativeBasePoint + baseLineVector)).1 := by
  have htransport (v : G2ParabolicLineFiber.OctImF2) :
      (g • octImToImaginary v).1 =
        (octImToImaginary (octImAction g v)).1 := by
    unfold octImAction
    exact congrArg Subtype.val
      (imaginaryOctImEquiv.left_inv (g • octImToImaginary v)).symm
  rcases nativeFlagStabilizer_baseLineVector_cases hg with h | h
  · left
    rw [autMatrix_action_octImToImaginary]
    rw [htransport, h]
  · right
    rw [autMatrix_action_octImToImaginary]
    rw [htransport, h]

end InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixCoordinateBridge
