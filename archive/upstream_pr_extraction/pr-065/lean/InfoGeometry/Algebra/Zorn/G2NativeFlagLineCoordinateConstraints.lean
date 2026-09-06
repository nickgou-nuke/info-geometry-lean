import InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixCoordinateBridge

/-!
# Coordinate consequences of fixing the native base line

This owner records the first coordinate-level consequences of the intrinsic
flag stabilizer.  The statements use the actual native Zorn line carrier and
the explicit base-line witness; no finite-group enumeration is involved.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

noncomputable def baseLineVectorPoint : OctImIsotropicPoint :=
  ⟨baseLineVector, nativeBaseLineWitness_points_valid baseLineVector
    (by
      change baseLineVector ∈ nativeLineSetAt nativeBasePoint baseLineVector
      unfold nativeLineSetAt
      simp)⟩

theorem baseLineVectorPoint_mem_baseIntrinsicLine :
    baseLineVectorPoint ∈ baseIntrinsicLine.1 := by
  apply (mem_baseIntrinsicLine_iff baseLineVectorPoint).2
  exact by
    change baseLineVector ∈
      {nativeBasePoint, baseLineVector, nativeBasePoint + baseLineVector}
    simp

theorem nativeFlagStabilizer_maps_baseLineVector_into_baseLine
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    octImPointPerm g baseLineVectorPoint ∈ baseIntrinsicLine.1 := by
  have hline := nativeFlagStabilizer_baseLine_map hg
  have hmem :
      octImPointPerm g baseLineVectorPoint ∈
        zornZeroTripleMap g baseIntrinsicLine.1 := by
    apply (mem_zornZeroTripleMap_iff g baseIntrinsicLine.1
      (octImPointPerm g baseLineVectorPoint)).2
    simpa using baseLineVectorPoint_mem_baseIntrinsicLine
  rw [hline] at hmem
  exact hmem

theorem nativeFlagStabilizer_maps_baseLineVector_into_nativeWitness
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (octImPointPerm g baseLineVectorPoint).1 ∈ nativeBaseLineWitness := by
  exact (mem_baseIntrinsicLine_iff
    (octImPointPerm g baseLineVectorPoint)).1
    (nativeFlagStabilizer_maps_baseLineVector_into_baseLine hg)

theorem nativeFlagStabilizer_baseLineVector_image_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (octImPointPerm g baseLineVectorPoint).1 = nativeBasePoint ∨
      (octImPointPerm g baseLineVectorPoint).1 = baseLineVector ∨
      (octImPointPerm g baseLineVectorPoint).1 =
        nativeBasePoint + baseLineVector := by
  have hmem := nativeFlagStabilizer_maps_baseLineVector_into_nativeWitness hg
  simpa [nativeBaseLineWitness, lineSet, nativeLineSetAt] using
    (Finset.mem_insert.mp hmem)

theorem nativeFlagStabilizer_baseLineVector_image_ne_base
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (octImPointPerm g baseLineVectorPoint).1 ≠ nativeBasePoint := by
  intro h
  have himage :
      octImPointPerm g baseLineVectorPoint =
        nativeBaseIsotropicPoint := by
    apply Subtype.ext
    exact h
  have hbase := nativeFlagStabilizer_fixes_base_point hg
  have hsame :
      octImPointPerm g baseLineVectorPoint =
        octImPointPerm g nativeBaseIsotropicPoint :=
    himage.trans hbase.symm
  have hpoints : baseLineVectorPoint = nativeBaseIsotropicPoint :=
    (octImPointPerm g).injective hsame
  have hvalues : baseLineVector = nativeBasePoint :=
    congrArg Subtype.val hpoints
  have hcoord := congrFun hvalues 2
  simp [baseLineVector, nativeBasePoint] at hcoord

theorem nativeFlagStabilizer_baseLineVector_image_two_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (octImPointPerm g baseLineVectorPoint).1 = baseLineVector ∨
      (octImPointPerm g baseLineVectorPoint).1 =
        nativeBasePoint + baseLineVector := by
  rcases nativeFlagStabilizer_baseLineVector_image_cases hg with h | h | h
  · exact False.elim
      (nativeFlagStabilizer_baseLineVector_image_ne_base hg h)
  · exact Or.inl h
  · exact Or.inr h

theorem nativeFlagStabilizer_matrix_baseLineVector_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    matrixAction (autMatrix g⁻¹) (octImToImaginary baseLineVector).1 =
        (octImToImaginary baseLineVector).1 ∨
      matrixAction (autMatrix g⁻¹) (octImToImaginary baseLineVector).1 =
        (octImToImaginary (nativeBasePoint + baseLineVector)).1 := by
  have hcases := nativeFlagStabilizer_baseLineVector_image_two_cases hg
  have hcases' :
      octImAction g baseLineVector = baseLineVector ∨
        octImAction g baseLineVector =
          nativeBasePoint + baseLineVector := by
    simpa [octImPointPerm_apply, baseLineVectorPoint] using hcases
  rw [autMatrix_action_octImToImaginary]
  have htransport :
      (g • octImToImaginary baseLineVector).1 =
        (octImToImaginary (octImAction g baseLineVector)).1 := by
    have hround :
        octImToImaginary (octImAction g baseLineVector) =
          g • octImToImaginary baseLineVector := by
      unfold octImAction
      exact imaginaryOctImEquiv.left_inv _
    exact congrArg Subtype.val hround.symm
  rw [htransport]
  rcases hcases' with h | h
  · exact Or.inl (congrArg (fun v => (octImToImaginary v).1) h)
  · exact Or.inr (congrArg (fun v => (octImToImaginary v).1) h)

theorem nativeFlagStabilizer_matrix_basis8_fifth_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    matrixAction (autMatrix g⁻¹) (basis8 5) = basis8 5 ∨
      matrixAction (autMatrix g⁻¹) (basis8 5) =
        add (basis8 4) (basis8 5) := by
  have h := nativeFlagStabilizer_matrix_baseLineVector_cases hg
  rcases h with h | h
  · left
    simpa [octImToImaginary, baseLineVector, basis8, down0, up2,
      ePlus, eMinus, zero, add, add2, boolToZMod, zModToBool] using h
  · right
    simpa [octImToImaginary, baseLineVector, nativeBasePoint, basis8,
      down0, up2, ePlus, eMinus, zero, add, add2, boolToZMod, zModToBool] using h

theorem nativeFlagStabilizer_inv_basis8_fifth_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g⁻¹).1 (basis8 5) = basis8 5 ∨
      (g⁻¹).1 (basis8 5) = add (basis8 4) (basis8 5) := by
  have h := nativeFlagStabilizer_matrix_basis8_fifth_cases hg
  rw [autMatrix_action] at h
  exact h

theorem nativeFlagStabilizer_inv_basis8_fifth_y0
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((g⁻¹).1 (basis8 5)).y0 = true := by
  rcases nativeFlagStabilizer_inv_basis8_fifth_cases hg with h | h
  · simpa [basis8, down0, up2, add, add2] using congrArg
      (fun X : SplitOctF2 => X.y0) h
  · simpa [basis8, down0, up2, add, add2] using congrArg
      (fun X : SplitOctF2 => X.y0) h

theorem nativeFlagStabilizer_inv_basis8_four
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g⁻¹).1 (basis8 4) = basis8 4 := by
  have h := nativeFlagStabilizer_matrix_fixed_nativeBasePoint hg
  rw [autMatrix_action] at h
  simpa [nativeBaseIsotropicPoint, nativeBasePoint, octImToImaginary,
    basis8, up2, ePlus, eMinus, zero, boolToZMod, zModToBool] using h

theorem nativeFlagStabilizer_basis8_four
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    g.1 (basis8 4) = basis8 4 := by
  simpa [inv_inv] using
    (nativeFlagStabilizer_inv_basis8_four
      (nativeFlagStabilizer.inv_mem hg))

theorem nativeFlagStabilizer_basis8_fifth_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    g.1 (basis8 5) = basis8 5 ∨
      g.1 (basis8 5) = add (basis8 4) (basis8 5) := by
  simpa [inv_inv] using
    (nativeFlagStabilizer_inv_basis8_fifth_cases
      (nativeFlagStabilizer.inv_mem hg))

theorem nativeFlagStabilizer_basis8_fifth_y0
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((g.1 (basis8 5))).y0 = true := by
  simpa [inv_inv] using
    (nativeFlagStabilizer_inv_basis8_fifth_y0
      (nativeFlagStabilizer.inv_mem hg))

end InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
