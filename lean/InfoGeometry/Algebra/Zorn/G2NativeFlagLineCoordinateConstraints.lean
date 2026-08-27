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
open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
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

theorem mul_basis8_four_two : mul (basis8 4) (basis8 2) = basis8 6 := rfl

theorem mul_basis8_four_apply_a (X : SplitOctF2) :
    (mul (basis8 4) X).a = X.y2 := by
  dsimp [mul, dot3, cross0, cross1, cross2, basis8, up2, ePlus, eMinus, add2, mul2]
  simp

theorem mul_basis8_four_apply_coordinates (X : SplitOctF2) :
    mul (basis8 4) X =
      ⟨X.y2, false, false, false, X.b,
        X.x1, X.x0, false⟩ := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  simp [mul, dot3, cross0, cross1, cross2, basis8, up2, ePlus,
    eMinus, add2, mul2]

theorem mul_basis8_four_apply_y0 (X : SplitOctF2) :
    (mul (basis8 4) X).y0 = X.x1 := by
  rw [mul_basis8_four_apply_coordinates]

theorem nativeFlagStabilizer_basis8_four_mul_two
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    mul (basis8 4) (g.1 (basis8 2)) = g.1 (basis8 6) := by
  have h4 := nativeFlagStabilizer_basis8_four hg
  calc
    mul (basis8 4) (g.1 (basis8 2)) =
        mul (g.1 (basis8 4)) (g.1 (basis8 2)) := by rw [h4]
    _ = g.1 (mul (basis8 4) (basis8 2)) := (g.2.2.2 (basis8 4) (basis8 2)).symm
    _ = g.1 (basis8 6) := by rw [mul_basis8_four_two]

theorem nativeFlagStabilizer_basis8_two_x1_eq_basis8_six_y0
  {g : SplitOctF2Aut}
  (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 2)).x1 = (g.1 (basis8 6)).y0 := by
  have hmul := nativeFlagStabilizer_basis8_four_mul_two hg
  have hy := congrArg (fun X : SplitOctF2 => X.y0) hmul
  change (mul (basis8 4) (g.1 (basis8 2))).y0 =
    (g.1 (basis8 6)).y0 at hy
  rw [mul_basis8_four_apply_y0] at hy
  exact hy

theorem nativeFlagStabilizer_basis8_six_coordinate_form
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    g.1 (basis8 6) =
      ⟨(g.1 (basis8 2)).y2, false, false, false,
        (g.1 (basis8 2)).b, (g.1 (basis8 2)).x1,
        (g.1 (basis8 2)).x0, false⟩ := by
  rw [← nativeFlagStabilizer_basis8_four_mul_two hg]
  exact mul_basis8_four_apply_coordinates (g.1 (basis8 2))

theorem mul_basis8_six_four : mul (basis8 6) (basis8 4) = zero := rfl

theorem mul_apply_basis8_four_x2 (X : SplitOctF2) :
    (mul X (basis8 4)).x2 = X.a := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  dsimp [mul, cross2, add2, mul2, basis8, up2, ePlus, eMinus]
  simp

theorem nativeFlagStabilizer_basis8_six_mul_four
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    mul (g.1 (basis8 6)) (basis8 4) = zero := by
  have h4 := nativeFlagStabilizer_basis8_four hg
  calc
    mul (g.1 (basis8 6)) (basis8 4) =
        mul (g.1 (basis8 6)) (g.1 (basis8 4)) := by rw [h4]
    _ = g.1 (mul (basis8 6) (basis8 4)) := (g.2.2.2 (basis8 6) (basis8 4)).symm
    _ = g.1 zero := by rw [mul_basis8_six_four]
    _ = zero := automorphism_map_zero g

theorem nativeFlagStabilizer_basis8_six_a
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 6)).a = false := by
  have h := nativeFlagStabilizer_basis8_six_mul_four hg
  have hx2 := congrArg (fun X : SplitOctF2 => X.x2) h
  simpa [mul_apply_basis8_four_x2] using hx2

theorem nativeFlagStabilizer_basis8_two_y2
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 2)).y2 = false := by
  have hprod := nativeFlagStabilizer_basis8_four_mul_two hg
  have ha : (mul (basis8 4) (g.1 (basis8 2))).a = (g.1 (basis8 6)).a := by
    rw [hprod]
  rw [mul_basis8_four_apply_a] at ha
  rw [ha]
  exact nativeFlagStabilizer_basis8_six_a hg

theorem automorphism_basis8_two_square_zero (g : SplitOctF2Aut) :
    mul (g.1 (basis8 2)) (g.1 (basis8 2)) = zero := by
  calc
    mul (g.1 (basis8 2)) (g.1 (basis8 2)) =
        g.1 (mul (basis8 2) (basis8 2)) :=
      (g.2.2.2 (basis8 2) (basis8 2)).symm
    _ = g.1 zero := by rfl
    _ = zero := automorphism_map_zero g

theorem mul_basis8_two_fifth : mul (basis8 2) (basis8 5) = basis8 0 := rfl

theorem mul_basis8_two_four : mul (basis8 2) (basis8 4) = basis8 6 := rfl

theorem nativeFlagStabilizer_basis8_two_mul_four
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    mul (g.1 (basis8 2)) (basis8 4) = g.1 (basis8 6) := by
  have h4 := nativeFlagStabilizer_basis8_four hg
  calc
    mul (g.1 (basis8 2)) (basis8 4) =
        mul (g.1 (basis8 2)) (g.1 (basis8 4)) := by rw [h4]
    _ = g.1 (mul (basis8 2) (basis8 4)) := (g.2.2.2 (basis8 2) (basis8 4)).symm
    _ = g.1 (basis8 6) := by rw [mul_basis8_two_four]

theorem automorphism_basis8_two_mul_fifth (g : SplitOctF2Aut) :
    mul (g.1 (basis8 2)) (g.1 (basis8 5)) = g.1 (basis8 0) := by
  calc
    mul (g.1 (basis8 2)) (g.1 (basis8 5)) =
        g.1 (mul (basis8 2) (basis8 5)) := (g.2.2.2 (basis8 2) (basis8 5)).symm
    _ = g.1 (basis8 0) := by rw [mul_basis8_two_fifth]

theorem nativeFlagStabilizer_basis8_two_mul_fifth
    {g : SplitOctF2Aut}
    (_hg : g ∈ nativeFlagStabilizer) :
    mul (g.1 (basis8 2)) (g.1 (basis8 5)) = g.1 (basis8 0) :=
  automorphism_basis8_two_mul_fifth g

theorem mul_apply_basis8_fifth_a (X : SplitOctF2) :
    (mul X (basis8 5)).a = X.x0 := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  dsimp [mul, dot3, basis8, down0, add2, mul2]
  simp

theorem mul_apply_basis8_four_add_fifth_a (X : SplitOctF2) :
    (mul X (add (basis8 4) (basis8 5))).a = X.x0 := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  dsimp [mul, dot3, basis8, up2, down0, add, add2, mul2]
  simp

theorem nativeFlagStabilizer_mul_apply_basis8_fifth_a
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (X : SplitOctF2) :
    (mul X (g.1 (basis8 5))).a = X.x0 := by
  rcases nativeFlagStabilizer_basis8_fifth_cases hg with h5 | h5
  · rw [h5, mul_apply_basis8_fifth_a]
  · rw [h5, mul_apply_basis8_four_add_fifth_a]

theorem nativeFlagStabilizer_basis8_two_x0_eq_basis8_zero_a
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 2)).x0 = (g.1 (basis8 0)).a := by
  have hproj := nativeFlagStabilizer_mul_apply_basis8_fifth_a hg (g.1 (basis8 2))
  have hmul := automorphism_basis8_two_mul_fifth g
  rw [← hproj]
  rw [hmul]

theorem mul_basis8_fifth_two : mul (basis8 5) (basis8 2) = basis8 1 := rfl

theorem automorphism_basis8_fifth_mul_two (g : SplitOctF2Aut) :
    mul (g.1 (basis8 5)) (g.1 (basis8 2)) = g.1 (basis8 1) := by
  calc
    mul (g.1 (basis8 5)) (g.1 (basis8 2)) =
        g.1 (mul (basis8 5) (basis8 2)) := (g.2.2.2 (basis8 5) (basis8 2)).symm
    _ = g.1 (basis8 1) := by rw [mul_basis8_fifth_two]

theorem mul_basis8_fifth_apply_a (X : SplitOctF2) :
    (mul (basis8 5) X).a = false := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  dsimp [mul, dot3, basis8, down0, add2, mul2]
  simp

theorem mul_basis8_four_add_fifth_apply_a (X : SplitOctF2) (hy2 : X.y2 = false) :
    (mul (add (basis8 4) (basis8 5)) X).a = false := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  change y2 = false at hy2
  subst y2
  dsimp [mul, dot3, basis8, up2, down0, add, add2, mul2]
  simp

theorem nativeFlagStabilizer_basis8_one_a
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 1)).a = false := by
  have hy2 := nativeFlagStabilizer_basis8_two_y2 hg
  have hmul := automorphism_basis8_fifth_mul_two g
  rw [← hmul]
  rcases nativeFlagStabilizer_basis8_fifth_cases hg with h5 | h5
  · rw [h5, mul_basis8_fifth_apply_a]
  · rw [h5, mul_basis8_four_add_fifth_apply_a (g.1 (basis8 2)) hy2]

theorem basis8_zero_add_one_eq_one : add (basis8 0) (basis8 1) = one := rfl

theorem nativeFlagStabilizer_basis8_zero_a
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 0)).a = true := by
  have hone : g.1 one = one := g.2.1
  have hsplit : g.1 one = add (g.1 (basis8 0)) (g.1 (basis8 1)) := by
    rw [← g.2.2.1, basis8_zero_add_one_eq_one]
  have ha : (g.1 one).a = (one : SplitOctF2).a := by rw [hone]
  have hone_a : (one : SplitOctF2).a = true := rfl
  rw [hsplit] at ha
  change (add2 (g.1 (basis8 0)).a (g.1 (basis8 1)).a) = true at ha
  rw [nativeFlagStabilizer_basis8_one_a hg] at ha
  change (add2 (g.1 (basis8 0)).a false) = true at ha
  simpa [add2] using ha

theorem nativeFlagStabilizer_basis8_two_x0
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 2)).x0 = true := by
  rw [nativeFlagStabilizer_basis8_two_x0_eq_basis8_zero_a hg]
  exact nativeFlagStabilizer_basis8_zero_a hg

theorem nativeFlagStabilizer_basis8_two_trace_zero
    {g : SplitOctF2Aut}
    (_hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 2)).a = (g.1 (basis8 2)).b := by
  have htrace : TraceZero (basis8 2) := by rfl
  exact automorphism_map_traceZero g (basis8 2) htrace

theorem nativeFlagStabilizer_basis8_two_partial_shape
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a b x1 x2 y0 y1 : F2Bit,
      g.1 (basis8 2) = ⟨a, b, true, x1, x2, y0, y1, false⟩ := by
  let X := g.1 (basis8 2)
  have hx0 : X.x0 = true := nativeFlagStabilizer_basis8_two_x0 hg
  have hy2 : X.y2 = false := nativeFlagStabilizer_basis8_two_y2 hg
  refine ⟨X.a, X.b, X.x1, X.x2, X.y0, X.y1, ?_⟩
  change X = ⟨X.a, X.b, true, X.x1, X.x2, X.y0, X.y1, false⟩
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  change x0 = true at hx0
  change y2 = false at hy2
  subst x0
  subst y2
  rfl

theorem nativeFlagStabilizer_basis8_two_trace_zero_shape
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a x1 x2 y0 y1 : F2Bit,
      g.1 (basis8 2) = ⟨a, a, true, x1, x2, y0, y1, false⟩ := by
  let X := g.1 (basis8 2)
  have hshape := nativeFlagStabilizer_basis8_two_partial_shape hg
  have htrace := nativeFlagStabilizer_basis8_two_trace_zero hg
  rcases hshape with ⟨a, b, x1, x2, y0, y1, hX⟩
  refine ⟨a, x1, x2, y0, y1, ?_⟩
  rw [hX]
  rw [hX] at htrace
  cases htrace
  rfl

theorem trace_zero_zornNorm_iff_dot3_eq_a
    {X : SplitOctF2} (htrace : X.a = X.b) :
    zornNorm X = false ↔
      dot3 X.x0 X.x1 X.x2 X.y0 X.y1 X.y2 = X.a := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  change a = b at htrace
  subst b
  cases a <;> simp [zornNorm, dot3, mul2]

theorem nativeFlagStabilizer_basis8_two_dot3_eq_a
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    dot3 (g.1 (basis8 2)).x0 (g.1 (basis8 2)).x1
      (g.1 (basis8 2)).x2 (g.1 (basis8 2)).y0
      (g.1 (basis8 2)).y1 (g.1 (basis8 2)).y2 =
      (g.1 (basis8 2)).a := by
  let X := g.1 (basis8 2)
  have htrace : TraceZero X := by
    exact nativeFlagStabilizer_basis8_two_trace_zero hg
  have hsquare : mul X X = zero := by
    exact automorphism_basis8_two_square_zero g
  have hiso : Isotropic X :=
    (isotropic_iff_square_zero X htrace).2 hsquare
  exact (trace_zero_zornNorm_iff_dot3_eq_a htrace).1 hiso

theorem nativeFlagStabilizer_basis8_two_peirce_dot3_formula
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    add2 (g.1 (basis8 2)).y0
      (mul2 (g.1 (basis8 2)).x1 (g.1 (basis8 2)).y1) =
      (g.1 (basis8 2)).a := by
  have hdot := nativeFlagStabilizer_basis8_two_dot3_eq_a hg
  have hx0 := nativeFlagStabilizer_basis8_two_x0 hg
  have hy2 := nativeFlagStabilizer_basis8_two_y2 hg
  revert hdot hx0 hy2
  generalize (g.1 (basis8 2)) = X
  rintro hdot hx0 hy2
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  change x0 = true at hx0
  change y2 = false at hy2
  subst x0
  subst y2
  dsimp [dot3, add2, mul2] at hdot
  simpa [add2, mul2] using hdot

theorem nativeFlagStabilizer_basis8_two_cartan_sector_zero
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (ha : (g.1 (basis8 2)).a = false) :
    (g.1 (basis8 2)).b = false ∧
    add2 (g.1 (basis8 2)).y0
      (mul2 (g.1 (basis8 2)).x1 (g.1 (basis8 2)).y1) = false := by
  have htr := nativeFlagStabilizer_basis8_two_trace_zero hg
  have hdot := nativeFlagStabilizer_basis8_two_peirce_dot3_formula hg
  rw [ha] at htr hdot
  exact ⟨htr.symm, hdot⟩

theorem nativeFlagStabilizer_basis8_two_cartan_sector_one
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (ha : (g.1 (basis8 2)).a = true) :
    (g.1 (basis8 2)).b = true ∧
    add2 (g.1 (basis8 2)).y0
      (mul2 (g.1 (basis8 2)).x1 (g.1 (basis8 2)).y1) = true := by
  have htr := nativeFlagStabilizer_basis8_two_trace_zero hg
  have hdot := nativeFlagStabilizer_basis8_two_peirce_dot3_formula hg
  rw [ha] at htr hdot
  exact ⟨htr.symm, hdot⟩

theorem mul_apply_basis8_three_coordinates (X : SplitOctF2) :
    mul X (basis8 3) =
      ⟨false, X.y1, false, X.a, false, X.x2, false, X.x0⟩ := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;>
    simp [mul, dot3, cross0, cross1, cross2, basis8, up0, up1,
      up2, down0, down1, down2, ePlus, eMinus, add2, mul2]

theorem mul_basis8_two_shape_basis8_three_eq_basis8_seven
    {X : SplitOctF2}
    (ha : X.a = false) (hx0 : X.x0 = true)
    (hx2 : X.x2 = false) (hy1 : X.y1 = false) :
    mul X (basis8 3) = basis8 7 := by
  rw [mul_apply_basis8_three_coordinates]
  simp [ha, hx0, hx2, hy1, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

theorem mul_basis8_four_seven : mul (basis8 4) (basis8 7) = basis8 0 := rfl

theorem nativeFlagStabilizer_basis8_four_mul_seven
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    mul (basis8 4) (g.1 (basis8 7)) = g.1 (basis8 0) := by
  have h4 := nativeFlagStabilizer_basis8_four hg
  calc
    mul (basis8 4) (g.1 (basis8 7)) =
        mul (g.1 (basis8 4)) (g.1 (basis8 7)) := by rw [h4]
    _ = g.1 (mul (basis8 4) (basis8 7)) := (g.2.2.2 (basis8 4) (basis8 7)).symm
    _ = g.1 (basis8 0) := by rw [mul_basis8_four_seven]

theorem nativeFlagStabilizer_basis8_seven_y2
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 7)).y2 = true := by
  have hprod := nativeFlagStabilizer_basis8_four_mul_seven hg
  have ha : (mul (basis8 4) (g.1 (basis8 7))).a = (g.1 (basis8 0)).a := by
    rw [hprod]
  rw [mul_basis8_four_apply_a] at ha
  rw [ha]
  exact nativeFlagStabilizer_basis8_zero_a hg

theorem nativeFlagStabilizer_basis8_seven_trace_zero
    {g : SplitOctF2Aut}
    (_hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 7)).a = (g.1 (basis8 7)).b := by
  have htrace : TraceZero (basis8 7) := by rfl
  exact automorphism_map_traceZero g (basis8 7) htrace

theorem mul_basis8_seven_four : mul (basis8 7) (basis8 4) = basis8 1 := rfl

theorem nativeFlagStabilizer_basis8_seven_mul_four
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    mul (g.1 (basis8 7)) (basis8 4) = g.1 (basis8 1) := by
  have h4 := nativeFlagStabilizer_basis8_four hg
  calc
    mul (g.1 (basis8 7)) (basis8 4) =
        mul (g.1 (basis8 7)) (g.1 (basis8 4)) := by rw [h4]
    _ = g.1 (mul (basis8 7) (basis8 4)) := (g.2.2.2 (basis8 7) (basis8 4)).symm
    _ = g.1 (basis8 1) := by rw [mul_basis8_seven_four]

theorem mul_basis8_three_four : mul (basis8 3) (basis8 4) = basis8 5 := rfl

theorem nativeFlagStabilizer_basis8_three_mul_four
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    mul (g.1 (basis8 3)) (basis8 4) = g.1 (basis8 5) := by
  have h4 := nativeFlagStabilizer_basis8_four hg
  calc
    mul (g.1 (basis8 3)) (basis8 4) =
        mul (g.1 (basis8 3)) (g.1 (basis8 4)) := by rw [h4]
    _ = g.1 (mul (basis8 3) (basis8 4)) := (g.2.2.2 (basis8 3) (basis8 4)).symm
    _ = g.1 (basis8 5) := by rw [mul_basis8_three_four]

theorem nativeFlagStabilizer_basis8_three_a_eq_basis8_fifth_x2
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 3)).a = (g.1 (basis8 5)).x2 := by
  have h := nativeFlagStabilizer_basis8_three_mul_four hg
  have hx2 := congrArg (fun X : SplitOctF2 => X.x2) h
  simpa [mul_apply_basis8_four_x2] using hx2

theorem mul_basis8_seven_fifth : mul (basis8 7) (basis8 5) = basis8 3 := rfl

theorem nativeFlagStabilizer_basis8_seven_mul_fifth
    (g : SplitOctF2Aut) :
    mul (g.1 (basis8 7)) (g.1 (basis8 5)) = g.1 (basis8 3) := by
  calc
    mul (g.1 (basis8 7)) (g.1 (basis8 5)) =
        g.1 (mul (basis8 7) (basis8 5)) := (g.2.2.2 (basis8 7) (basis8 5)).symm
    _ = g.1 (basis8 3) := by rw [mul_basis8_seven_fifth]

theorem mul_basis8_seven_sheared_y2
    (X : SplitOctF2) :
    (mul X (add (basis8 4) (basis8 5))).y2 = false := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  simp [mul, cross2, add, add2, mul2, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

theorem nativeFlagStabilizer_basis8_three_y2_zero_of_fifth_fixed
    {g : SplitOctF2Aut}
    (h5 : g.1 (basis8 5) = basis8 5) :
    (g.1 (basis8 3)).y2 = false := by
  have hmul := nativeFlagStabilizer_basis8_seven_mul_fifth g
  have hy := congrArg (fun X : SplitOctF2 => X.y2) hmul
  rw [h5] at hy
  simp [mul, cross2, add2, mul2, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2] at hy
  exact hy

theorem nativeFlagStabilizer_basis8_three_y2_of_fifth_sheared
    {g : SplitOctF2Aut}
    (h5 : g.1 (basis8 5) = add (basis8 4) (basis8 5)) :
    (g.1 (basis8 3)).y2 =
      (mul (g.1 (basis8 7)) (add (basis8 4) (basis8 5))).y2 := by
  have hmul := nativeFlagStabilizer_basis8_seven_mul_fifth g
  rw [h5] at hmul
  exact (congrArg (fun X : SplitOctF2 => X.y2) hmul).symm

theorem nativeFlagStabilizer_basis8_three_y2_zero_of_fifth_sheared
    {g : SplitOctF2Aut}
    (h5 : g.1 (basis8 5) = add (basis8 4) (basis8 5)) :
    (g.1 (basis8 3)).y2 = false := by
  rw [nativeFlagStabilizer_basis8_three_y2_of_fifth_sheared h5]
  exact mul_basis8_seven_sheared_y2 (g.1 (basis8 7))

theorem nativeFlagStabilizer_basis8_three_y2_zero
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 3)).y2 = false := by
  rcases nativeFlagStabilizer_basis8_fifth_cases hg with h5 | h5
  · exact nativeFlagStabilizer_basis8_three_y2_zero_of_fifth_fixed h5
  · exact nativeFlagStabilizer_basis8_three_y2_zero_of_fifth_sheared h5

theorem nativeFlagStabilizer_basis8_seven_x0_eq_basis8_fifth_x2
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 7)).x0 = (g.1 (basis8 5)).x2 := by
  have hproj := nativeFlagStabilizer_mul_apply_basis8_fifth_a hg (g.1 (basis8 7))
  have hmul := nativeFlagStabilizer_basis8_seven_mul_fifth g
  have ha : (mul (g.1 (basis8 7)) (g.1 (basis8 5))).a = (g.1 (basis8 3)).a := by
    rw [hmul]
  rw [hproj] at ha
  rw [ha]
  exact nativeFlagStabilizer_basis8_three_a_eq_basis8_fifth_x2 hg

theorem nativeFlagStabilizer_basis8_seven_x0_iff_fifth_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((g.1 (basis8 7)).x0 = false ∧ g.1 (basis8 5) = basis8 5) ∨
    ((g.1 (basis8 7)).x0 = true ∧ g.1 (basis8 5) = add (basis8 4) (basis8 5)) := by
  have hx0 := nativeFlagStabilizer_basis8_seven_x0_eq_basis8_fifth_x2 hg
  rcases nativeFlagStabilizer_basis8_fifth_cases hg with h5 | h5
  · left
    refine ⟨?_, h5⟩
    rw [hx0, h5]
    rfl
  · right
    refine ⟨?_, h5⟩
    rw [hx0, h5]
    rfl

end InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
