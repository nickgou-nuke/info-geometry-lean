import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeLineFiber

/-!
# Native base flag for the intrinsic incidence carrier

The base flag is constructed on the Zorn-zero intrinsic carrier.  The older
`octCross` line predicate is intentionally not used here.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

instance : DecidableEq OctImIsotropicPoint := by infer_instance

private theorem baseLineWitness_points_valid (v : OctImF2)
    (hv : v ∈ nativeBaseLineWitness) :
    splitQuad v = 0 ∧ v ≠ 0 := by
  simp only [nativeBaseLineWitness, lineSet, nativeLineSetAt,
    Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hbase | hrest
  · subst v
    constructor
    · simp [splitQuad, nativeBasePoint, canonicalBasePoint]
    · intro h
      have h2 := congrFun h (2 : Fin 7)
      norm_num [nativeBasePoint, canonicalBasePoint] at h2
  · rcases hrest with hvec | hsum
    · subst v
      constructor
      · simp [splitQuad, baseLineVector]
      · intro h
        have h3 := congrFun h (3 : Fin 7)
        norm_num [baseLineVector] at h3
    · subst v
      constructor
      · simp [splitQuad, nativeBasePoint, canonicalBasePoint, baseLineVector]
      · intro h
        have h2 := congrFun h (2 : Fin 7)
        have hneq : (2 : Fin 7) ≠ 3 := by
          intro heq
          have hv := congrArg Fin.val heq
          norm_num at hv
        simp [nativeBasePoint, canonicalBasePoint, baseLineVector, hneq] at h2

theorem nativeBaseLineWitness_points_valid (v : OctImF2)
    (hv : v ∈ nativeBaseLineWitness) :
    splitQuad v = 0 ∧ v ≠ 0 :=
  baseLineWitness_points_valid v hv

private def intrinsicPointOf (v : OctImF2)
    (hv : v ∈ nativeBaseLineWitness) : OctImIsotropicPoint :=
  ⟨v, baseLineWitness_points_valid v hv⟩

def baseIntrinsicLineSet : Finset OctImIsotropicPoint :=
  nativeBaseLineWitness.attach.image (fun v => intrinsicPointOf v.1 v.2)

theorem baseIntrinsicLineSet_card : baseIntrinsicLineSet.card = 3 := by
  calc
    baseIntrinsicLineSet.card = nativeBaseLineWitness.attach.card := by
      unfold baseIntrinsicLineSet
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      apply Subtype.ext
      exact congrArg (fun p : OctImIsotropicPoint => p.1) hab
    _ = nativeBaseLineWitness.card := by simp
    _ = 3 := by
      simpa [nativeBaseLineWitness] using
        lineSet_card baseLineVector baseLineVector_mem_candidates

private theorem mem_baseIntrinsicLineSet_iff (v : OctImIsotropicPoint) :
    v ∈ baseIntrinsicLineSet ↔ v.1 ∈ nativeBaseLineWitness := by
  unfold baseIntrinsicLineSet
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨w, hw, hEq⟩
    have hval : w.1 = v.1 := congrArg Subtype.val hEq
    simpa [hval] using w.2
  · intro hv
    refine Finset.mem_image.mpr ⟨⟨v.1, hv⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

private def baseLineVectorPoint : OctImIsotropicPoint :=
  ⟨baseLineVector, nativeBaseLineWitness_points_valid baseLineVector (by
    simp [nativeBaseLineWitness, lineSet, nativeLineSetAt])⟩

private def baseLineSumPoint : OctImIsotropicPoint :=
  ⟨nativeBasePoint + baseLineVector,
    nativeBaseLineWitness_points_valid (nativeBasePoint + baseLineVector) (by
      simp [nativeBaseLineWitness, lineSet, nativeLineSetAt])⟩

private theorem basePoint_related_to_baseLineVector :
    G2InvariantIncidenceCandidates.ZornZeroRelated
      nativeBaseIsotropicPoint baseLineVectorPoint := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro h
    have h2 := congrFun h (2 : Fin 7)
    simp [nativeBaseIsotropicPoint, baseLineVectorPoint, baseLineVector,
      nativeBasePoint, canonicalBasePoint] at h2
  · change mul (embed nativeBasePoint) (embed baseLineVector) = zero
    ext <;>
      simp [embed, octImToImaginary, zModToBool, nativeBasePoint,
        canonicalBasePoint, baseLineVector, mul, zero, add2, mul2,
        dot3, cross0, cross1, cross2]
  · change mul (embed baseLineVector) (embed nativeBasePoint) = zero
    ext <;>
      simp [embed, octImToImaginary, zModToBool, nativeBasePoint,
        canonicalBasePoint, baseLineVector, mul, zero, add2, mul2,
        dot3, cross0, cross1, cross2]

private theorem basePoint_related_to_baseLineSum :
    G2InvariantIncidenceCandidates.ZornZeroRelated
      nativeBaseIsotropicPoint baseLineSumPoint := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro h
    have h3 := congrFun h (3 : Fin 7)
    simp [nativeBaseIsotropicPoint, baseLineSumPoint, baseLineVector,
      nativeBasePoint, canonicalBasePoint] at h3
  · change mul (embed nativeBasePoint)
      (embed (nativeBasePoint + baseLineVector)) = zero
    ext <;>
      simp [embed, octImToImaginary, zModToBool, nativeBasePoint,
        canonicalBasePoint, baseLineVector, mul, zero, add2, mul2,
        dot3, cross0, cross1, cross2]
  · change mul (embed (nativeBasePoint + baseLineVector))
      (embed nativeBasePoint) = zero
    ext <;>
      simp [embed, octImToImaginary, zModToBool, nativeBasePoint,
        canonicalBasePoint, baseLineVector, mul, zero, add2, mul2,
        dot3, cross0, cross1, cross2]

private theorem baseLineVector_related_to_baseLineSum :
    G2InvariantIncidenceCandidates.ZornZeroRelated
      baseLineVectorPoint baseLineSumPoint := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro h
    have h2 := congrFun h (2 : Fin 7)
    simp [baseLineVectorPoint, baseLineSumPoint, baseLineVector,
      nativeBasePoint, canonicalBasePoint] at h2
  · change mul (embed baseLineVector)
      (embed (nativeBasePoint + baseLineVector)) = zero
    ext <;>
      simp [embed, octImToImaginary, zModToBool, nativeBasePoint,
        canonicalBasePoint, baseLineVector, mul, zero, add2, mul2,
        dot3, cross0, cross1, cross2]
  · change mul (embed (nativeBasePoint + baseLineVector))
      (embed baseLineVector) = zero
    ext <;>
      simp [embed, octImToImaginary, zModToBool, nativeBasePoint,
        canonicalBasePoint, baseLineVector, mul, zero, add2, mul2,
        dot3, cross0, cross1, cross2]

noncomputable def baseIntrinsicLine : IntrinsicLine nativeBaseIsotropicPoint := by
  refine ⟨baseIntrinsicLineSet, ?_, baseIntrinsicLineSet_card, ?_⟩
  · apply (mem_baseIntrinsicLineSet_iff _).2
    change nativeBasePoint ∈ nativeBaseLineWitness
    rw [nativeBaseLineWitness]
    simp [lineSet, nativeLineSetAt]
  · intro u v hu hv huv
    have hu' := (mem_baseIntrinsicLineSet_iff u).1 hu
    have hv' := (mem_baseIntrinsicLineSet_iff v).1 hv
    simp only [nativeBaseLineWitness, lineSet, nativeLineSetAt,
      Finset.mem_insert, Finset.mem_singleton] at hu' hv'
    rcases hu' with hu0 | huRest
    · have huEq : u = nativeBaseIsotropicPoint := by
        apply Subtype.ext
        exact hu0
      rcases hv' with hv0 | hvRest
      · have hvEq : v = nativeBaseIsotropicPoint := by
          apply Subtype.ext
          exact hv0
        exact False.elim (huv (huEq.trans hvEq.symm))
      · rcases hvRest with hv1 | hv2
        · have hvEq : v = baseLineVectorPoint := by
            apply Subtype.ext
            exact hv1
          rw [huEq, hvEq]
          exact basePoint_related_to_baseLineVector
        · have hvEq : v = baseLineSumPoint := by
            apply Subtype.ext
            exact hv2
          rw [huEq, hvEq]
          exact basePoint_related_to_baseLineSum
    · rcases huRest with hu1 | hu2
      · have huEq : u = baseLineVectorPoint := by
          apply Subtype.ext
          exact hu1
        rcases hv' with hv0 | hvRest
        · have hvEq : v = nativeBaseIsotropicPoint := by
            apply Subtype.ext
            exact hv0
          rw [huEq, hvEq]
          exact (zornZeroRelated_symmetric _ _).mp
            basePoint_related_to_baseLineVector
        · rcases hvRest with hv1 | hv2
          · have hvEq : v = baseLineVectorPoint := by
              apply Subtype.ext
              exact hv1
            exact False.elim (huv (huEq.trans hvEq.symm))
          · have hvEq : v = baseLineSumPoint := by
              apply Subtype.ext
              exact hv2
            rw [huEq, hvEq]
            exact baseLineVector_related_to_baseLineSum
      · have huEq : u = baseLineSumPoint := by
          apply Subtype.ext
          exact hu2
        rcases hv' with hv0 | hvRest
        · have hvEq : v = nativeBaseIsotropicPoint := by
            apply Subtype.ext
            exact hv0
          rw [huEq, hvEq]
          exact (zornZeroRelated_symmetric _ _).mp
            basePoint_related_to_baseLineSum
        · rcases hvRest with hv1 | hv2
          · have hvEq : v = baseLineVectorPoint := by
              apply Subtype.ext
              exact hv1
            rw [huEq, hvEq]
            exact (zornZeroRelated_symmetric _ _).mp
              baseLineVector_related_to_baseLineSum
          · have hvEq : v = baseLineSumPoint := by
              apply Subtype.ext
              exact hv2
            exact False.elim (huv (huEq.trans hvEq.symm))

noncomputable def baseIntrinsicFlag : IntrinsicFlag :=
  ⟨nativeBaseIsotropicPoint, baseIntrinsicLine⟩

theorem mem_baseIntrinsicLine_iff (v : OctImIsotropicPoint) :
    v ∈ baseIntrinsicLine.1 ↔ v.1 ∈ nativeBaseLineWitness := by
  exact mem_baseIntrinsicLineSet_iff v

end InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
