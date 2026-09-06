import InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge
import InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
import InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
import InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
import InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization
import InfoGeometry.Lie.CanonicalZornMathlibRootSpace

/-!
# Finite G₂ labels on the native nonzero-root carrier

This file contains only the index transport which is common to the finite
root model and the characteristic-zero native root-space model.  Weyl
equivariance and normalization are deliberately downstream.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport

open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge
open InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
open InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
open InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
open InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization
open InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction
open InfoGeometry.Physics.Octonion
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornMathlibRootSpace
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivationRootBridge

/-! Transport of the already-proved finite Weyl permutation to the native
nonzero-root index.  This is only an index permutation: it makes no claim
about the adjoint action on derivations. -/

def nonzeroIndexAction
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (i : nonzeroIndex) : nonzeroIndex :=
  rootIndexEquiv
    (weylRootAction p (rootIndexEquiv.symm i))

theorem nonzeroIndexAction_bijective
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    Function.Bijective (nonzeroIndexAction p) := by
  unfold nonzeroIndexAction
  exact (rootIndexEquiv.bijective.comp
    ((weylRootActionEquiv p).bijective.comp
      rootIndexEquiv.symm.bijective))

theorem nonzeroIndexAction_apply_root
    (p : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2)
    (r : G2Root) :
    nonzeroIndexAction p (rootIndexOf r) =
      rootIndexOf (weylRootAction p r) := by
  unfold nonzeroIndexAction
  change rootIndexOf
      (weylRootAction p
        (rootIndexEquiv.symm (rootIndexOf r))) = _
  have h : rootIndexEquiv.symm (rootIndexOf r) = r := by
    exact rootIndexEquiv.symm_apply_apply r
  rw [h]

theorem nonzeroIndexAction_one (i : nonzeroIndex) :
    nonzeroIndexAction (0, false) i = i := by
  obtain ⟨r, rfl⟩ := rootIndexEquiv.surjective i
  change nonzeroIndexAction (0, false) (rootIndexOf r) = _
  rw [nonzeroIndexAction_apply_root]
  simp [weylRootAction, cActionPow, cActionPowNat]

/-! The finite root label and its canonical Mathlib root vector are connected
by the existing coordinate readout.  `rootIndexOf` contributes only the
non-Cartan channel bookkeeping; it does not introduce a second root carrier. -/
theorem rootIndexOf_canonical_derivation_transport (r : G2Root) :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (zornDerivationRootRepresentation r) =
      rootDerivation (rootIndexOf r).1 := by
  simpa [rootIndexOf_val] using
    (InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge.finiteRoot_derivation_canonical_transport r)

theorem rootIndexOf_canonical_derivation_injective :
    Function.Injective (fun r : G2Root =>
      InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (zornDerivationRootRepresentation r)) := by
  exact InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge.finiteRoot_canonical_derivation_injective

theorem realWeylCycle_E22 :
    nativeAut realWeylCycle (ZornVectorMatrix.E22 : ZornVectorMatrix ℝ) =
      ZornVectorMatrix.E22 := by
  have hE : nativeCircularBasis (4 : Fin 8) =
      (ZornVectorMatrix.E22 : ZornVectorMatrix ℝ) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 4) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_scalarMinus_nativeE22
  have h := realWeylCycle_nativeCircularBasis (4 : Fin 8)
  rw [← hE]
  simpa [cycleFrameIndex] using h

theorem realWeylCycle_U (i : Fin 3) :
    nativeAut realWeylCycle (ZornVectorMatrix.U i) =
      ZornVectorMatrix.U (nextColor i) := by
  fin_cases i
  · have h := realWeylCycle_nativeCircularBasis (1 : Fin 8)
    norm_num [nextColor]
    have h0 : nativeCircularBasis 1 = (ZornVectorMatrix.U 0 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 1) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 0
    have h1 : nativeCircularBasis 2 = (ZornVectorMatrix.U 1 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 2) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 1
    change nativeAut realWeylCycle (ZornVectorMatrix.U 0) = ZornVectorMatrix.U 1
    rw [← h0, ← h1]
    simpa [cycleFrameIndex]
  · have h := realWeylCycle_nativeCircularBasis (2 : Fin 8)
    norm_num [nextColor]
    have h1 : nativeCircularBasis 2 = (ZornVectorMatrix.U 1 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 2) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 1
    have h2 : nativeCircularBasis 3 = (ZornVectorMatrix.U 2 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 3) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 2
    change nativeAut realWeylCycle (ZornVectorMatrix.U 1) = ZornVectorMatrix.U 2
    rw [← h1, ← h2]
    simpa [cycleFrameIndex]
  · have h := realWeylCycle_nativeCircularBasis (3 : Fin 8)
    norm_num [nextColor]
    have h2 : nativeCircularBasis 3 = (ZornVectorMatrix.U 2 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 3) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 2
    have h0 : nativeCircularBasis 1 = (ZornVectorMatrix.U 0 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 1) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 0
    change nativeAut realWeylCycle (ZornVectorMatrix.U 2) = ZornVectorMatrix.U 0
    rw [← h2, ← h0]
    simpa [cycleFrameIndex]

theorem realWeylCycle_V (i : Fin 3) :
    nativeAut realWeylCycle (ZornVectorMatrix.V i) =
      ZornVectorMatrix.V (nextColor i) := by
  fin_cases i
  · have h := realWeylCycle_nativeCircularBasis (5 : Fin 8)
    norm_num [nextColor]
    have h0 : nativeCircularBasis 5 = (ZornVectorMatrix.V 0 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 5) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 0
    have h1 : nativeCircularBasis 6 = (ZornVectorMatrix.V 1 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 6) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 1
    change nativeAut realWeylCycle (ZornVectorMatrix.V 0) = ZornVectorMatrix.V 1
    rw [← h0, ← h1]
    simpa [cycleFrameIndex]

  · have h := realWeylCycle_nativeCircularBasis (6 : Fin 8)
    norm_num [nextColor]
    have h1 : nativeCircularBasis 6 = (ZornVectorMatrix.V 1 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 6) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 1
    have h2 : nativeCircularBasis 7 = (ZornVectorMatrix.V 2 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 7) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 2
    change nativeAut realWeylCycle (ZornVectorMatrix.V 1) = ZornVectorMatrix.V 2
    rw [← h1, ← h2]
    simpa [cycleFrameIndex]
  · have h := realWeylCycle_nativeCircularBasis (7 : Fin 8)
    norm_num [nextColor]
    have h2 : nativeCircularBasis 7 = (ZornVectorMatrix.V 2 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 7) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 2
    have h0 : nativeCircularBasis 5 = (ZornVectorMatrix.V 0 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 5) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 0
    change nativeAut realWeylCycle (ZornVectorMatrix.V 2) = ZornVectorMatrix.V 0
    rw [← h2, ← h0]
    simpa [cycleFrameIndex]

noncomputable def cycleFrameIndexInv : Fin 8 → Fin 8 := Function.invFun cycleFrameIndex

theorem cycleFrameIndexInv_left (i : Fin 8) :
    cycleFrameIndexInv (cycleFrameIndex i) = i := by
  exact Function.leftInverse_invFun cycleFrameIndex_bijective.1 i

theorem cycleFrameIndexInv_right (i : Fin 8) :
    cycleFrameIndex (cycleFrameIndexInv i) = i := by
  exact Function.rightInverse_invFun cycleFrameIndex_bijective.2 i

theorem realWeylCycle_symm_nativeCircularBasis (i : Fin 8) :
    (nativeAut realWeylCycle).symm (nativeCircularBasis i) =
      nativeCircularBasis (cycleFrameIndexInv i) := by
  apply (nativeAut realWeylCycle).injective
  rw [LinearEquiv.apply_symm_apply]
  rw [realWeylCycle_nativeCircularBasis]
  rw [cycleFrameIndexInv_right]

theorem realWeylCycle_symm_E22 :
    (nativeAut realWeylCycle).symm (ZornVectorMatrix.E22 : ZornVectorMatrix ℝ) =
      ZornVectorMatrix.E22 := by
  apply (nativeAut realWeylCycle).injective
  rw [LinearEquiv.apply_symm_apply, realWeylCycle_E22]

theorem realWeylCycle_symm_U (i : Fin 3) :
    (nativeAut realWeylCycle).symm (ZornVectorMatrix.U i) =
      ZornVectorMatrix.U (if i = 0 then 2 else if i = 1 then 0 else 1) := by
  fin_cases i
  · apply (nativeAut realWeylCycle).injective
    rw [LinearEquiv.apply_symm_apply, realWeylCycle_U]
    norm_num [nextColor]
  · apply (nativeAut realWeylCycle).injective
    rw [LinearEquiv.apply_symm_apply, realWeylCycle_U]
    norm_num [nextColor]
  · apply (nativeAut realWeylCycle).injective
    rw [LinearEquiv.apply_symm_apply, realWeylCycle_U]
    norm_num [nextColor]
    congr 1

theorem realWeylCycle_symm_V (i : Fin 3) :
    (nativeAut realWeylCycle).symm (ZornVectorMatrix.V i) =
      ZornVectorMatrix.V (if i = 0 then 2 else if i = 1 then 0 else 1) := by
  fin_cases i
  · apply (nativeAut realWeylCycle).injective
    rw [LinearEquiv.apply_symm_apply, realWeylCycle_V]
    norm_num [nextColor]
  · apply (nativeAut realWeylCycle).injective
    rw [LinearEquiv.apply_symm_apply, realWeylCycle_V]
    norm_num [nextColor]
  · apply (nativeAut realWeylCycle).injective
    rw [LinearEquiv.apply_symm_apply, realWeylCycle_V]
    norm_num [nextColor]
    congr 1

noncomputable def reflectionFrameIndexInv : Fin 8 → Fin 8 := Function.invFun reflectionFrameIndex

theorem reflectionFrameIndexInv_left (i : Fin 8) :
    reflectionFrameIndexInv (reflectionFrameIndex i) = i := by
  exact Function.leftInverse_invFun reflectionFrameIndex_bijective.1 i

theorem reflectionFrameIndexInv_right (i : Fin 8) :
    reflectionFrameIndex (reflectionFrameIndexInv i) = i := by
  exact Function.rightInverse_invFun reflectionFrameIndex_bijective.2 i

theorem realWeylReflection_symm_nativeCircularBasis (i : Fin 8) :
    (nativeAut realWeylReflection).symm (nativeCircularBasis i) =
      nativeCircularBasis (reflectionFrameIndexInv i) := by
  apply (nativeAut realWeylReflection).injective
  rw [LinearEquiv.apply_symm_apply]
  rw [realWeylReflection_nativeCircularBasis]
  rw [reflectionFrameIndexInv_right]

/- theorem realWeylReflection_symm_U (i : Fin 3) :
    (nativeAut realWeylReflection).symm (ZornVectorMatrix.U i) =
      ZornVectorMatrix.V (if i = 0 then 0 else if i = 1 then 2 else 1) := by
  fin_cases i
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_V]
    norm_num
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_V]
    norm_num
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_V]
    norm_num

theorem realWeylReflection_symm_V (i : Fin 3) :
    (nativeAut realWeylReflection).symm (ZornVectorMatrix.V i) =
      ZornVectorMatrix.U (if i = 0 then 0 else if i = 1 then 2 else 1) := by
  fin_cases i
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_U]
    norm_num
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_U]
    norm_num
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_U]
    norm_num
 -/

theorem realWeylReflection_E22 :
    nativeAut realWeylReflection (ZornVectorMatrix.E22 : ZornVectorMatrix ℝ) =
      ZornVectorMatrix.E11 := by
  have hE : nativeCircularBasis (4 : Fin 8) =
      (ZornVectorMatrix.E22 : ZornVectorMatrix ℝ) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 4) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_scalarMinus_nativeE22
  have h11 : nativeCircularBasis (0 : Fin 8) =
      (ZornVectorMatrix.E11 : ZornVectorMatrix ℝ) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 0) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_scalarPlus_nativeE11
  have h := realWeylReflection_nativeCircularBasis (4 : Fin 8)
  rw [← hE, ← h11]
  simpa [reflectionFrameIndex] using h

theorem realWeylReflection_U (i : Fin 3) :
    nativeAut realWeylReflection (ZornVectorMatrix.U i) =
      ZornVectorMatrix.V (if i = 0 then 0 else if i = 1 then 2 else 1) := by
  fin_cases i
  · have h := realWeylReflection_nativeCircularBasis (1 : Fin 8)
    norm_num [nextColor]
    have hu : nativeCircularBasis 1 = (ZornVectorMatrix.U 0 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 1) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 0
    have hv : nativeCircularBasis 5 = (ZornVectorMatrix.V 0 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 5) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 0
    change nativeAut realWeylReflection (ZornVectorMatrix.U 0) = ZornVectorMatrix.V 0
    rw [← hu, ← hv]
    simpa [reflectionFrameIndex] using h
  · have h := realWeylReflection_nativeCircularBasis (2 : Fin 8)
    norm_num [nextColor]
    have hu : nativeCircularBasis 2 = (ZornVectorMatrix.U 1 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 2) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 1
    have hv : nativeCircularBasis 7 = (ZornVectorMatrix.V 2 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 7) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 2
    change nativeAut realWeylReflection (ZornVectorMatrix.U 1) = ZornVectorMatrix.V 2
    rw [← hu, ← hv]
    simpa [reflectionFrameIndex] using h
  · have h := realWeylReflection_nativeCircularBasis (3 : Fin 8)
    norm_num [nextColor]
    have hu : nativeCircularBasis 3 = (ZornVectorMatrix.U 2 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 3) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 2
    have hv : nativeCircularBasis 6 = (ZornVectorMatrix.V 1 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 6) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 1
    change nativeAut realWeylReflection (ZornVectorMatrix.U 2) = ZornVectorMatrix.V 1
    rw [← hu, ← hv]
    simpa [reflectionFrameIndex] using h

theorem realWeylReflection_V (i : Fin 3) :
    nativeAut realWeylReflection (ZornVectorMatrix.V i) =
      ZornVectorMatrix.U (if i = 0 then 0 else if i = 1 then 2 else 1) := by
  fin_cases i
  · have h := realWeylReflection_nativeCircularBasis (5 : Fin 8)
    norm_num [nextColor]
    have hv : nativeCircularBasis 5 = (ZornVectorMatrix.V 0 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 5) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 0
    have hu : nativeCircularBasis 1 = (ZornVectorMatrix.U 0 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 1) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 0
    change nativeAut realWeylReflection (ZornVectorMatrix.V 0) = ZornVectorMatrix.U 0
    rw [← hv, ← hu]
    simpa [reflectionFrameIndex] using h
  · have h := realWeylReflection_nativeCircularBasis (6 : Fin 8)
    norm_num [nextColor]
    have hv : nativeCircularBasis 6 = (ZornVectorMatrix.V 1 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 6) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 1
    have hu : nativeCircularBasis 3 = (ZornVectorMatrix.U 2 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 3) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 2
    change nativeAut realWeylReflection (ZornVectorMatrix.V 1) = ZornVectorMatrix.U 2
    rw [← hv, ← hu]
    simpa [reflectionFrameIndex] using h
  · have h := realWeylReflection_nativeCircularBasis (7 : Fin 8)
    norm_num [nextColor]
    have hv : nativeCircularBasis 7 = (ZornVectorMatrix.V 2 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 7) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootMinus_nativeV 2
    have hu : nativeCircularBasis 2 = (ZornVectorMatrix.U 1 : ZornVectorMatrix ℝ) := by
      change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 2) = _
      rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
      exact circular_rootPlus_nativeU 1
    change nativeAut realWeylReflection (ZornVectorMatrix.V 2) = ZornVectorMatrix.U 1
    rw [← hv, ← hu]
    simpa [reflectionFrameIndex] using h

theorem realWeylReflection_symm_U (i : Fin 3) :
    (nativeAut realWeylReflection).symm (ZornVectorMatrix.U i) =
      ZornVectorMatrix.V (if i = 0 then 0 else if i = 1 then 2 else 1) := by
  fin_cases i
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_V]
    norm_num <;> simp
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_V]
    norm_num <;> simp
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_V]
    norm_num <;> simp

theorem realWeylReflection_symm_V (i : Fin 3) :
    (nativeAut realWeylReflection).symm (ZornVectorMatrix.V i) =
      ZornVectorMatrix.U (if i = 0 then 0 else if i = 1 then 2 else 1) := by
  fin_cases i
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_U]
    norm_num <;> simp
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_U]
    norm_num <;> simp
  · apply (nativeAut realWeylReflection).injective
    rw [LinearEquiv.apply_symm_apply, realWeylReflection_U]
    norm_num <;> simp

theorem realWeylCycle_U0V0_parameter_readback :
    derivationParameters
      (conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0)))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 (-2) +
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 := by
  rw [conjugateNative_innerDerivation]
  simp only [canonicalU, canonicalV, canonicalVectorEquiv.apply_symm_apply]
  rw [realWeylCycle_U, realWeylCycle_V]
  simp only [nextColor]
  change derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 1))) = _
  rw [← InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization.canonicalToVector_standard_U1_V1]
  change InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)) = _
  rw [standardColumn_U1_V1]

private theorem standardColumn_U2_V2_readback :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 +
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 (-2) := by
  funext i
  by_cases h6 : i = 6 <;> by_cases h13 : i = 13 <;>
    simp [InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVec3.basis, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv,
      h6, h13] <;>
    fin_cases i <;> simp_all

theorem realWeylCycle_U1V1_parameter_readback :
    derivationParameters
      (conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1)))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 +
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 (-2) := by
  rw [conjugateNative_innerDerivation]
  simp only [canonicalU, canonicalV, canonicalVectorEquiv.apply_symm_apply]
  rw [realWeylCycle_U, realWeylCycle_V]
  simp only [nextColor]
  change derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2))) = _
  have hi : NativeStanDerivationBilinear.innerDerivation
      (canonicalVectorEquiv (canonicalU 2))
      (canonicalVectorEquiv (canonicalV 2)) =
      canonicalToVectorDerivation
        (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)) := by
    apply vectorCanonicalLinearEquiv.injective
    change vectorCanonicalLinearEquiv
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 2))
          (canonicalVectorEquiv (canonicalV 2))) =
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)
    simpa only [canonicalVectorEquiv.apply_symm_apply] using
      (vector_inner_to_canonical
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2)))
  rw [hi]
  change InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)) = _
  rw [standardColumn_U2_V2_readback]

theorem realWeylCycle_U1V1_derivation_readback :
    conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1))) =
      parameterDerivation
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 +
          InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 (-2)) := by
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1)))) = _
  rw [realWeylCycle_U1V1_parameter_readback]
  simpa [parameterLinearEquiv] using
    (parameterLinearEquiv.left_inv
      (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 +
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 (-2))).symm

theorem realWeylCycle_U0V0_parameter_support
    (i : Fin 14) (hi6 : i ≠ 6) (hi13 : i ≠ 13) :
    derivationParameters
        (conjugateNativeDerivation realWeylCycle
          (NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 0))
            (canonicalVectorEquiv (canonicalV 0)))) i = 0 := by
  rw [realWeylCycle_U0V0_parameter_readback]
  simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
    hi6, hi13]

theorem realWeylCycle_U1V1_parameter_support
    (i : Fin 14) (hi6 : i ≠ 6) (hi13 : i ≠ 13) :
    derivationParameters
        (conjugateNativeDerivation realWeylCycle
          (NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 1))
            (canonicalVectorEquiv (canonicalV 1)))) i = 0 := by
  rw [realWeylCycle_U1V1_parameter_readback]
  simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
    hi6, hi13]


theorem realWeylReflection_U0V0_pair_readback :
    conjugateNativeDerivation realWeylReflection
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0))) =
      NativeStanDerivationBilinear.innerDerivation
        (ZornVectorMatrix.V 0) (ZornVectorMatrix.U 0) := by
  rw [conjugateNative_innerDerivation]
  simp only [canonicalU, canonicalV, canonicalVectorEquiv.apply_symm_apply]
  rw [realWeylReflection_U, realWeylReflection_V]
  norm_num

theorem realWeylReflection_U1V1_pair_readback :
    conjugateNativeDerivation realWeylReflection
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1))) =
      NativeStanDerivationBilinear.innerDerivation
        (ZornVectorMatrix.V 2) (ZornVectorMatrix.U 2) := by
  rw [conjugateNative_innerDerivation]
  simp only [canonicalU, canonicalV, canonicalVectorEquiv.apply_symm_apply]
  rw [realWeylReflection_U, realWeylReflection_V]
  norm_num

theorem realWeylReflection_U0V0_parameter_transport :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (ZornVectorMatrix.V 0) (ZornVectorMatrix.U 0)) =
      InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (canonicalStandardDerivationOfCanonical (canonicalV 0) (canonicalU 0)) := by
  change derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalV 0))
        (canonicalVectorEquiv (canonicalU 0))) = _
  rw [← InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization.canonicalToVector_standard_V0_U0]
  rfl

theorem realWeylReflection_U1V1_parameter_transport :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (ZornVectorMatrix.V 2) (ZornVectorMatrix.U 2)) =
      InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (canonicalStandardDerivationOfCanonical (canonicalV 2) (canonicalU 2)) := by
  change derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalV 2))
        (canonicalVectorEquiv (canonicalU 2))) = _
  rw [← InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization.canonicalToVector_standard_V2_U2]
  rfl

/-
theorem V2U2_parameter_readback :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalV 2))
          (canonicalVectorEquiv (canonicalU 2))) =
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  rw [← InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization.canonicalToVector_standard_V2_U2]
  change InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalV 2) (canonicalU 2)) = _
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters,
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem realWeylReflection_U1V1_parameter_readback :
    derivationParameters
        (conjugateNativeDerivation realWeylReflection
          (NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 1))
            (canonicalVectorEquiv (canonicalV 1)))) =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 -
        (2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  rw [realWeylReflection_U1V1_pair_readback]
  exact V2U2_parameter_readback
 -/

/- theorem cartanParameterPlane_le_cartanPairParameterSpan :
    cartanParameterPlane ≤ cartanPairParameterSpan := by
  apply Submodule.span_le.2
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · let p₀ :=
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
    let p₁ :=
      (-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
    have hp₀ : p₀ ∈ cartanPairParameterSpan := Submodule.subset_span (by simp [p₀, cartanPairParameterSpan])
    have hp₁ : p₁ ∈ cartanPairParameterSpan := Submodule.subset_span (by simp [p₁, cartanPairParameterSpan])
    have h : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 =
        (1 / 3 : ℝ) • (p₀ - p₁) := by
      funext i
      fin_cases i <;>
        simp [p₀, p₁, InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
        norm_num
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hp₀ hp₁)
  · let p₀ :=
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
    let p₁ :=
      (-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
    have hp₀ : p₀ ∈ cartanPairParameterSpan := Submodule.subset_span (by simp [p₀, cartanPairParameterSpan])
    have hp₁ : p₁ ∈ cartanPairParameterSpan := Submodule.subset_span (by simp [p₁, cartanPairParameterSpan])
    have h : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 =
        (1 / 3 : ℝ) • ((2 : ℝ) • p₀ + p₁) := by
      funext i
      fin_cases i <;>
        simp [p₀, p₁, InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
        norm_num
    rw [h]
    exact Submodule.smul_mem _ _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ hp₀) hp₁)

theorem cartanPairParameterSpan_eq_cartanParameterPlane :
    cartanPairParameterSpan = cartanParameterPlane := by
  exact le_antisymm cartanPairParameterSpan_le_cartanParameterPlane
    cartanParameterPlane_le_cartanPairParameterSpan -/

theorem V0U0_parameter_readback :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalV 0))
          (canonicalVectorEquiv (canonicalU 0))) =
      - (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) := by
  rw [← InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization.canonicalToVector_standard_V0_U0]
  change InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalV 0) (canonicalU 0)) = _
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
      derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVec3.basis, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem realWeylReflection_U0V0_parameter_readback :
    derivationParameters
        (conjugateNativeDerivation realWeylReflection
          (NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 0))
            (canonicalVectorEquiv (canonicalV 0)))) =
      - (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) := by
  rw [realWeylReflection_U0V0_pair_readback,
    realWeylReflection_U0V0_parameter_transport]
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
      derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVec3.basis, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv]

theorem U0V0_parameter_readback :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0))) =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  rw [← InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization.canonicalToVector_standard_U0_V0]
  change InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)) = _
  rw [standardColumn_U0_V0]
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem realWeylCycle_U0V0_derivation_readback :
    conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0))) =
      parameterDerivation
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 (-2) +
          InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13) := by
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0)))) =
    derivationParameters
      (parameterDerivation
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 (-2) +
          InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13))
  rw [realWeylCycle_U0V0_parameter_readback]
  funext i
  fin_cases i <;>
    simp [derivationParameters, parameterDerivation, parameterAction,
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      canonicalU, canonicalV, ZornVectorMatrix.E22, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation]

private theorem standardColumn_V0_U0_support
    (i : Fin 14) (hi6 : i ≠ 6) (hi13 : i ≠ 13) :
    (InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalV 0) (canonicalU 0))) i = 0 := by
  fin_cases i <;>
    simp_all [InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv,
    InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv,
    canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
    derivationParameters, vectorCanonicalLinearEquiv,
    canonicalToVectorDerivation, canonicalU, canonicalV,
    ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
    ZornVec3.basis, InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, canonicalVectorEquiv,
      ]

private theorem standardColumn_V2_U2_support
    (i : Fin 14) (hi6 : i ≠ 6) (hi13 : i ≠ 13) :
    (InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalV 2) (canonicalU 2))) i = 0 := by
  fin_cases i <;>
    simp_all [InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv,
      canonicalStandardDerivationOfCanonical, directCanonicalStanDerMap_apply,
      derivationParameters, vectorCanonicalLinearEquiv,
      canonicalToVectorDerivation, canonicalU, canonicalV,
      ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVec3.basis, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]

def cartanParameterPlane : Submodule ℝ Params :=
  Submodule.span ℝ ({
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6,
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 } : Set Params)

def cartanPairParameterSpan : Submodule ℝ Params :=
  Submodule.span ℝ ({
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13,
    (-2 : ℝ) •
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 } : Set Params)

theorem cartanPairParameterSpan_le_cartanParameterPlane :
    cartanPairParameterSpan ≤ cartanParameterPlane := by
  apply Submodule.span_le.2
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · apply Submodule.add_mem
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)

/- theorem cartanParameterPlane_le_cartanPairParameterSpan :
    cartanParameterPlane ≤ cartanPairParameterSpan := by
  apply Submodule.span_le.2
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · let p₀ :=
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
    let p₁ :=
      (-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
    have hp₀ : p₀ ∈ cartanPairParameterSpan := Submodule.subset_span (by
      simp [p₀, cartanPairParameterSpan])
    have hp₁ : p₁ ∈ cartanPairParameterSpan := Submodule.subset_span (by
      simp [p₁, cartanPairParameterSpan])
    have h :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 =
          (1 / 3 : ℝ) • (p₀ - p₁) := by
      funext i
      fin_cases i <;>
        simp [p₀, p₁,
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
        try ring
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hp₀ hp₁)
  · let p₀ :=
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
    let p₁ :=
      (-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
    have hp₀ : p₀ ∈ cartanPairParameterSpan := Submodule.subset_span (by
      simp [p₀, cartanPairParameterSpan])
    have hp₁ : p₁ ∈ cartanPairParameterSpan := Submodule.subset_span (by
      simp [p₁, cartanPairParameterSpan])
    have h :
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 =
          (1 / 3 : ℝ) • ((2 : ℝ) • p₀ + p₁) := by
      funext i
      fin_cases i <;>
        simp [p₀, p₁,
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
        norm_num
    rw [h]
    exact Submodule.smul_mem _ (1 / 3 : ℝ)
      (Submodule.add_mem _ (Submodule.smul_mem _ (2 : ℝ) hp₀) hp₁)

theorem cartanPairParameterSpan_eq_cartanParameterPlane :
    cartanPairParameterSpan = cartanParameterPlane := by
  exact le_antisymm cartanPairParameterSpan_le_cartanParameterPlane
    cartanParameterPlane_le_cartanPairParameterSpan

 -/

theorem cartanParameterPlane_eq_cartanPairParameterSpan :
    cartanParameterPlane = cartanPairParameterSpan := by
  apply le_antisymm
  · apply Submodule.span_le.2
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · let p₀ :=
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
      let p₁ :=
        (-2 : ℝ) •
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
      have hp₀ : p₀ ∈ cartanPairParameterSpan := Submodule.subset_span (by
        simp [p₀, cartanPairParameterSpan])
      have hp₁ : p₁ ∈ cartanPairParameterSpan := Submodule.subset_span (by
        simp [p₁, cartanPairParameterSpan])
      have h :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 =
            (1 / 3 : ℝ) • (p₀ - p₁) := by
        funext i
        fin_cases i <;>
          simp [p₀, p₁,
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
          norm_num
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hp₀ hp₁)
    · let p₀ :=
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
      let p₁ :=
        (-2 : ℝ) •
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
      have hp₀ : p₀ ∈ cartanPairParameterSpan := Submodule.subset_span (by
        simp [p₀, cartanPairParameterSpan])
      have hp₁ : p₁ ∈ cartanPairParameterSpan := Submodule.subset_span (by
        simp [p₁, cartanPairParameterSpan])
      have h :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 =
            (1 / 3 : ℝ) • ((2 : ℝ) • p₀ + p₁) := by
        funext i
        fin_cases i <;>
          simp [p₀, p₁,
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
          norm_num
      rw [h]
      exact Submodule.smul_mem _ _
        (Submodule.add_mem _ (Submodule.smul_mem _ _ hp₀) hp₁)
  · exact cartanPairParameterSpan_le_cartanParameterPlane

theorem realWeylReflection_cartanPair_zero_mem_cartanParameterPlane :
    derivationParameters
        (conjugateNativeDerivation realWeylReflection
          (NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 0))
            (canonicalVectorEquiv (canonicalV 0)))) ∈
      cartanParameterPlane := by
  rw [realWeylReflection_U0V0_pair_readback,
    realWeylReflection_U0V0_parameter_transport]
  let p :=
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalV 0) (canonicalU 0))
  have hp : p = p 6 •
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      p 13 •
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
    funext i
    by_cases h6 : i = 6
    · subst i
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
    by_cases h13 : i = 13
    · subst i
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
    · have hz := standardColumn_V0_U0_support i h6 h13
      simpa [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
        h6, h13] using hz
  change p ∈ cartanParameterPlane
  rw [hp]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
theorem realWeylReflection_cartanPair_one_mem_cartanParameterPlane :
    derivationParameters
        (conjugateNativeDerivation realWeylReflection
          (NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 1))
            (canonicalVectorEquiv (canonicalV 1)))) ∈
      cartanParameterPlane := by
  rw [realWeylReflection_U1V1_pair_readback,
    realWeylReflection_U1V1_parameter_transport]
  let p :=
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalV 2) (canonicalU 2))
  have hp : p = p 6 •
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      p 13 •
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
    funext i
    by_cases h6 : i = 6
    · subst i
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
    by_cases h13 : i = 13
    · subst i
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
    · have hz := standardColumn_V2_U2_support i h6 h13
      simpa [p, InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
        h6, h13] using hz
  change p ∈ cartanParameterPlane
  rw [hp]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem realWeylCycle_cartanPair_one_mem_cartanParameterPlane :
    derivationParameters
      (conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1)))) ∈
      cartanParameterPlane := by
  rw [realWeylCycle_U1V1_parameter_readback]
  have h6 : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 ∈
      cartanParameterPlane := by
    apply Submodule.subset_span
    simp
  have h13 : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 ∈
      cartanParameterPlane := by
    apply Submodule.subset_span
    simp
  have hs6 : InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 := by
    rfl
  have hs13 : InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 (-2) =
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
    funext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
  rw [hs6, hs13]
  apply Submodule.add_mem
  · exact h6
  · exact Submodule.smul_mem cartanParameterPlane (-2 : ℝ) h13

theorem realWeylCycle_cartanPair_zero_mem_cartanParameterPlane :
    derivationParameters
      (conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0)))) ∈
      cartanParameterPlane := by
  rw [realWeylCycle_U0V0_parameter_readback]
  have h6 : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 ∈
      cartanParameterPlane := by
    apply Submodule.subset_span
    simp
  have h13 : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 ∈
      cartanParameterPlane := by
    apply Submodule.subset_span
    simp
  have hs6 : InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 (-2) =
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 := by
    funext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
  have hs13 : InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
    rfl
  rw [hs6, hs13]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ h6
  · exact h13

noncomputable def conjugatedParameterLinearMap
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) : Params →ₗ[ℝ] Params :=
  InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm.toLinearMap.comp
    ((conjugateNativeDerivationLinear φ).comp
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.toLinearMap)

@[simp] theorem conjugatedParameterLinearMap_apply
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (p : Params) :
    conjugatedParameterLinearMap φ p =
      derivationParameters
        (conjugateNativeDerivation φ
          (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation p)) := by
  rfl

theorem U1V1_parameter_readback :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1))) =
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  rw [← InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization.canonicalToVector_standard_U1_V1]
  change InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)) = _
  rw [standardColumn_U1_V1]
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem conjugatedParameterLinearMap_cycle_U0V0_mem_cartanParameterPlane :
    conjugatedParameterLinearMap realWeylCycle
      (derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0)))) ∈
      cartanParameterPlane := by
  rw [conjugatedParameterLinearMap_apply]
  have hp :
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation
          (derivationParameters
            (NativeStanDerivationBilinear.innerDerivation
              (canonicalVectorEquiv (canonicalU 0))
              (canonicalVectorEquiv (canonicalV 0)))) =
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0)) := by
    change InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv
        (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm _ ) = _
    exact InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.apply_symm_apply _
  rw [hp]
  exact realWeylCycle_cartanPair_zero_mem_cartanParameterPlane

theorem conjugatedParameterLinearMap_cycle_U1V1_mem_cartanParameterPlane :
    conjugatedParameterLinearMap realWeylCycle
      (derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1)))) ∈
      cartanParameterPlane := by
  rw [conjugatedParameterLinearMap_apply]
  have hp :
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation
          (derivationParameters
            (NativeStanDerivationBilinear.innerDerivation
              (canonicalVectorEquiv (canonicalU 1))
              (canonicalVectorEquiv (canonicalV 1)))) =
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1)) := by
    change InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv
        (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm _) = _
    exact InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.apply_symm_apply _
  rw [hp]
  exact realWeylCycle_cartanPair_one_mem_cartanParameterPlane

def canonicalCartanParameterPlane :
    Submodule ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  canonicalParameterSubmodule cartanParameterPlane

theorem parameterDerivation_derivationParameters
    (D : ZornVectorMatrix.Derivation (R := ℝ)) :
    parameterDerivation (derivationParameters D) = D := by
  change parameterLinearEquiv (parameterLinearEquiv.symm D) = D
  exact parameterLinearEquiv.apply_symm_apply D

theorem parameterDerivation_U0V0_readback :
    parameterDerivation
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 0))
        (canonicalVectorEquiv (canonicalV 0)) := by
  rw [← U0V0_parameter_readback]
  exact parameterDerivation_derivationParameters _

theorem parameterDerivation_U1V1_readback :
    parameterDerivation
        ((-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 1)) := by
  rw [← U1V1_parameter_readback]
  exact parameterDerivation_derivationParameters _

theorem realWeylCycle_canonicalCartan_U0V0_mem :
    conjugateCanonicalDerivation realWeylCycle
        (parameterCanonicalLieEquiv
          (derivationParameters
            (NativeStanDerivationBilinear.innerDerivation
              (canonicalVectorEquiv (canonicalU 0))
              (canonicalVectorEquiv (canonicalV 0))))) ∈
      canonicalCartanParameterPlane := by
  apply conjugateCanonicalDerivation_mem_canonicalParameterSubmodule
    realWeylCycle cartanParameterPlane _
  rw [parameterDerivation_derivationParameters]
  exact realWeylCycle_cartanPair_zero_mem_cartanParameterPlane

theorem realWeylCycle_canonicalCartan_U1V1_mem :
    conjugateCanonicalDerivation realWeylCycle
        (parameterCanonicalLieEquiv
          (derivationParameters
            (NativeStanDerivationBilinear.innerDerivation
              (canonicalVectorEquiv (canonicalU 1))
              (canonicalVectorEquiv (canonicalV 1))))) ∈
      canonicalCartanParameterPlane := by
  apply conjugateCanonicalDerivation_mem_canonicalParameterSubmodule
    realWeylCycle cartanParameterPlane _
  rw [parameterDerivation_derivationParameters]
  exact realWeylCycle_cartanPair_one_mem_cartanParameterPlane

theorem realWeylReflection_canonicalCartan_U0V0_mem :
    conjugateCanonicalDerivation realWeylReflection
        (parameterCanonicalLieEquiv
          (derivationParameters
            (NativeStanDerivationBilinear.innerDerivation
              (canonicalVectorEquiv (canonicalU 0))
              (canonicalVectorEquiv (canonicalV 0))))) ∈
      canonicalCartanParameterPlane := by
  apply conjugateCanonicalDerivation_mem_canonicalParameterSubmodule
    realWeylReflection cartanParameterPlane _
  rw [parameterDerivation_derivationParameters]
  exact realWeylReflection_cartanPair_zero_mem_cartanParameterPlane

theorem realWeylReflection_canonicalCartan_U1V1_mem :
    conjugateCanonicalDerivation realWeylReflection
        (parameterCanonicalLieEquiv
          (derivationParameters
            (NativeStanDerivationBilinear.innerDerivation
              (canonicalVectorEquiv (canonicalU 1))
              (canonicalVectorEquiv (canonicalV 1))))) ∈
      canonicalCartanParameterPlane := by
  apply conjugateCanonicalDerivation_mem_canonicalParameterSubmodule
    realWeylReflection cartanParameterPlane _
  rw [parameterDerivation_derivationParameters]
  exact realWeylReflection_cartanPair_one_mem_cartanParameterPlane

/-! Parameter readback for the next, representation-sensitive layer.  This
is intentionally stated for an arbitrary native automorphism: it records the
coordinates of a conjugated Cartan derivation without asserting that those
coordinates are supported on the Cartan indices. -/

noncomputable def conjugatedCartanParameters
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (j : Fin 2) : Params :=
  parameterLinearEquiv.symm
    (conjugateNativeDerivation φ (cartanDerivation j))

theorem conjugatedCartanParameters_readback
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (j : Fin 2) :
    conjugateNativeDerivation φ (cartanDerivation j) =
      parameterDerivation (conjugatedCartanParameters φ j) := by
  unfold conjugatedCartanParameters
  change _ = parameterLinearEquiv (parameterLinearEquiv.symm _)
  exact (parameterLinearEquiv.apply_symm_apply _).symm

theorem U0V0_innerDerivation_eq_cartanDerivation_add :
    NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 0))
        (canonicalVectorEquiv (canonicalV 0)) =
      cartanDerivation 0 + cartanDerivation 1 := by
  change _ = parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 6) +
      parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 13)
  rw [← map_add]
  rw [← parameterLinearEquiv.apply_symm_apply
    (NativeStanDerivationBilinear.innerDerivation
      (canonicalVectorEquiv (canonicalU 0))
      (canonicalVectorEquiv (canonicalV 0)))]
  rw [← canonicalToVector_standard_U0_V0]
  apply_fun parameterLinearEquiv.symm
  simp only [LinearEquiv.symm_apply_apply]
  change canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)) = _
  rw [standardColumn_U0_V0]
  simp [cartanDerivation, nativeParameterBasis, parameterLinearEquiv,
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
  · funext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
        Pi.basisFun]
  · exact parameterLinearEquiv.symm.injective

theorem U1V1_innerDerivation_eq_cartanDerivation_combination :
    NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 1)) =
      (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
  simp only [cartanDerivation, nativeParameterBasis]
  change _ = (-2 : ℝ) • parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 6) +
      parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 13)
  rw [← map_smul, ← map_add]
  rw [← parameterLinearEquiv.apply_symm_apply
    (NativeStanDerivationBilinear.innerDerivation
      (canonicalVectorEquiv (canonicalU 1))
      (canonicalVectorEquiv (canonicalV 1)))]
  rw [← canonicalToVector_standard_U1_V1]
  apply_fun parameterLinearEquiv.symm
  simp only [LinearEquiv.symm_apply_apply]
  change canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)) = _
  rw [standardColumn_U1_V1]
  simp [cartanDerivation, nativeParameterBasis, parameterLinearEquiv,
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
  · funext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
        Pi.basisFun]
  · exact parameterLinearEquiv.symm.injective

theorem realWeylCycle_U0V0_eq_U1V1 :
    conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0))) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 1)) := by
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0)))) =
    derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 1)))
  rw [realWeylCycle_U0V0_parameter_readback,
    U1V1_parameter_readback]
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem U2V2_parameter_readback_active :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 2))
          (canonicalVectorEquiv (canonicalV 2))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 +
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 (-2) := by
  have hi : NativeStanDerivationBilinear.innerDerivation
      (canonicalVectorEquiv (canonicalU 2))
      (canonicalVectorEquiv (canonicalV 2)) =
      canonicalToVectorDerivation
        (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)) := by
    apply vectorCanonicalLinearEquiv.injective
    change vectorCanonicalLinearEquiv
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 2))
          (canonicalVectorEquiv (canonicalV 2))) =
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)
    simpa only [canonicalVectorEquiv.apply_symm_apply] using
      (vector_inner_to_canonical
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2)))
  rw [hi]
  change InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)) = _
  exact standardColumn_U2_V2_readback

/-
theorem realWeylCycle_cartanPair_zero_readback :
    conjugateNativeDerivation realWeylCycle
        (cartanDerivation 0 + cartanDerivation 1) =
      (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
  rw [← U1V1_innerDerivation_eq_cartanDerivation_combination]
  rw [← U0V0_innerDerivation_eq_cartanDerivation_add]
  rw [realWeylCycle_U0V0_derivation_readback]
  apply parameterLinearEquiv.symm.injective
  change
    InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 (-2) +
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 =
      derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1)))
  rw [U1V1_parameter_readback]

-/

theorem splitParameterUnit_six_eq_canonical :
    InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 := by
  rfl

theorem splitParameterUnit_thirteen_eq_canonical_smul (r : ℝ) :
    InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 r =
      r • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem realWeylCycle_cartanPair_zero_verified :
    conjugateNativeDerivation realWeylCycle
        (cartanDerivation 0 + cartanDerivation 1) =
      (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
  rw [← U0V0_innerDerivation_eq_cartanDerivation_add]
  rw [realWeylCycle_U0V0_eq_U1V1]
  rw [U1V1_innerDerivation_eq_cartanDerivation_combination]

theorem U2V2_innerDerivation_eq_cartanDerivation_combination :
    NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2)) =
      cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1 := by
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2))) = _
  rw [U2V2_parameter_readback_active]
  simp only [map_add, map_neg, map_smul, parameterLinearEquiv.symm_apply_apply]
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterAction,
      ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVec3.basis, cartanDerivation, nativeParameterBasis, parameterLinearEquiv,
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem realWeylCycle_U1V1_eq_U2V2_active :
    conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1))) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2)) := by
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1)))) =
    derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2)))
  rw [realWeylCycle_U1V1_parameter_readback, U2V2_parameter_readback_active]

theorem realWeylCycle_cartanPair_one_verified :
    conjugateNativeDerivation realWeylCycle
        ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
      cartanDerivation 0 + (-2 : ℝ) • cartanDerivation 1 := by
  rw [← U1V1_innerDerivation_eq_cartanDerivation_combination]
  rw [realWeylCycle_U1V1_eq_U2V2_active]
  rw [U2V2_innerDerivation_eq_cartanDerivation_combination]

theorem realWeylReflection_cartanPair_zero_verified :
    conjugateNativeDerivation realWeylReflection
        (cartanDerivation 0 + cartanDerivation 1) =
      -(cartanDerivation 0 + cartanDerivation 1) := by
  rw [← U0V0_innerDerivation_eq_cartanDerivation_add]
  rw [realWeylReflection_U0V0_pair_readback]
  change
    NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalV 0))
        (canonicalVectorEquiv (canonicalU 0)) = _
  rw [NativeStanDerivationBilinear.innerDerivation_swap]

/-
theorem V2U2_parameter_readback_active :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalV 2))
          (canonicalVectorEquiv (canonicalU 2))) =
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  have hp := realWeylReflection_U1V1_parameter_readback_active
  rw [realWeylReflection_U1V1_pair_readback] at hp
  simpa using hp

theorem V2U2_innerDerivation_eq_cartanDerivation_combination :
    NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalV 2))
        (canonicalVectorEquiv (canonicalU 2)) =
      (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalV 2))
        (canonicalVectorEquiv (canonicalU 2))) = _
  rw [V2U2_parameter_readback_active]
  simp [InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters,
    InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation,
    InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterAction,
    ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
    ZornVec3.basis, cartanDerivation, nativeParameterBasis, parameterLinearEquiv,
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem realWeylReflection_cartanPair_one_verified :
    conjugateNativeDerivation realWeylReflection
        ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
      (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
  rw [← U1V1_innerDerivation_eq_cartanDerivation_combination]
  rw [realWeylReflection_U1V1_pair_readback]
  change NativeStanDerivationBilinear.innerDerivation
      (canonicalVectorEquiv (canonicalV 2))
      (canonicalVectorEquiv (canonicalU 2)) = _
  rw [V2U2_innerDerivation_eq_cartanDerivation_combination]

-/

/-
theorem realWeylReflection_cartanPair_zero_readback_verified :
    conjugateNativeDerivation realWeylReflection
        (cartanDerivation 0 + cartanDerivation 1) =
      -(cartanDerivation 0 + cartanDerivation 1) := by
  rw [← U0V0_innerDerivation_eq_cartanDerivation_add]
  conv_rhs =>
    rw [← U0V0_innerDerivation_eq_cartanDerivation_add]
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (conjugateNativeDerivation realWeylReflection
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0)))) = _
  rw [realWeylReflection_U0V0_parameter_readback]
  simp [InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters,
    InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation,
    InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterAction,
    ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
    ZornVec3.basis, cartanDerivation, nativeParameterBasis, parameterLinearEquiv,
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

-/

/-
theorem realWeylReflection_cartanPair_zero_verified :
    conjugateNativeDerivation realWeylReflection
        (cartanDerivation 0 + cartanDerivation 1) =
      -(cartanDerivation 0 + cartanDerivation 1) := by
  rw [← U0V0_innerDerivation_eq_cartanDerivation_add]
  rw [realWeylReflection_U0V0_pair_readback]
  rw [← U0V0_innerDerivation_eq_cartanDerivation_add]
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalV 0))
        (canonicalVectorEquiv (canonicalU 0))) = _
  rw [realWeylReflection_U0V0_parameter_transport]
  simp [cartanDerivation, nativeParameterBasis, parameterLinearEquiv,
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

-/

noncomputable def cycleCartanParameterAction_active :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.Params →ₗ[ℝ]
      InfoGeometry.Lie.CanonicalZornDerivationDimension.Params where
  toFun p :=
    (-p 6 - p 13) •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      p 6 •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
  map_add' p q := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
      ring
  map_smul' r p := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
      ring

theorem cycleCartanParameterAction_active_pair_zero :
    cycleCartanParameterAction_active
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      (-2 : ℝ) •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  ext i
  fin_cases i <;>
    simp [cycleCartanParameterAction_active,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
    norm_num

theorem cycleCartanParameterAction_active_pair_one :
    cycleCartanParameterAction_active
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        (-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  ext i
  fin_cases i <;>
    simp [cycleCartanParameterAction_active,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
    norm_num

noncomputable def conjugatedParameterLinearMap_active
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.Params →ₗ[ℝ]
      InfoGeometry.Lie.CanonicalZornDerivationDimension.Params :=
  InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm.toLinearMap.comp
    ((conjugateNativeDerivationLinear φ).comp
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.toLinearMap)

@[simp] theorem conjugatedParameterLinearMap_active_apply
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (p : InfoGeometry.Lie.CanonicalZornDerivationDimension.Params) :
    conjugatedParameterLinearMap_active φ p =
      derivationParameters
        (conjugateNativeDerivation φ (parameterDerivation p)) := by
  rfl

/-
theorem conjugatedParameterLinearMap_active_cycle_pair_zero :
    conjugatedParameterLinearMap_active realWeylCycle
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      cycleCartanParameterAction_active
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) := by
  rw [← U0V0_parameter_readback]
  rw [conjugatedParameterLinearMap_active_apply]
  rw [realWeylCycle_U0V0_derivation_readback]
  rw [U1V1_parameter_readback]
  funext i
  fin_cases i <;>
    simp [cycleCartanParameterAction_active,
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem conjugatedParameterLinearMap_active_cycle_pair_one :
    conjugatedParameterLinearMap_active realWeylCycle
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      cycleCartanParameterAction_active
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) := by
  rw [← U1V1_parameter_readback]
  rw [conjugatedParameterLinearMap_active_apply]
  rw [realWeylCycle_U1V1_eq_U2V2_active]
  rw [U2V2_parameter_readback_active]
  funext i
  fin_cases i <;>
    simp [cycleCartanParameterAction_active,
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem conjugatedParameterLinearMap_active_cycle_eq_on_cartanParameterPlane
    (p : InfoGeometry.Lie.CanonicalZornDerivationDimension.Params)
    (hp : p ∈ cartanParameterPlane) :
    conjugatedParameterLinearMap_active realWeylCycle p =
      cycleCartanParameterAction_active p := by
  rw [cartanParameterPlane_eq_cartanPairParameterSpan] at hp
  refine Submodule.span_induction
    (p := fun q _ =>
      conjugatedParameterLinearMap_active realWeylCycle q =
        cycleCartanParameterAction_active q) ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact conjugatedParameterLinearMap_active_cycle_pair_zero
    · exact conjugatedParameterLinearMap_active_cycle_pair_one
  · simp only [(conjugatedParameterLinearMap_active realWeylCycle).map_zero,
      cycleCartanParameterAction_active.map_zero]
  · intro p q _ _ hp hq
    simp only [(conjugatedParameterLinearMap_active realWeylCycle).map_add,
      cycleCartanParameterAction_active.map_add, hp, hq]
  · intro a p _ hp
    simp only [(conjugatedParameterLinearMap_active realWeylCycle).map_smul,
      cycleCartanParameterAction_active.map_smul, hp]

 -/







/-
The declarations below are exploratory Cartan-coordinate work.  They are kept
out of the owner until their carrier and scalar-support proofs are complete.
 -/

theorem realWeylCycle_U1V1_eq_U2V2_direct :
    conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1))) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2)) := by
  rw [conjugateNative_innerDerivation]
  simp only [canonicalVectorEquiv.apply_symm_apply]
  rw [realWeylCycle_U, realWeylCycle_V]
  simp [nextColor]

/-
theorem U2V2_parameter_readback :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 2))
          (canonicalVectorEquiv (canonicalV 2))) =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 (-2) := by
  have hi : NativeStanDerivationBilinear.innerDerivation
      (canonicalVectorEquiv (canonicalU 2))
      (canonicalVectorEquiv (canonicalV 2)) =
      canonicalToVectorDerivation
        (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)) := by
    apply vectorCanonicalLinearEquiv.injective
    change vectorCanonicalLinearEquiv
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 2))
          (canonicalVectorEquiv (canonicalV 2))) =
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)
    simpa only [canonicalVectorEquiv.apply_symm_apply] using
      (vector_inner_to_canonical
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2)))
  rw [hi]
  change InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)) = _
  rw [standardColumn_U2_V2_readback]

theorem V2U2_parameter_readback :
    derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalV 2))
          (canonicalVectorEquiv (canonicalU 2))) =
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  rw [← InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization.canonicalToVector_standard_V2_U2]
  change InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalV 2) (canonicalU 2)) = _
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv,
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
      canonicalU, canonicalV, ZornVectorMatrix.E22, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis]

theorem realWeylReflection_cartanPair_one_verified :
    conjugateNativeDerivation realWeylReflection
        ((-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1) =
      (-2 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
  rw [← U1V1_innerDerivation_eq_cartanDerivation_combination]
  rw [realWeylReflection_U1V1_pair_readback]
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (ZornVectorMatrix.V 2) (ZornVectorMatrix.U 2)) = _
  rw [V2U2_parameter_readback]
  simp [cartanDerivation, nativeParameterBasis, parameterLinearEquiv,
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem realWeylReflection_U1V1_parameter_readback_active :
    derivationParameters
        (conjugateNativeDerivation realWeylReflection
          (NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 1))
            (canonicalVectorEquiv (canonicalV 1)))) =
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  rw [realWeylReflection_U1V1_pair_readback]
  exact V2U2_parameter_readback

theorem realWeylCycle_U1V1_eq_U2V2 :
    conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1))) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2)) := by
  apply parameterLinearEquiv.symm.injective
  change derivationParameters
      (conjugateNativeDerivation realWeylCycle
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1)))) =
    derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 2)))
  rw [realWeylCycle_U1V1_parameter_readback, U2V2_parameter_readback]
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem conjugatedParameterLinearMap_cycle_pair_zero_to_one :
    conjugatedParameterLinearMap realWeylCycle
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 (-2) +
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 := by
  rw [← U0V0_parameter_readback]
  rw [conjugatedParameterLinearMap_apply]
  rw [realWeylCycle_U0V0_parameter_readback]
  rfl

theorem conjugatedParameterLinearMap_cycle_pair_one_to_two :
    conjugatedParameterLinearMap realWeylCycle
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 (-2) := by
  rw [← U1V1_parameter_readback]
  rw [conjugatedParameterLinearMap_apply]
  rw [realWeylCycle_U1V1_parameter_readback]
  rfl

noncomputable def cycleCartanParameterAction : Params →ₗ[ℝ] Params where
  toFun p :=
    (-p 6 - p 13) •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      p 6 •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
  map_add' p q := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
      ring
  map_smul' r p := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
      ring

@[simp] theorem cycleCartanParameterAction_apply_pair_zero :
    cycleCartanParameterAction
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  ext i
  fin_cases i <;>
    simp [cycleCartanParameterAction,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

@[simp] theorem cycleCartanParameterAction_apply_pair_one :
    cycleCartanParameterAction
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  ext i
  fin_cases i <;>
    simp [cycleCartanParameterAction,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem conjugatedParameterLinearMap_cycle_agrees_on_pair_zero :
    conjugatedParameterLinearMap realWeylCycle
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      cycleCartanParameterAction
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) := by
  rw [conjugatedParameterLinearMap_cycle_pair_zero_to_one,
    cycleCartanParameterAction_apply_pair_zero]
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem conjugatedParameterLinearMap_cycle_agrees_on_pair_one :
    conjugatedParameterLinearMap realWeylCycle
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      cycleCartanParameterAction
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) := by
  rw [conjugatedParameterLinearMap_cycle_pair_one_to_two,
    cycleCartanParameterAction_apply_pair_one]
  rfl

theorem conjugatedParameterLinearMap_cycle_eq_cycleCartanParameterAction_on_pair_span
    (p : Params) (hp : p ∈ cartanPairParameterSpan) :
    conjugatedParameterLinearMap realWeylCycle p =
      cycleCartanParameterAction p := by
  refine Submodule.span_induction
    (p := fun q _ => conjugatedParameterLinearMap realWeylCycle q =
      cycleCartanParameterAction q) ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact conjugatedParameterLinearMap_cycle_agrees_on_pair_zero
    · exact conjugatedParameterLinearMap_cycle_agrees_on_pair_one
  · simp only [(conjugatedParameterLinearMap realWeylCycle).map_zero,
      cycleCartanParameterAction.map_zero]
  · intro p q _ _ hp hq
    rw [(conjugatedParameterLinearMap realWeylCycle).map_add,
      cycleCartanParameterAction.map_add, hp, hq]
  · intro r p _ hp
    rw [(conjugatedParameterLinearMap realWeylCycle).map_smul,
      cycleCartanParameterAction.map_smul, hp]

theorem conjugatedParameterLinearMap_cycle_eq_cycleCartanParameterAction_on_cartanParameterPlane
    (p : Params) (hp : p ∈ cartanParameterPlane) :
    conjugatedParameterLinearMap realWeylCycle p =
      cycleCartanParameterAction p := by
  rw [← cartanParameterPlane_eq_cartanPairParameterSpan] at hp
  exact conjugatedParameterLinearMap_cycle_eq_cycleCartanParameterAction_on_pair_span p hp

theorem conjugatedParameterLieEquiv_cycle_eq_cycleCartanParameterAction_on_cartanParameterPlane
    (p : Params) (hp : p ∈ cartanParameterPlane) :
    conjugatedParameterLieEquiv realWeylCycle p =
      cycleCartanParameterAction p := by
  rw [conjugatedParameterLieEquiv_apply]
  exact conjugatedParameterLinearMap_cycle_eq_cycleCartanParameterAction_on_cartanParameterPlane
    p hp

noncomputable def reflectionCartanParameterAction : Params →ₗ[ℝ] Params where
  toFun p :=
    ((p 6 - 4 * p 13) / 3) •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      ((-2 * p 6 - p 13) / 3) •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13
  map_add' p q := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
      ring
  map_smul' r p := by
    ext i
    fin_cases i <;>
      simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit] <;>
      ring

@[simp] theorem reflectionCartanParameterAction_apply_pair_zero :
    reflectionCartanParameterAction
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      (-1 : ℝ) •
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) := by
  ext i
  fin_cases i <;>
    simp [reflectionCartanParameterAction,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

@[simp] theorem reflectionCartanParameterAction_apply_pair_one :
    reflectionCartanParameterAction
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      (-2 : ℝ) • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  ext i
  fin_cases i <;>
    simp [reflectionCartanParameterAction,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

@[simp] theorem conjugatedParameterLinearMap_add
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (p q : Params) :
    conjugatedParameterLinearMap φ (p + q) =
      conjugatedParameterLinearMap φ p + conjugatedParameterLinearMap φ q := by
  exact (conjugatedParameterLinearMap φ).map_add p q

@[simp] theorem conjugatedParameterLinearMap_smul
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (r : ℝ) (p : Params) :
    conjugatedParameterLinearMap φ (r • p) =
      r • conjugatedParameterLinearMap φ p := by
  exact (conjugatedParameterLinearMap φ).map_smul r p

theorem conjugatedParameterLinearMap_cycle_maps_cartanParameterPlane
    (p : Params) (hp : p ∈ cartanParameterPlane) :
    conjugatedParameterLinearMap realWeylCycle p ∈ cartanParameterPlane := by
  rw [cartanParameterPlane_eq_cartanPairParameterSpan] at hp
  refine Submodule.span_induction
    (p := fun q _ => conjugatedParameterLinearMap realWeylCycle q ∈
      cartanParameterPlane) ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · rw [← U0V0_parameter_readback]
      exact conjugatedParameterLinearMap_cycle_U0V0_mem_cartanParameterPlane
    · rw [← U1V1_parameter_readback]
      exact conjugatedParameterLinearMap_cycle_U1V1_mem_cartanParameterPlane
  · change conjugatedParameterLinearMap realWeylCycle 0 ∈ cartanParameterPlane
    rw [(conjugatedParameterLinearMap realWeylCycle).map_zero]
    exact cartanParameterPlane.zero_mem
  · intro p q _ _ hp hq
    rw [(conjugatedParameterLinearMap realWeylCycle).map_add]
    exact cartanParameterPlane.add_mem hp hq
  · intro r p _ hp
    rw [(conjugatedParameterLinearMap realWeylCycle).map_smul]
    exact cartanParameterPlane.smul_mem r hp

theorem conjugatedParameterLinearMap_reflection_U0V0_mem_cartanParameterPlane :
    conjugatedParameterLinearMap realWeylReflection
      (derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 0)))) ∈ cartanParameterPlane := by
  rw [conjugatedParameterLinearMap_apply]
  change parameterLinearEquiv.symm
      (conjugateNativeDerivation realWeylReflection
        (parameterLinearEquiv (parameterLinearEquiv.symm _))) ∈ _
  rw [parameterLinearEquiv.apply_symm_apply]
  exact realWeylReflection_cartanPair_zero_mem_cartanParameterPlane

theorem conjugatedParameterLinearMap_reflection_U1V1_mem_cartanParameterPlane :
    conjugatedParameterLinearMap realWeylReflection
      (derivationParameters
        (NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 1)))) ∈ cartanParameterPlane := by
  rw [conjugatedParameterLinearMap_apply]
  change parameterLinearEquiv.symm
      (conjugateNativeDerivation realWeylReflection
        (parameterLinearEquiv (parameterLinearEquiv.symm _))) ∈ _
  rw [parameterLinearEquiv.apply_symm_apply]
  exact realWeylReflection_cartanPair_one_mem_cartanParameterPlane

theorem conjugatedParameterLinearMap_reflection_maps_cartanParameterPlane
    (p : Params) (hp : p ∈ cartanParameterPlane) :
    conjugatedParameterLinearMap realWeylReflection p ∈ cartanParameterPlane := by
  rw [cartanParameterPlane_eq_cartanPairParameterSpan] at hp
  refine Submodule.span_induction
    (p := fun q _ => conjugatedParameterLinearMap realWeylReflection q ∈ cartanParameterPlane) ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · rw [← U0V0_parameter_readback]
      exact conjugatedParameterLinearMap_reflection_U0V0_mem_cartanParameterPlane
    · rw [← U1V1_parameter_readback]
      exact conjugatedParameterLinearMap_reflection_U1V1_mem_cartanParameterPlane
  · change conjugatedParameterLinearMap realWeylReflection 0 ∈ cartanParameterPlane
    rw [(conjugatedParameterLinearMap realWeylReflection).map_zero]
    exact cartanParameterPlane.zero_mem
  · intro p q _ _ hp hq
    rw [(conjugatedParameterLinearMap realWeylReflection).map_add]
    exact cartanParameterPlane.add_mem hp hq
  · intro r p _ hp
    rw [(conjugatedParameterLinearMap realWeylReflection).map_smul]
    exact cartanParameterPlane.smul_mem r hp

theorem conjugatedParameterLinearMap_reflection_pair_zero_eq_action :
    conjugatedParameterLinearMap realWeylReflection
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      reflectionCartanParameterAction
        (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) := by
  rw [← U0V0_parameter_readback]
  rw [conjugatedParameterLinearMap_apply, parameterDerivation_derivationParameters]
  rw [realWeylReflection_U0V0_parameter_readback]
  exact reflectionCartanParameterAction_apply_pair_zero.symm

theorem conjugatedParameterLinearMap_reflection_pair_one_eq_action :
    conjugatedParameterLinearMap realWeylReflection
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) =
      reflectionCartanParameterAction
        ((-2 : ℝ) •
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13) := by
  rw [← U1V1_parameter_readback]
  rw [conjugatedParameterLinearMap_apply, parameterDerivation_derivationParameters]
  rw [realWeylReflection_U1V1_parameter_readback]
  exact reflectionCartanParameterAction_apply_pair_one.symm

theorem conjugatedParameterLinearMap_reflection_eq_on_cartanParameterPlane
    (p : Params) (hp : p ∈ cartanParameterPlane) :
    conjugatedParameterLinearMap realWeylReflection p =
      reflectionCartanParameterAction p := by
  rw [← cartanPairParameterSpan_eq_cartanParameterPlane] at hp
  refine Submodule.span_induction
    (p := fun q _ => conjugatedParameterLinearMap realWeylReflection q =
      reflectionCartanParameterAction q) ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact conjugatedParameterLinearMap_reflection_pair_zero_eq_action
    · exact conjugatedParameterLinearMap_reflection_pair_one_eq_action
  · simp only [(conjugatedParameterLinearMap realWeylReflection).map_zero,
      reflectionCartanParameterAction.map_zero]
  · intro p q _ _ hp hq
    simp only [(conjugatedParameterLinearMap realWeylReflection).map_add,
      reflectionCartanParameterAction.map_add, hp, hq]
  · intro a p _ hp
    simp only [(conjugatedParameterLinearMap realWeylReflection).map_smul,
      reflectionCartanParameterAction.map_smul, hp]

theorem conjugatedParameterLieEquiv_reflection_eq_reflectionCartanParameterAction_on_cartanParameterPlane
    (p : Params) (hp : p ∈ cartanParameterPlane) :
    conjugatedParameterLieEquiv realWeylReflection p =
      reflectionCartanParameterAction p := by
  rw [conjugatedParameterLieEquiv_apply]
  exact conjugatedParameterLinearMap_reflection_eq_on_cartanParameterPlane p hp

noncomputable def cartanParameterRestriction
    (L : Params ≃ₗ[ℝ] Params)
    (hL : cartanParameterPlane.map L.toLinearMap = cartanParameterPlane) :
    cartanParameterPlane ≃ₗ[ℝ] cartanParameterPlane := by
  let f : cartanParameterPlane →ₗ[ℝ] cartanParameterPlane :=
    { toFun := fun p => ⟨L p, by
        have : L p ∈ cartanParameterPlane.map L.toLinearMap :=
          ⟨p, p.property, rfl⟩
        rw [hL] at this
        exact this⟩
      map_add' := by
        intro p q
        apply Subtype.ext
        exact L.map_add p q
      map_smul' := by
        intro r p
        apply Subtype.ext
        exact L.map_smul r p }
  apply LinearEquiv.ofBijective f
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply L.injective
    exact congrArg Subtype.val hpq
  · intro q
    have hq : (q : Params) ∈ cartanParameterPlane.map L.toLinearMap := by
      rw [hL]
      exact q.property
    rcases hq with ⟨p, hp, hpeq⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    exact hpeq

theorem conjugatedParameterLieEquiv_map_cartanParameterPlane_eq_of_mem
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (hφ : ∀ p ∈ cartanParameterPlane,
      conjugatedParameterLinearMap φ p ∈ cartanParameterPlane) :
    cartanParameterPlane.map
        (conjugatedParameterLieEquiv φ).toLinearMap = cartanParameterPlane := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨p, hp, rfl⟩
    change conjugatedParameterLieEquiv φ p ∈ cartanParameterPlane
    rw [conjugatedParameterLieEquiv_apply]
    exact hφ p hp
  · exact (conjugatedParameterLieEquiv φ).finrank_map_eq cartanParameterPlane

noncomputable def cycleCartanParameterEquiv :
    cartanParameterPlane ≃ₗ[ℝ] cartanParameterPlane :=
  cartanParameterRestriction (conjugatedParameterLieEquiv realWeylCycle)
    (conjugatedParameterLieEquiv_map_cartanParameterPlane_eq_of_mem
      realWeylCycle
      (fun p hp => conjugatedParameterLinearMap_cycle_maps_cartanParameterPlane p hp))

noncomputable def reflectionCartanParameterEquiv :
    cartanParameterPlane ≃ₗ[ℝ] cartanParameterPlane :=
  cartanParameterRestriction (conjugatedParameterLieEquiv realWeylReflection)
    (conjugatedParameterLieEquiv_map_cartanParameterPlane_eq_of_mem
      realWeylReflection
      (fun p hp => conjugatedParameterLinearMap_reflection_maps_cartanParameterPlane p hp))

theorem conjugateCanonicalDerivation_maps_canonicalCartanParameterPlane
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (hφ : ∀ p ∈ cartanParameterPlane,
      conjugatedParameterLinearMap φ p ∈ cartanParameterPlane)
    {D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations}
    (hD : D ∈ canonicalCartanParameterPlane) :
    conjugateCanonicalDerivation φ D ∈ canonicalCartanParameterPlane := by
  rcases hD with ⟨p, hp, rfl⟩
  change p ∈ cartanParameterPlane at hp
  change conjugateCanonicalDerivation φ (parameterCanonicalLieEquiv p) ∈
    canonicalCartanParameterPlane
  apply conjugateCanonicalDerivation_mem_canonicalParameterSubmodule φ
    cartanParameterPlane p
  exact hφ p hp

theorem realWeylCycle_maps_canonicalCartanParameterPlane
    {D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations}
    (hD : D ∈ canonicalCartanParameterPlane) :
    conjugateCanonicalDerivation realWeylCycle D ∈ canonicalCartanParameterPlane := by
  exact conjugateCanonicalDerivation_maps_canonicalCartanParameterPlane
    realWeylCycle
    (fun p hp => conjugatedParameterLinearMap_cycle_maps_cartanParameterPlane p hp)
    hD

theorem realWeylReflection_maps_canonicalCartanParameterPlane
    {D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations}
    (hD : D ∈ canonicalCartanParameterPlane) :
    conjugateCanonicalDerivation realWeylReflection D ∈ canonicalCartanParameterPlane := by
  exact conjugateCanonicalDerivation_maps_canonicalCartanParameterPlane
    realWeylReflection
    (fun p hp => conjugatedParameterLinearMap_reflection_maps_cartanParameterPlane p hp)
    hD

private theorem cartanParameterPlane_mem_of_index_eq_six_or_thirteen
    (p : Params) (hp : p ∈ cartanParameterPlane) (i : Fin 14)
    (hi6 : i ≠ 6) (hi13 : i ≠ 13) : p i = 0 := by
  rw [cartanParameterPlane_eq_cartanPairParameterSpan] at hp
  refine Submodule.span_induction
    (p := fun q _ => q i = 0) ?_ (by simp) ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · simp [hi6, hi13,
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
    · simp [hi6, hi13,
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
  · intro p q _ _ hp hq
    simp [hp, hq]
  · intro r p _ hp
    simp [hp]

theorem conjugatedCartanParameters_cycle_support
    (j : Fin 2) (i : Fin 14) (hi6 : i ≠ 6) (hi13 : i ≠ 13) :
    conjugatedCartanParameters realWeylCycle j i = 0 := by
  have hp : derivationParameters (cartanDerivation j) ∈ cartanParameterPlane := by
    fin_cases j
    · change derivationParameters (parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 6)) ∈ _
      rw [parameterLinearEquiv.left_inv]
      apply Submodule.subset_span
      simp [cartanParameterPlane]
    · change derivationParameters (parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 13)) ∈ _
      rw [parameterLinearEquiv.left_inv]
      apply Submodule.subset_span
      simp [cartanParameterPlane]
  have hq := conjugatedParameterLinearMap_cycle_maps_cartanParameterPlane
    (derivationParameters (cartanDerivation j)) hp
  have heq : conjugatedCartanParameters realWeylCycle j =
      conjugatedParameterLinearMap realWeylCycle
        (derivationParameters (cartanDerivation j)) := by
    unfold conjugatedCartanParameters conjugatedParameterLinearMap
    rfl
  rw [heq]
  change (conjugatedParameterLinearMap realWeylCycle
    (derivationParameters (cartanDerivation j))) i = 0
  exact cartanParameterPlane_mem_of_index_eq_six_or_thirteen _ hq i hi6 hi13

theorem conjugatedCartanParameters_reflection_support
    (j : Fin 2) (i : Fin 14) (hi6 : i ≠ 6) (hi13 : i ≠ 13) :
    conjugatedCartanParameters realWeylReflection j i = 0 := by
  have hp : derivationParameters (cartanDerivation j) ∈ cartanParameterPlane := by
    fin_cases j
    · change derivationParameters (parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 6)) ∈ _
      simp [cartanDerivation, nativeParameterBasis, derivationParameters,
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
        parameterLinearEquiv]
    · change derivationParameters (parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 13)) ∈ _
      simp [cartanDerivation, nativeParameterBasis, derivationParameters,
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
        parameterLinearEquiv]
  have hq := conjugatedParameterLinearMap_reflection_maps_cartanParameterPlane
    (derivationParameters (cartanDerivation j)) hp
  have heq : conjugatedCartanParameters realWeylReflection j =
      conjugatedParameterLinearMap realWeylReflection
        (derivationParameters (cartanDerivation j)) := by
    unfold conjugatedCartanParameters conjugatedParameterLinearMap
    rfl
  rw [heq]
  change (conjugatedParameterLinearMap realWeylReflection
    (derivationParameters (cartanDerivation j))) i = 0
  exact cartanParameterPlane_mem_of_index_eq_six_or_thirteen _ hq i hi6 hi13

theorem params_eq_cartan_coordinates_of_support
    (p : Params)
    (hp : ∀ i : Fin 14, i ≠ 6 → i ≠ 13 → p i = 0) :
    p = p 6 • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      p 13 • InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  funext i
  by_cases h6 : i = 6
  · subst i
    simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
  by_cases h13 : i = 13
  · subst i
    simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]
  · rw [hp i h6 h13]
    simp [h6, h13,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit]

theorem conjugatedCartanParameters_cycle_eq_cartan_coordinates
    (j : Fin 2) :
    conjugatedCartanParameters realWeylCycle j =
      conjugatedCartanParameters realWeylCycle j 6 •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      conjugatedCartanParameters realWeylCycle j 13 •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  apply params_eq_cartan_coordinates_of_support
  intro i hi6 hi13
  exact conjugatedCartanParameters_cycle_support j i hi6 hi13

theorem conjugatedCartanParameters_reflection_eq_cartan_coordinates
    (j : Fin 2) :
    conjugatedCartanParameters realWeylReflection j =
      conjugatedCartanParameters realWeylReflection j 6 •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6 +
      conjugatedCartanParameters realWeylReflection j 13 •
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13 := by
  apply params_eq_cartan_coordinates_of_support
  intro i hi6 hi13
  exact conjugatedCartanParameters_reflection_support j i hi6 hi13

theorem cartanDerivation_zero_eq_pair_combination :
    cartanDerivation 0 =
      (1 / 3 : ℝ) •
          NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 0))
            (canonicalVectorEquiv (canonicalV 0)) +
        (-1 / 3 : ℝ) •
          NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 1))
            (canonicalVectorEquiv (canonicalV 1)) := by
  rw [← U0V0_innerDerivation_eq_cartanDerivation_add,
    ← U1V1_innerDerivation_eq_cartanDerivation_combination]
  module

theorem cartanDerivation_one_eq_pair_combination :
    cartanDerivation 1 =
      (2 / 3 : ℝ) •
          NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 0))
            (canonicalVectorEquiv (canonicalV 0)) +
        (1 / 3 : ℝ) •
          NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 1))
            (canonicalVectorEquiv (canonicalV 1)) := by
  rw [U0V0_innerDerivation_eq_cartanDerivation_add,
    U1V1_innerDerivation_eq_cartanDerivation_combination]
  module

theorem realWeylCycle_cartanBasis_zero_verified :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 0) =
      (-1 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
  rw [cartanDerivation_zero_eq_pair_combination]
  simp only [map_add, map_smul]
  rw [realWeylCycle_cartanPair_zero_verified,
    realWeylCycle_cartanPair_one_verified]
  module

theorem realWeylCycle_cartanBasis_one_verified :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 1) =
      (-1 : ℝ) • cartanDerivation 0 := by
  rw [cartanDerivation_one_eq_pair_combination]
  simp only [map_add, map_smul]
  rw [realWeylCycle_cartanPair_zero_verified,
    realWeylCycle_cartanPair_one_verified]
  module

theorem realWeylReflection_cartanBasis_zero_verified :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 0) =
      (1 / 3 : ℝ) • cartanDerivation 0 + (-2 / 3 : ℝ) • cartanDerivation 1 := by
  rw [cartanDerivation_zero_eq_pair_combination]
  simp only [map_add, map_smul]
  rw [realWeylReflection_cartanPair_zero_verified,
    realWeylReflection_cartanPair_one_verified]
  module

theorem realWeylReflection_cartanBasis_one_verified :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 1) =
      (-4 / 3 : ℝ) • cartanDerivation 0 + (-1 / 3 : ℝ) • cartanDerivation 1 := by
  rw [cartanDerivation_one_eq_pair_combination]
  simp only [map_add, map_smul]
  rw [realWeylReflection_cartanPair_zero_verified,
    realWeylReflection_cartanPair_one_verified]
  module

/-! Stable production names for the verified native Cartan basis action. -/

theorem realWeylCycle_cartanBasis_zero :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 0) =
      (-1 : ℝ) • cartanDerivation 0 + cartanDerivation 1 :=
  realWeylCycle_cartanBasis_zero_verified

theorem realWeylCycle_cartanBasis_one :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 1) =
      (-1 : ℝ) • cartanDerivation 0 :=
  realWeylCycle_cartanBasis_one_verified

theorem realWeylReflection_cartanBasis_zero :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 0) =
      (1 / 3 : ℝ) • cartanDerivation 0 + (-2 / 3 : ℝ) • cartanDerivation 1 :=
  realWeylReflection_cartanBasis_zero_verified

theorem realWeylReflection_cartanBasis_one :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 1) =
      (-4 / 3 : ℝ) • cartanDerivation 0 + (-1 / 3 : ℝ) • cartanDerivation 1 :=
  realWeylReflection_cartanBasis_one_verified

theorem canonicalCartanParameterPlane_le_nativeCartan :
    canonicalCartanParameterPlane ≤
      (axialCartanLieSubalgebra : Submodule ℝ canonicalZornDerivations) := by
  intro D hD
  rcases hD with ⟨p, hp, rfl⟩
  change p ∈ cartanParameterPlane at hp
  change parameterCanonicalLieEquiv p ∈ _
  rw [nativeCartan_eq_cartanRootSpan]
  change p ∈ Submodule.span ℝ
    ({parameterUnit 6, parameterUnit 13} : Set Params) at hp
  refine Submodule.span_induction (p := fun q _ =>
    parameterCanonicalLieEquiv q ∈ cartanRootSpan) ?_ ?_ ?_ ?_ hp
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · change rootDerivation 6 ∈ cartanRootSpan
      exact Submodule.subset_span (by simp)
    · change rootDerivation 13 ∈ cartanRootSpan
      exact Submodule.subset_span (by simp)
  · simp
  · intro p q hp hq ihp ihq
    simpa only [map_add] using Submodule.add_mem cartanRootSpan ihp ihq
  · intro a p hp ihp
    simpa only [map_smul] using Submodule.smul_mem cartanRootSpan a ihp

theorem canonicalCartanParameterPlane_le_nativeCartan_public :
    canonicalCartanParameterPlane ≤
      (InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra :
        Submodule ℝ canonicalZornDerivations) := by
  intro D hD
  rcases hD with ⟨p, hp, rfl⟩
  change p ∈ cartanParameterPlane at hp
  change parameterCanonicalLieEquiv p ∈ _
  rw [nativeCartan_eq_cartanRootSpan]
  change p ∈ Submodule.span ℝ
    ({parameterUnit 6, parameterUnit 13} : Set Params) at hp
  refine Submodule.span_induction (p := fun q _ =>
    parameterCanonicalLieEquiv q ∈ cartanRootSpan) ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · change rootDerivation 6 ∈ cartanRootSpan
      exact Submodule.subset_span (by simp)
    · change rootDerivation 13 ∈ cartanRootSpan
      exact Submodule.subset_span (by simp)
  · simp
  · intro p q hp hq ihp ihq
    simpa only [map_add] using Submodule.add_mem cartanRootSpan ihp ihq
  · intro a p hp ihp
    simpa only [map_smul] using Submodule.smul_mem cartanRootSpan a ihp

theorem nativeCartan_eq_canonicalCartanParameterPlane :
    (InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra :
      Submodule ℝ canonicalZornDerivations) =
      canonicalCartanParameterPlane := by
  apply le_antisymm
  · intro D hD
    change D ∈ (axialCartanLieSubalgebra : Submodule ℝ canonicalZornDerivations) at hD
    change D ∈ (axialCartanLieSubalgebra : Submodule ℝ canonicalZornDerivations) at hD
    have hD' : D ∈ cartanRootSpan := by
      rw [← nativeCartan_eq_cartanRootSpan]
      change D ∈ (InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra :
        Submodule ℝ canonicalZornDerivations) at hD
      exact hD
    refine Submodule.span_induction
      (p := fun q _ => q ∈ canonicalCartanParameterPlane) ?_ ?_ ?_ ?_ hD'
    · intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact ⟨InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6,
          Submodule.subset_span (by simp), by rfl⟩
      · exact ⟨InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13,
          Submodule.subset_span (by simp), by rfl⟩
    · exact canonicalCartanParameterPlane.zero_mem
    · intro p q hp hq ihp ihq
      exact canonicalCartanParameterPlane.add_mem ihp ihq
    · intro a p hp ihp
      exact canonicalCartanParameterPlane.smul_mem a ihp
  · intro D hD
    rcases hD with ⟨p, hp, rfl⟩
    change p ∈ cartanParameterPlane at hp
    change parameterCanonicalLieEquiv p ∈ _
    rw [nativeCartan_eq_cartanRootSpan]
    change p ∈ Submodule.span ℝ
      ({parameterUnit 6, parameterUnit 13} : Set Params) at hp
    refine Submodule.span_induction (p := fun q _ =>
      parameterCanonicalLieEquiv q ∈ cartanRootSpan) ?_ ?_ ?_ ?_ hp
    · intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · change rootDerivation 6 ∈ cartanRootSpan
        exact Submodule.subset_span (by simp)
      · change rootDerivation 13 ∈ cartanRootSpan
        exact Submodule.subset_span (by simp)
    · simp
    · intro p q hp hq ihp ihq
      simpa only [map_add] using Submodule.add_mem cartanRootSpan ihp ihq
    · intro a p hp ihp
      simpa only [map_smul] using Submodule.smul_mem cartanRootSpan a ihp


/-

theorem U0V0_innerDerivation_eq_cartanDerivation_add :
    NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 0))
        (canonicalVectorEquiv (canonicalV 0)) =
      cartanDerivation 0 + cartanDerivation 1 := by
  change _ = parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 6) +
      parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) 13)
  rw [← map_add]
  rw [← parameterLinearEquiv.apply_symm_apply
    (NativeStanDerivationBilinear.innerDerivation
      (canonicalVectorEquiv (canonicalU 0))
      (canonicalVectorEquiv (canonicalV 0)))]
  rw [← canonicalToVector_standard_U0_V0]
  apply_fun parameterLinearEquiv.symm
  simp only [LinearEquiv.symm_apply_apply]
  change canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)) = _
  rw [standardColumn_U0_V0]
  simp [cartanDerivation, nativeParameterBasis, parameterLinearEquiv,
    parameterUnit]
  · funext i
    fin_cases i <;> simp [parameterUnit, Pi.basisFun]
  · exact parameterLinearEquiv.symm.injective

def cycleCartanInputSpan : Submodule ℝ Params :=
  Submodule.span ℝ ({
    derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 0))
        (canonicalVectorEquiv (canonicalV 0))),
    derivationParameters
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 1))) } : Set Params)

theorem cycleCartanInputSpan_eq_cartanParameterPlane :
    cycleCartanInputSpan = cartanParameterPlane := by
  unfold cycleCartanInputSpan
  rw [U0V0_parameter_readback, U1V1_parameter_readback]
  exact cartanParameterPlane_eq_cartanPairParameterSpan.symm

theorem conjugatedParameterLinearMap_cycle_maps_cartanParameterPlane' :
    ∀ p ∈ cartanParameterPlane,
      conjugatedParameterLinearMap realWeylCycle p ∈ cartanParameterPlane := by
  intro p hp
  rw [← cycleCartanInputSpan_eq_cartanParameterPlane] at hp
  refine Submodule.span_induction
    (p := fun q _ => conjugatedParameterLinearMap realWeylCycle q ∈
      cartanParameterPlane) ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact conjugatedParameterLinearMap_cycle_U0V0_mem_cartanParameterPlane
    · exact conjugatedParameterLinearMap_cycle_U1V1_mem_cartanParameterPlane
  · change conjugatedParameterLinearMap realWeylCycle 0 ∈ cartanParameterPlane
    rw [(conjugatedParameterLinearMap realWeylCycle).map_zero]
    exact cartanParameterPlane.zero_mem
  · intro p q _ _ hp hq
    rw [(conjugatedParameterLinearMap realWeylCycle).map_add]
    exact cartanParameterPlane.add_mem hp hq
  · intro r p _ hp
    rw [(conjugatedParameterLinearMap realWeylCycle).map_smul]
    exact cartanParameterPlane.smul_mem r hp

 -/


theorem conjugatedParameterLieEquiv_map_cartanParameterPlane_eq
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (hφ : ∀ p ∈ cartanParameterPlane,
      conjugatedParameterLinearMap φ p ∈ cartanParameterPlane) :
    cartanParameterPlane.map
        (conjugatedParameterLieEquiv φ).toLinearMap = cartanParameterPlane := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨p, hp, rfl⟩
    change conjugatedParameterLieEquiv φ p ∈ cartanParameterPlane
    rw [conjugatedParameterLieEquiv_apply]
    exact hφ p hp
  · exact (conjugatedParameterLieEquiv φ).finrank_map_eq cartanParameterPlane

theorem realWeylCycle_parameterCartanPlane_map_eq :
    cartanParameterPlane.map
        (conjugatedParameterLieEquiv realWeylCycle).toLinearMap =
      cartanParameterPlane := by
  exact conjugatedParameterLieEquiv_map_cartanParameterPlane_eq
    realWeylCycle
    (fun p hp => conjugatedParameterLinearMap_cycle_maps_cartanParameterPlane p hp)

theorem realWeylReflection_parameterCartanPlane_map_eq :
    cartanParameterPlane.map
        (conjugatedParameterLieEquiv realWeylReflection).toLinearMap =
      cartanParameterPlane := by
  exact conjugatedParameterLieEquiv_map_cartanParameterPlane_eq
    realWeylReflection
    (fun p hp => conjugatedParameterLinearMap_reflection_maps_cartanParameterPlane p hp)

-/

theorem canonicalCartanParameterPlane_le_nativeCartan_qualified :
    canonicalCartanParameterPlane ≤
      InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra.toSubmodule := by
  intro D hD
  rcases hD with ⟨p, hp, rfl⟩
  change p ∈ cartanParameterPlane at hp
  change InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.parameterCanonicalLieEquiv p ∈
    InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra.toSubmodule
  rw [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.nativeCartan_eq_cartanRootSpan]
  change p ∈ Submodule.span ℝ
    ({InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13} :
        Set InfoGeometry.Lie.CanonicalZornDerivationDimension.Params) at hp
  refine Submodule.span_induction (p := fun q _ =>
    InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.parameterCanonicalLieEquiv q ∈
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.cartanRootSpan) ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · change InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivation 6 ∈
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.cartanRootSpan
      exact Submodule.subset_span (by simp)
    · change InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivation 13 ∈
        InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.cartanRootSpan
      exact Submodule.subset_span (by simp)
  · simp
  · intro p q hp hq ihp ihq
    simpa only [map_add] using Submodule.add_mem
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.cartanRootSpan ihp ihq
  · intro a p hp ihp
    simpa only [map_smul] using Submodule.smul_mem
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.cartanRootSpan a ihp

theorem nativeCartan_le_canonicalCartanParameterPlane_qualified :
    InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra.toSubmodule ≤
      canonicalCartanParameterPlane := by
  intro D hD
  have hD' : D ∈ InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.cartanRootSpan := by
    rw [← InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.nativeCartan_eq_cartanRootSpan]
    exact hD
  refine Submodule.span_induction
    (p := fun q _ => q ∈ canonicalCartanParameterPlane) ?_ ?_ ?_ ?_ hD'
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact ⟨InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 6,
        Submodule.subset_span (by simp), by rfl⟩
    · exact ⟨InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit 13,
        Submodule.subset_span (by simp), by rfl⟩
  · exact canonicalCartanParameterPlane.zero_mem
  · intro p q hp hq ihp ihq
    exact canonicalCartanParameterPlane.add_mem ihp ihq
  · intro a p hp ihp
    exact canonicalCartanParameterPlane.smul_mem a ihp

theorem nativeCartan_eq_canonicalCartanParameterPlane_qualified :
    InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra.toSubmodule =
      canonicalCartanParameterPlane := by
  exact le_antisymm
    nativeCartan_le_canonicalCartanParameterPlane_qualified
    canonicalCartanParameterPlane_le_nativeCartan_qualified

noncomputable def nativeCartanParameterPlaneEquiv :
    InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra.toSubmodule
      ≃ₗ[ℝ] canonicalCartanParameterPlane := by
  let f : InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra.toSubmodule
      →ₗ[ℝ] canonicalCartanParameterPlane :=
    { toFun := fun H => ⟨H.1, by
        rw [← nativeCartan_eq_canonicalCartanParameterPlane_qualified]
        exact H.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a x
        apply Subtype.ext
        rfl }
  exact LinearEquiv.ofBijective f ⟨
    (fun x y h => by
      apply Subtype.ext
      exact congrArg (fun z : canonicalCartanParameterPlane => z.1) h),
    (fun y => by
      refine ⟨⟨y.1, ?_⟩, ?_⟩
      · rw [nativeCartan_eq_canonicalCartanParameterPlane_qualified]
        exact y.2
      · rfl)⟩

noncomputable def restrictCanonicalDerivationEquiv
    (P : Submodule ℝ canonicalZornDerivations)
    (L : canonicalZornDerivations ≃ₗ⁅ℝ⁆ canonicalZornDerivations)
    (hL : ∀ D ∈ P, L D ∈ P)
    (hLinv : ∀ D ∈ P, L.symm D ∈ P) :
    P ≃ₗ[ℝ] P := by
  let f : P →ₗ[ℝ] P :=
    { toFun := fun D => ⟨L D, hL D.1 D.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change L (((x + y : P) : canonicalZornDerivations)) =
          L ((x : P) : canonicalZornDerivations) +
            L ((y : P) : canonicalZornDerivations)
        exact map_add L _ _
      map_smul' := by
        intro a x
        apply Subtype.ext
        change L (((a • x : P) : canonicalZornDerivations)) =
          (RingHom.id ℝ) a • L ((x : P) : canonicalZornDerivations)
        simpa only [RingHom.id_apply] using
          map_smul L a ((x : P) : canonicalZornDerivations) }
  exact LinearEquiv.ofBijective f ⟨
    (fun x y h => by
      apply Subtype.ext
      apply L.injective
      exact congrArg (fun z : P => (z : canonicalZornDerivations)) h),
    (fun y => by
      refine ⟨⟨L.symm y.1, hLinv y.1 y.2⟩, ?_⟩
      apply Subtype.ext
      simp [f])⟩

/-
theorem conjugateCanonicalDerivation_map_canonicalCartanParameterPlane_eq
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (hφ : ∀ D ∈ canonicalCartanParameterPlane,
      conjugateCanonicalDerivation φ D ∈ canonicalCartanParameterPlane) :
    canonicalCartanParameterPlane.map
        (conjugateCanonicalDerivation φ).toLinearMap =
      canonicalCartanParameterPlane := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨D, hD, rfl⟩
    exact hφ D hD
  · exact (conjugateCanonicalDerivation φ).toLinearEquiv.finrank_map_eq
      canonicalCartanParameterPlane

theorem conjugateCanonicalDerivation_symm_mem_canonicalCartanParameterPlane
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (hφ : ∀ D ∈ canonicalCartanParameterPlane,
      conjugateCanonicalDerivation φ D ∈ canonicalCartanParameterPlane)
    {D : canonicalZornDerivations} (hD : D ∈ canonicalCartanParameterPlane) :
    (conjugateCanonicalDerivation φ).symm D ∈ canonicalCartanParameterPlane := by
  have hm : D ∈ canonicalCartanParameterPlane.map
      (conjugateCanonicalDerivation φ).toLinearMap := by
    rw [conjugateCanonicalDerivation_map_canonicalCartanParameterPlane_eq φ hφ]
    exact hD
  rcases hm with ⟨E, hE, hED⟩
  have hEq : conjugateCanonicalDerivation φ E = D := hED
  rw [← hEq]
  simpa using hE

noncomputable def realWeylCycle_canonicalCartanEquiv :
    canonicalCartanParameterPlane ≃ₗ[ℝ] canonicalCartanParameterPlane :=
  restrictCanonicalDerivationEquiv canonicalCartanParameterPlane
    (conjugateCanonicalDerivation realWeylCycle)
    (fun D hD => realWeylCycle_maps_canonicalCartanParameterPlane hD)
    (fun D hD =>
      conjugateCanonicalDerivation_symm_mem_canonicalCartanParameterPlane
        realWeylCycle
        (fun D hD => realWeylCycle_maps_canonicalCartanParameterPlane hD)
        hD)

noncomputable def realWeylReflection_canonicalCartanEquiv :
    canonicalCartanParameterPlane ≃ₗ[ℝ] canonicalCartanParameterPlane :=
  restrictCanonicalDerivationEquiv canonicalCartanParameterPlane
    (conjugateCanonicalDerivation realWeylReflection)
    (fun D hD => realWeylReflection_maps_canonicalCartanParameterPlane hD)
    (fun D hD =>
      conjugateCanonicalDerivation_symm_mem_canonicalCartanParameterPlane
        realWeylReflection
        (fun D hD => realWeylReflection_maps_canonicalCartanParameterPlane hD)
        hD)

-/

/-
theorem cartanDerivation_zero_eq_pair_combination_active :
    cartanDerivation 0 =
      (1 / 3 : ℝ) •
          NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 0))
            (canonicalVectorEquiv (canonicalV 0)) +
        (-1 / 3 : ℝ) •
          NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 1))
            (canonicalVectorEquiv (canonicalV 1)) := by
  rw [← U0V0_innerDerivation_eq_cartanDerivation_add,
    ← U1V1_innerDerivation_eq_cartanDerivation_combination]
  module

theorem cartanDerivation_one_eq_pair_combination_active :
    cartanDerivation 1 =
      (2 / 3 : ℝ) •
          NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 0))
            (canonicalVectorEquiv (canonicalV 0)) +
        (1 / 3 : ℝ) •
          NativeStanDerivationBilinear.innerDerivation
            (canonicalVectorEquiv (canonicalU 1))
            (canonicalVectorEquiv (canonicalV 1)) := by
  rw [U0V0_innerDerivation_eq_cartanDerivation_add,
    U1V1_innerDerivation_eq_cartanDerivation_combination]
  module

theorem realWeylCycle_cartanBasis_zero_active :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 0) =
      (-1 : ℝ) • cartanDerivation 0 + cartanDerivation 1 := by
  rw [cartanDerivation_zero_eq_pair_combination_active]
  change conjugateNativeDerivationLinear realWeylCycle _ = _
  simp only [map_add, map_smul]
  rw [realWeylCycle_cartanPair_zero_verified,
    realWeylCycle_cartanPair_one_verified]
  module

theorem realWeylCycle_cartanBasis_one_active :
    conjugateNativeDerivation realWeylCycle (cartanDerivation 1) =
      (-1 : ℝ) • cartanDerivation 0 := by
  rw [cartanDerivation_one_eq_pair_combination_active]
  change conjugateNativeDerivationLinear realWeylCycle _ = _
  simp only [map_add, map_smul]
  rw [realWeylCycle_cartanPair_zero_verified,
    realWeylCycle_cartanPair_one_verified]
  module

theorem realWeylReflection_cartanBasis_zero_active :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 0) =
      (1 / 3 : ℝ) • cartanDerivation 0 + (-2 / 3 : ℝ) • cartanDerivation 1 := by
  rw [cartanDerivation_zero_eq_pair_combination_active]
  change conjugateNativeDerivationLinear realWeylReflection _ = _
  simp only [map_add, map_smul]
  rw [realWeylReflection_cartanPair_zero_verified,
    realWeylReflection_cartanPair_one_verified]
  module

theorem realWeylReflection_cartanBasis_one_active :
    conjugateNativeDerivation realWeylReflection (cartanDerivation 1) =
      (-4 / 3 : ℝ) • cartanDerivation 0 + (-1 / 3 : ℝ) • cartanDerivation 1 := by
  rw [cartanDerivation_one_eq_pair_combination_active]
  change conjugateNativeDerivationLinear realWeylReflection _ = _
  simp only [map_add, map_smul]
  rw [realWeylReflection_cartanPair_zero_verified,
    realWeylReflection_cartanPair_one_verified]
  module
 -/

end InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
