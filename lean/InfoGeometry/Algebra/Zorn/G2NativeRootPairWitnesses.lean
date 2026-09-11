import InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native pair witnesses for selected finite roots

These are exact carrier-level identities.  They do not assert a Weyl root
action; they expose the inner-derivation representatives needed by the Weyl
covariance owner.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2NativeRootPairWitnesses

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
open InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornMathlibRootSpace
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivationRootBridge
open InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem

theorem shortZero_eq_inner_E11_V0 :
    zornDerivationRootRepresentation
        (⟨RootLength.Short, 0⟩ : G2Root) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalV 0)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalV 0))) =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 0) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv canonicalE11)
          (canonicalVectorEquiv (canonicalV 0))),
    ]
  change rootDerivation 0 =
    canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 0)
  exact standardColumn_E11_V0_root.symm

theorem shortOne_eq_inner_E11_V1 :
    zornDerivationRootRepresentation
        (⟨RootLength.Short, 1⟩ : G2Root) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalV 1)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalV 1))) =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 1) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv canonicalE11)
          (canonicalVectorEquiv (canonicalV 1))),
    ]
  change rootDerivation 3 =
    canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 1)
  exact standardColumn_E11_V1_root.symm

theorem realWeylCycle_shortZero_to_shortOne :
    conjugateNativeDerivation realWeylCycle
        (zornDerivationRootRepresentation
          (⟨RootLength.Short, 0⟩ : G2Root)) =
      zornDerivationRootRepresentation
        (⟨RootLength.Short, 1⟩ : G2Root) := by
  rw [shortZero_eq_inner_E11_V0]
  have hE : nativeCircularBasis (0 : Fin 8) =
      canonicalVectorEquiv canonicalE11 := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 0) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_scalarPlus_nativeE11
  have hV : nativeCircularBasis (5 : Fin 8) =
      canonicalVectorEquiv (canonicalV 0) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 5) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootMinus_nativeV 0
  have hV1 : nativeCircularBasis (6 : Fin 8) =
      canonicalVectorEquiv (canonicalV 1) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 6) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootMinus_nativeV 1
  rw [← hE, ← hV]
  change realWeylCycle •
      NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis (0 : Fin 8)) (nativeCircularBasis (5 : Fin 8)) = _
  rw [realWeylCycle_nativeCircularPairDerivation]
  change NativeStanDerivationBilinear.innerDerivation
      (nativeCircularBasis (cycleFrameIndex 0))
      (nativeCircularBasis (cycleFrameIndex 5)) = _
  norm_num [cycleFrameIndex]
  rw [hE, hV1]
  exact shortOne_eq_inner_E11_V1.symm

theorem longZero_eq_neg_third_inner_U1_V0 :
    zornDerivationRootRepresentation
        (⟨RootLength.Long, 0⟩ : G2Root) =
      (-1 / 3 : ℝ) •
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 0)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport]
  rw [map_smul]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 0))) =
      canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 0)))]
  rw [standardColumn_U1_V0_root]
  change rootDerivation 1 = (-1 / 3 : ℝ) • (-3 : ℝ) • rootDerivation 1
  module

theorem longOne_eq_neg_third_inner_U2_V0 :
    zornDerivationRootRepresentation
        (⟨RootLength.Long, 1⟩ : G2Root) =
      (-1 / 3 : ℝ) •
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 2))
          (canonicalVectorEquiv (canonicalV 0)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport]
  rw [map_smul]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 0))) =
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv (canonicalU 2))
          (canonicalVectorEquiv (canonicalV 0)))]
  rw [standardColumn_U2_V0_root]
  change rootDerivation 2 = (-1 / 3 : ℝ) • (-3 : ℝ) • rootDerivation 2
  module

theorem shortTwo_eq_neg_inner_E11_U2 :
    zornDerivationRootRepresentation
        (⟨RootLength.Short, 2⟩ : G2Root) =
      (-1 : ℝ) •
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv canonicalE11)
          (canonicalVectorEquiv (canonicalU 2)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport]
  rw [map_smul]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalU 2))) =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 2) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv canonicalE11)
          (canonicalVectorEquiv (canonicalU 2)))]
  rw [standardColumn_E11_U2_root]
  change rootDerivation 4 = (-1 : ℝ) • (-1 : ℝ) • rootDerivation 4
  module

theorem longTwo_eq_neg_third_inner_U0_V1 :
    zornDerivationRootRepresentation
        (⟨RootLength.Long, 2⟩ : G2Root) =
      (-1 / 3 : ℝ) •
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 1)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport, map_smul]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 0))
        (canonicalVectorEquiv (canonicalV 1))) =
      canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 1) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 1))),
    standardColumn_U0_V1_root]
  change rootDerivation 5 = (-1 / 3 : ℝ) • (-3 : ℝ) • rootDerivation 5
  module

theorem longThree_eq_neg_third_inner_U2_V1 :
    zornDerivationRootRepresentation
        (⟨RootLength.Long, 3⟩ : G2Root) =
      (-1 / 3 : ℝ) •
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 2))
          (canonicalVectorEquiv (canonicalV 1)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport, map_smul]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 2))
        (canonicalVectorEquiv (canonicalV 1))) =
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv (canonicalU 2))
          (canonicalVectorEquiv (canonicalV 1))),
    standardColumn_U2_V1_root]
  change rootDerivation 7 = (-1 / 3 : ℝ) • (-3 : ℝ) • rootDerivation 7
  module

theorem realWeylCycle_longZero_to_longThree :
    conjugateNativeDerivation realWeylCycle
        (zornDerivationRootRepresentation
          (⟨RootLength.Long, 0⟩ : G2Root)) =
      zornDerivationRootRepresentation
        (⟨RootLength.Long, 3⟩ : G2Root) := by
  rw [longZero_eq_neg_third_inner_U1_V0]
  have hU1 : nativeCircularBasis (2 : Fin 8) =
      canonicalVectorEquiv (canonicalU 1) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 2) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootPlus_nativeU 1
  have hU2 : nativeCircularBasis (3 : Fin 8) =
      canonicalVectorEquiv (canonicalU 2) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 3) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootPlus_nativeU 2
  have hV0 : nativeCircularBasis (5 : Fin 8) =
      canonicalVectorEquiv (canonicalV 0) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 5) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootMinus_nativeV 0
  have hV1 : nativeCircularBasis (6 : Fin 8) =
      canonicalVectorEquiv (canonicalV 1) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 6) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootMinus_nativeV 1
  change conjugateNativeDerivationLinear realWeylCycle
      ((-1 / 3 : ℝ) • NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 0))) = _
  rw [(conjugateNativeDerivationLinear realWeylCycle).map_smul,
    conjugateNativeDerivationLinear_apply, ← hU1, ← hV0]
  change (-1 / 3 : ℝ) • (realWeylCycle •
      NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis (2 : Fin 8)) (nativeCircularBasis (5 : Fin 8))) = _
  rw [realWeylCycle_nativeCircularPairDerivation]
  norm_num [cycleFrameIndex]
  rw [hU2, hV1]
  convert longThree_eq_neg_third_inner_U2_V1.symm using 1 <;> norm_num

theorem longFour_eq_neg_third_inner_U0_V2 :
    zornDerivationRootRepresentation
        (⟨RootLength.Long, 4⟩ : G2Root) =
      (-1 / 3 : ℝ) •
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 2)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport, map_smul]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 0))
        (canonicalVectorEquiv (canonicalV 2))) =
      canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 2) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv (canonicalU 0))
          (canonicalVectorEquiv (canonicalV 2))),
    standardColumn_U0_V2_root]
  change rootDerivation 11 = (-1 / 3 : ℝ) • (-3 : ℝ) • rootDerivation 11
  module

theorem longFive_eq_neg_third_inner_U1_V2 :
    zornDerivationRootRepresentation
        (⟨RootLength.Long, 5⟩ : G2Root) =
      (-1 / 3 : ℝ) •
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 2)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport, map_smul]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 2))) =
      canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 2) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv (canonicalU 1))
          (canonicalVectorEquiv (canonicalV 2))),
    standardColumn_U1_V2_root]
  change rootDerivation 12 = (-1 / 3 : ℝ) • (-3 : ℝ) • rootDerivation 12
  module

theorem shortThree_eq_inner_E11_V2 :
    zornDerivationRootRepresentation
        (⟨RootLength.Short, 3⟩ : G2Root) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalV 2)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalV 2))) =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 2) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv canonicalE11)
          (canonicalVectorEquiv (canonicalV 2))),
    standardColumn_E11_V2_root]
  change rootDerivation 8 = rootDerivation 8
  rfl

theorem realWeylCycle_shortOne_to_shortThree :
    conjugateNativeDerivation realWeylCycle
        (zornDerivationRootRepresentation
          (⟨RootLength.Short, 1⟩ : G2Root)) =
      zornDerivationRootRepresentation
        (⟨RootLength.Short, 3⟩ : G2Root) := by
  rw [shortOne_eq_inner_E11_V1]
  have hE : nativeCircularBasis (0 : Fin 8) =
      canonicalVectorEquiv canonicalE11 := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 0) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_scalarPlus_nativeE11
  have hV : nativeCircularBasis (6 : Fin 8) =
      canonicalVectorEquiv (canonicalV 1) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 6) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootMinus_nativeV 1
  have hV2 : nativeCircularBasis (7 : Fin 8) =
      canonicalVectorEquiv (canonicalV 2) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 7) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootMinus_nativeV 2
  change realWeylCycle •
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalV 1)) = _
  rw [← hE, ← hV, realWeylCycle_nativeCircularPairDerivation]
  norm_num [cycleFrameIndex]
  rw [hE, hV2]
  exact shortThree_eq_inner_E11_V2.symm

theorem realWeylCycle_shortThree_to_shortZero :
    conjugateNativeDerivation realWeylCycle
        (zornDerivationRootRepresentation
          (⟨RootLength.Short, 3⟩ : G2Root)) =
      zornDerivationRootRepresentation
        (⟨RootLength.Short, 0⟩ : G2Root) := by
  rw [shortThree_eq_inner_E11_V2]
  have hE : nativeCircularBasis (0 : Fin 8) =
      canonicalVectorEquiv canonicalE11 := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 0) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_scalarPlus_nativeE11
  have hV2 : nativeCircularBasis (7 : Fin 8) =
      canonicalVectorEquiv (canonicalV 2) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 7) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootMinus_nativeV 2
  have hV0 : nativeCircularBasis (5 : Fin 8) =
      canonicalVectorEquiv (canonicalV 0) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 5) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootMinus_nativeV 0
  change realWeylCycle •
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalV 2)) = _
  rw [← hE, ← hV2, realWeylCycle_nativeCircularPairDerivation]
  norm_num [cycleFrameIndex]
  rw [hE, hV0]
  exact shortZero_eq_inner_E11_V0.symm

theorem shortFour_eq_inner_E11_U1 :
    zornDerivationRootRepresentation
        (⟨RootLength.Short, 4⟩ : G2Root) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalU 1)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalU 1))) =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 1) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv canonicalE11)
          (canonicalVectorEquiv (canonicalU 1))),
    standardColumn_E11_U1_root]
  change rootDerivation 9 = rootDerivation 9
  rfl

theorem realWeylCycle_shortFour_to_shortTwo :
    conjugateNativeDerivation realWeylCycle
        (zornDerivationRootRepresentation
          (⟨RootLength.Short, 4⟩ : G2Root)) =
      -zornDerivationRootRepresentation
        (⟨RootLength.Short, 2⟩ : G2Root) := by
  rw [shortFour_eq_inner_E11_U1]
  have hE : nativeCircularBasis (0 : Fin 8) =
      canonicalVectorEquiv canonicalE11 := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 0) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_scalarPlus_nativeE11
  have hU1 : nativeCircularBasis (2 : Fin 8) =
      canonicalVectorEquiv (canonicalU 1) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 2) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootPlus_nativeU 1
  have hU2 : nativeCircularBasis (3 : Fin 8) =
      canonicalVectorEquiv (canonicalU 2) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 3) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootPlus_nativeU 2
  change realWeylCycle •
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalU 1)) = _
  rw [← hE, ← hU1, realWeylCycle_nativeCircularPairDerivation]
  norm_num [cycleFrameIndex]
  rw [hE, hU2, shortTwo_eq_neg_inner_E11_U2]
  simp

theorem shortFive_eq_neg_inner_E11_U0 :
    zornDerivationRootRepresentation
        (⟨RootLength.Short, 5⟩ : G2Root) =
      (-1 : ℝ) •
        NativeStanDerivationBilinear.innerDerivation
          (canonicalVectorEquiv canonicalE11)
          (canonicalVectorEquiv (canonicalU 0)) := by
  apply vectorCanonicalLinearEquiv.injective
  rw [rootIndexOf_canonical_derivation_transport, map_smul]
  rw [show vectorCanonicalLinearEquiv
      (NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalU 0))) =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 0) by
        simpa using (vector_inner_to_canonical
          (canonicalVectorEquiv canonicalE11)
          (canonicalVectorEquiv (canonicalU 0))),
    standardColumn_E11_U0_root]
  change rootDerivation 10 = (-1 : ℝ) • (-1 : ℝ) • rootDerivation 10
  module

theorem realWeylCycle_shortTwo_to_shortFive :
    conjugateNativeDerivation realWeylCycle
        (zornDerivationRootRepresentation
          (⟨RootLength.Short, 2⟩ : G2Root)) =
      zornDerivationRootRepresentation
        (⟨RootLength.Short, 5⟩ : G2Root) := by
  rw [shortTwo_eq_neg_inner_E11_U2]
  have hE : nativeCircularBasis (0 : Fin 8) =
      canonicalVectorEquiv canonicalE11 := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 0) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_scalarPlus_nativeE11
  have hU2 : nativeCircularBasis (3 : Fin 8) =
      canonicalVectorEquiv (canonicalU 2) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 3) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootPlus_nativeU 2
  have hU0 : nativeCircularBasis (1 : Fin 8) =
      canonicalVectorEquiv (canonicalU 0) := by
    change canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 1) = _
    rw [InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]
    exact circular_rootPlus_nativeU 0
  change realWeylCycle •
      ((-1 : ℝ) • NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalU 2))) = _
  change conjugateNativeDerivationLinear realWeylCycle
      ((-1 : ℝ) • NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv canonicalE11)
        (canonicalVectorEquiv (canonicalU 2))) = _
  rw [(conjugateNativeDerivationLinear realWeylCycle).map_smul,
    conjugateNativeDerivationLinear_apply]
  rw [← hE, ← hU2]
  change (-1 : ℝ) • (realWeylCycle •
      NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis (0 : Fin 8)) (nativeCircularBasis (3 : Fin 8))) = _
  rw [realWeylCycle_nativeCircularPairDerivation]
  norm_num [cycleFrameIndex]
  rw [hE, hU0, shortFive_eq_neg_inner_E11_U0]
  simp

theorem root_representation_exists_scaled_inner_witness (r : G2Root) :
    ∃ (a : ℝ) (x y : ZornVectorMatrix ℝ),
      zornDerivationRootRepresentation r =
        a • NativeStanDerivationBilinear.innerDerivation x y := by
  rcases r with ⟨l, k⟩
  fin_cases l <;> fin_cases k
  · exact ⟨1, canonicalVectorEquiv canonicalE11,
      canonicalVectorEquiv (canonicalV 0), by simpa using shortZero_eq_inner_E11_V0⟩
  · exact ⟨1, canonicalVectorEquiv canonicalE11,
      canonicalVectorEquiv (canonicalV 1), by simpa using shortOne_eq_inner_E11_V1⟩
  · exact ⟨-1, canonicalVectorEquiv canonicalE11,
      canonicalVectorEquiv (canonicalU 2), by simpa using shortTwo_eq_neg_inner_E11_U2⟩
  · exact ⟨1, canonicalVectorEquiv canonicalE11,
      canonicalVectorEquiv (canonicalV 2), by simpa using shortThree_eq_inner_E11_V2⟩
  · exact ⟨1, canonicalVectorEquiv canonicalE11,
      canonicalVectorEquiv (canonicalU 1), by simpa using shortFour_eq_inner_E11_U1⟩
  · exact ⟨-1, canonicalVectorEquiv canonicalE11,
      canonicalVectorEquiv (canonicalU 0), by simpa using shortFive_eq_neg_inner_E11_U0⟩
  · exact ⟨-1 / 3, canonicalVectorEquiv (canonicalU 1),
      canonicalVectorEquiv (canonicalV 0), by simpa using longZero_eq_neg_third_inner_U1_V0⟩
  · exact ⟨-1 / 3, canonicalVectorEquiv (canonicalU 2),
      canonicalVectorEquiv (canonicalV 0), by simpa using longOne_eq_neg_third_inner_U2_V0⟩
  · exact ⟨-1 / 3, canonicalVectorEquiv (canonicalU 0),
      canonicalVectorEquiv (canonicalV 1), by simpa using longTwo_eq_neg_third_inner_U0_V1⟩
  · exact ⟨-1 / 3, canonicalVectorEquiv (canonicalU 2),
      canonicalVectorEquiv (canonicalV 1), by simpa using longThree_eq_neg_third_inner_U2_V1⟩
  · exact ⟨-1 / 3, canonicalVectorEquiv (canonicalU 0),
      canonicalVectorEquiv (canonicalV 2), by simpa using longFour_eq_neg_third_inner_U0_V2⟩
  · exact ⟨-1 / 3, canonicalVectorEquiv (canonicalU 1),
      canonicalVectorEquiv (canonicalV 2), by simpa using longFive_eq_neg_third_inner_U1_V2⟩

theorem root_representation_ne_zero (r : G2Root) :
    zornDerivationRootRepresentation r ≠ 0 := by
  intro hz
  have hroot := congrArg vectorCanonicalLinearEquiv hz
  rw [rootIndexOf_canonical_derivation_transport] at hroot
  exact rootDerivation_ne_zero (rootIndexOf r).1 (by simpa using hroot)

/-
theorem rootDerivation_bracket_eigen (i : nonzeroIndex)
    (H : axialCartanLieSubalgebra) :
    ⁅(H : InfoGeometry.Lie.CanonicalZornMathlibRootSpace.Der),
      rootDerivation i.1⁆ =
      nativeRootWeight i H •
        (rootDerivation i.1 : InfoGeometry.Lie.CanonicalZornMathlibRootSpace.Der) := by
  let k := axialCartanLieEquiv.symm H
  simpa [InfoGeometry.Lie.CanonicalZornCartanAdjointAction.adCartan_apply,
    nativeRootWeight, k] using adCartan_rootDerivation k i.1
 -/

theorem cycle_covariant_of_inner_witness
    (r : G2Root) (x y : ZornVectorMatrix ℝ)
    (h : zornDerivationRootRepresentation r =
      NativeStanDerivationBilinear.innerDerivation x y) :
    conjugateNativeDerivation realWeylCycle
        (zornDerivationRootRepresentation r) =
      NativeStanDerivationBilinear.innerDerivation
        (nativeAut realWeylCycle x) (nativeAut realWeylCycle y) := by
  rw [h]
  exact realWeylCycle_innerDerivation_covariant _ _

theorem reflection_covariant_of_inner_witness
    (r : G2Root) (x y : ZornVectorMatrix ℝ)
    (h : zornDerivationRootRepresentation r =
      NativeStanDerivationBilinear.innerDerivation x y) :
    conjugateNativeDerivation realWeylReflection
        (zornDerivationRootRepresentation r) =
      NativeStanDerivationBilinear.innerDerivation
        (nativeAut realWeylReflection x) (nativeAut realWeylReflection y) := by
  rw [h]
  exact realWeylReflection_innerDerivation_covariant _ _

theorem cycle_covariant_of_scaled_inner_witness
    (r : G2Root) (a : ℝ) (x y : ZornVectorMatrix ℝ)
    (h : zornDerivationRootRepresentation r =
      a • NativeStanDerivationBilinear.innerDerivation x y) :
    conjugateNativeDerivation realWeylCycle
        (zornDerivationRootRepresentation r) =
      a • NativeStanDerivationBilinear.innerDerivation
        (nativeAut realWeylCycle x) (nativeAut realWeylCycle y) := by
  rw [h]
  change conjugateNativeDerivationLinear realWeylCycle
      (a • NativeStanDerivationBilinear.innerDerivation x y) = _
  rw [(conjugateNativeDerivationLinear realWeylCycle).map_smul]
  simpa [conjugateNativeDerivationLinear_apply] using
    congrArg (fun D => a • D) (realWeylCycle_innerDerivation_covariant x y)

theorem reflection_covariant_of_scaled_inner_witness
    (r : G2Root) (a : ℝ) (x y : ZornVectorMatrix ℝ)
    (h : zornDerivationRootRepresentation r =
      a • NativeStanDerivationBilinear.innerDerivation x y) :
    conjugateNativeDerivation realWeylReflection
        (zornDerivationRootRepresentation r) =
      a • NativeStanDerivationBilinear.innerDerivation
        (nativeAut realWeylReflection x) (nativeAut realWeylReflection y) := by
  rw [h]
  change conjugateNativeDerivationLinear realWeylReflection
      (a • NativeStanDerivationBilinear.innerDerivation x y) = _
  rw [(conjugateNativeDerivationLinear realWeylReflection).map_smul]
  simpa [conjugateNativeDerivationLinear_apply] using
    congrArg (fun D => a • D) (realWeylReflection_innerDerivation_covariant x y)

theorem cycle_maps_root_to_scaled_inner_pair (r : G2Root) :
    ∃ (a : ℝ) (x y : ZornVectorMatrix ℝ),
      conjugateNativeDerivation realWeylCycle
          (zornDerivationRootRepresentation r) =
        a • NativeStanDerivationBilinear.innerDerivation
          (nativeAut realWeylCycle x) (nativeAut realWeylCycle y) := by
  obtain ⟨a, x, y, h⟩ := root_representation_exists_scaled_inner_witness r
  exact ⟨a, x, y, cycle_covariant_of_scaled_inner_witness r a x y h⟩

theorem reflection_maps_root_to_scaled_inner_pair (r : G2Root) :
    ∃ (a : ℝ) (x y : ZornVectorMatrix ℝ),
      conjugateNativeDerivation realWeylReflection
          (zornDerivationRootRepresentation r) =
        a • NativeStanDerivationBilinear.innerDerivation
          (nativeAut realWeylReflection x) (nativeAut realWeylReflection y) := by
  obtain ⟨a, x, y, h⟩ := root_representation_exists_scaled_inner_witness r
  exact ⟨a, x, y, reflection_covariant_of_scaled_inner_witness r a x y h⟩

/-
noncomputable def nativeCartanCycleEquiv :
    axialCartanLieSubalgebra.toSubmodule ≃ₗ[ℝ]
      axialCartanLieSubalgebra.toSubmodule :=
  nativeCartanParameterPlaneEquiv.symm.trans
    ((G2NativeWeylRootSpaceTransport.cycleCartanParameterEquiv).trans nativeCartanParameterPlaneEquiv)

noncomputable def nativeCartanReflectionEquiv :
    axialCartanLieSubalgebra.toSubmodule ≃ₗ[ℝ]
      axialCartanLieSubalgebra.toSubmodule :=
  nativeCartanParameterPlaneEquiv.symm.trans
    ((G2NativeWeylRootSpaceTransport.reflectionCartanParameterEquiv).trans nativeCartanParameterPlaneEquiv)

theorem nativeCartanCycleEquiv_apply_eq_conjugate
    (H : axialCartanLieSubalgebra.toSubmodule) :
    ((nativeCartanCycleEquiv H : axialCartanLieSubalgebra.toSubmodule) :
      canonicalZornDerivations) =
      conjugateCanonicalDerivation realWeylCycle (H : canonicalZornDerivations) := by
  apply Subtype.ext
  change ((nativeCartanParameterPlaneEquiv.symm
      ((cycleCartanParameterEquiv) (nativeCartanParameterPlaneEquiv H))) :
        canonicalZornDerivations) = _
  change ((G2NativeWeylRootSpaceTransport.cycleCartanParameterEquiv) (nativeCartanParameterPlaneEquiv H) :
      canonicalCartanParameterPlane) = _
  rw [← conjugatedParameterLieEquiv_apply]
  rfl

-/

/-
theorem nativeCartanReflectionEquiv_apply_eq_conjugate
    (H : axialCartanLieSubalgebra.toSubmodule) :
    ((nativeCartanReflectionEquiv H : axialCartanLieSubalgebra.toSubmodule) :
      canonicalZornDerivations) =
      conjugateCanonicalDerivation realWeylReflection
        (H : canonicalZornDerivations) := by
  apply Subtype.ext
  change ((nativeCartanParameterPlaneEquiv.symm
      ((reflectionCartanParameterEquiv) (nativeCartanParameterPlaneEquiv H))) :
        canonicalZornDerivations) = _
  change ((G2NativeWeylRootSpaceTransport.reflectionCartanParameterEquiv) (nativeCartanParameterPlaneEquiv H) :
      canonicalCartanParameterPlane) = _
  rw [← conjugatedParameterLieEquiv_apply]
  rfl

-/

end InfoGeometry.Algebra.Zorn.G2NativeRootPairWitnesses
