/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.CircularChiralDerivationsFourteen

/-!
# First explicit readback for the circular chiral carrier

This owner records one concrete coordinate equality between the historical
`ZornMatrix` carrier and the canonical Cartesian circular readout.  It does
not identify derivations or assert a fourteen-element basis theorem.
-/

namespace InfoGeometry.Algebra.CircularChiralCarrierReadout

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Algebra.CircularChiralCausalConeBasis
open InfoGeometry.Algebra.CircularChiralDerivationsFourteen
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
open InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.G2ChiralOperatorNativeBridge

theorem chiralReadoutBasis_sPlus_zero_readout :
    chiralReadoutBasis (.sPlus 0) =
      canonicalVectorEquiv
        (cartesianZornLinearEquiv (circularFrame 1)) := by
  simp [chiralReadoutBasis, chiralOperatorNativeReadout,
    chiralGeneratorIndex, circularBasis_apply]

theorem chiralReadoutBasis_sPlus_native_readout (i : Fin 3) :
    chiralReadoutBasis (.sPlus i) =
      InfoGeometry.Algebra.ZornVectorMatrix.U i := by
  fin_cases i
  · simpa [chiralReadoutBasis, chiralOperatorNativeReadout,
      chiralGeneratorIndex, circularBasis_apply] using circular_rootPlus_nativeU 0
  · simpa [chiralReadoutBasis, chiralOperatorNativeReadout,
      chiralGeneratorIndex, circularBasis_apply] using circular_rootPlus_nativeU 1
  · simpa [chiralReadoutBasis, chiralOperatorNativeReadout,
      chiralGeneratorIndex, circularBasis_apply] using circular_rootPlus_nativeU 2

theorem chiralReadoutBasis_pPlus_native_readout :
    chiralReadoutBasis (.pPlus) =
      InfoGeometry.Algebra.ZornVectorMatrix.E11 := by
  have h : chiralReadoutBasis (.pPlus) =
      canonicalVectorEquiv (cartesianZornLinearEquiv (circularFrame 0)) := by
    simp [chiralReadoutBasis, chiralOperatorNativeReadout,
      chiralGeneratorIndex, circularBasis_apply]
  rw [h]
  exact circular_scalarPlus_nativeE11

theorem chiralReadoutBasis_sPlus_zero_circularPeirce_readout :
    chiralReadoutBasis (.sPlus 0) =
      canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 1) := by
  simp [chiralReadoutBasis, chiralOperatorNativeReadout,
    chiralGeneratorIndex, circularBasis_apply,
    InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]

theorem chiralReadoutBasis_sMinus_zero_readout :
    chiralReadoutBasis (.sMinus 0) =
      canonicalVectorEquiv
        (cartesianZornLinearEquiv (circularFrame 5)) := by
  simp [chiralReadoutBasis, chiralOperatorNativeReadout,
    chiralGeneratorIndex, circularBasis_apply]

theorem chiralReadoutBasis_sMinus_native_readout (i : Fin 3) :
    chiralReadoutBasis (.sMinus i) =
      InfoGeometry.Algebra.ZornVectorMatrix.V i := by
  fin_cases i
  · simpa [chiralReadoutBasis, chiralOperatorNativeReadout,
      chiralGeneratorIndex, circularBasis_apply] using circular_rootMinus_nativeV 0
  · simpa [chiralReadoutBasis, chiralOperatorNativeReadout,
      chiralGeneratorIndex, circularBasis_apply] using circular_rootMinus_nativeV 1
  · simpa [chiralReadoutBasis, chiralOperatorNativeReadout,
      chiralGeneratorIndex, circularBasis_apply] using circular_rootMinus_nativeV 2

theorem chiralReadoutBasis_pMinus_native_readout :
    chiralReadoutBasis (.pMinus) =
      InfoGeometry.Algebra.ZornVectorMatrix.E22 := by
  have h : chiralReadoutBasis (.pMinus) =
      canonicalVectorEquiv (cartesianZornLinearEquiv (circularFrame 4)) := by
    simp [chiralReadoutBasis, chiralOperatorNativeReadout,
      chiralGeneratorIndex, circularBasis_apply]
  rw [h]
  exact circular_scalarMinus_nativeE22

theorem chiralReadoutBasis_sMinus_zero_circularPeirce_readout :
    chiralReadoutBasis (.sMinus 0) =
      canonicalVectorEquiv
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis 5) := by
  simp [chiralReadoutBasis, chiralOperatorNativeReadout,
    chiralGeneratorIndex, circularBasis_apply,
    InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis_apply]

theorem chiralReadoutBasis_sPlus_zero_native_readout :
    chiralReadoutBasis (.sPlus 0) =
      InfoGeometry.Algebra.ZornVectorMatrix.U 0 := by
  rw [chiralReadoutBasis_sPlus_zero_readout]
  exact circular_rootPlus_nativeU 0

theorem chiralReadoutBasis_sMinus_zero_native_readout :
    chiralReadoutBasis (.sMinus 0) =
      InfoGeometry.Algebra.ZornVectorMatrix.V 0 := by
  rw [chiralReadoutBasis_sMinus_zero_readout]
  exact circular_rootMinus_nativeV 0

theorem gaugeWitnessNativeDerivation_cartan0_readout :
    gaugeWitnessNativeDerivation
        (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan0) =
      innerDerivation
        (chiralReadoutBasis (.sPlus 0))
        (chiralReadoutBasis (.sMinus 0)) := by
  rfl

theorem gaugeWitnessNativeDerivation_cartan0_native_pair :
    gaugeWitnessNativeDerivation
        (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan0) =
      innerDerivation
        (InfoGeometry.Algebra.ZornVectorMatrix.U 0)
        (InfoGeometry.Algebra.ZornVectorMatrix.V 0) := by
  rw [gaugeWitnessNativeDerivation_cartan0_readout,
    chiralReadoutBasis_sPlus_zero_native_readout,
    chiralReadoutBasis_sMinus_zero_native_readout]

theorem gaugeWitnessNativeDerivation_cartan0_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan0)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 0)
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 0) := by
  rw [gaugeWitnessNativeDerivation_cartan0_native_pair]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_cartan1_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan1)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 1)
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 1) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.sPlus 1))
        (chiralReadoutBasis (.sMinus 1))) = _
  rw [chiralReadoutBasis_sPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_gluon01_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon01)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 0)
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 1) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.sPlus 0))
        (chiralReadoutBasis (.sMinus 1))) = _
  rw [chiralReadoutBasis_sPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_gluon02_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon02)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 0)
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 2) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.sPlus 0))
        (chiralReadoutBasis (.sMinus 2))) = _
  rw [chiralReadoutBasis_sPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_gluon10_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon10)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 1)
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 0) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.sPlus 1))
        (chiralReadoutBasis (.sMinus 0))) = _
  rw [chiralReadoutBasis_sPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_gluon12_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon12)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 1)
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 2) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.sPlus 1))
        (chiralReadoutBasis (.sMinus 2))) = _
  rw [chiralReadoutBasis_sPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_gluon20_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon20)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 2)
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 0) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.sPlus 2))
        (chiralReadoutBasis (.sMinus 0))) = _
  rw [chiralReadoutBasis_sPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_gluon21_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon21)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 2)
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 1) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.sPlus 2))
        (chiralReadoutBasis (.sMinus 1))) = _
  rw [chiralReadoutBasis_sPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_quarkUp0_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkUp0)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalE11
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 0) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.pPlus))
        (chiralReadoutBasis (.sPlus 0))) = _
  rw [chiralReadoutBasis_pPlus_native_readout,
    chiralReadoutBasis_sPlus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_quarkUp1_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkUp1)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalE11
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 1) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.pPlus))
        (chiralReadoutBasis (.sPlus 1))) = _
  rw [chiralReadoutBasis_pPlus_native_readout,
    chiralReadoutBasis_sPlus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_quarkUp2_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkUp2)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalE11
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalU 2) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.pPlus))
        (chiralReadoutBasis (.sPlus 2))) = _
  rw [chiralReadoutBasis_pPlus_native_readout,
    chiralReadoutBasis_sPlus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_quarkDown0_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkDown0)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalE11
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 0) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.pPlus))
        (chiralReadoutBasis (.sMinus 0))) = _
  rw [chiralReadoutBasis_pPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_quarkDown1_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkDown1)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalE11
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 1) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.pPlus))
        (chiralReadoutBasis (.sMinus 1))) = _
  rw [chiralReadoutBasis_pPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_quarkDown2_canonical_readout :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation
          (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkDown2)) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalE11
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalV 2) := by
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (innerDerivation (chiralReadoutBasis (.pPlus))
        (chiralReadoutBasis (.sMinus 2))) = _
  rw [chiralReadoutBasis_pPlus_native_readout,
    chiralReadoutBasis_sMinus_native_readout]
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_canonical_readout (g :
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator) :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation g) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.canonicalStandardDerivationOfCanonical
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.symm
          (chiralReadoutBasis (gaugeWitnessOperatorPair g).1))
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.symm
          (chiralReadoutBasis (gaugeWitnessOperatorPair g).2)) := by
  exact InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage.vector_inner_to_canonical _ _

theorem gaugeWitnessNativeDerivation_quarkUp0_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkUp0))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 10 (-1) := by
  rw [gaugeWitnessNativeDerivation_quarkUp0_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_E11_U0

theorem gaugeWitnessNativeDerivation_quarkUp1_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkUp1))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 9 1 := by
  rw [gaugeWitnessNativeDerivation_quarkUp1_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_E11_U1

theorem gaugeWitnessNativeDerivation_quarkUp2_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkUp2))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 4 (-1) := by
  rw [gaugeWitnessNativeDerivation_quarkUp2_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_E11_U2

theorem gaugeWitnessNativeDerivation_quarkDown0_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkDown0))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 0 1 := by
  rw [gaugeWitnessNativeDerivation_quarkDown0_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_E11_V0

theorem gaugeWitnessNativeDerivation_quarkDown1_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkDown1))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 3 1 := by
  rw [gaugeWitnessNativeDerivation_quarkDown1_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_E11_V1

theorem gaugeWitnessNativeDerivation_quarkDown2_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkDown2))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 8 1 := by
  rw [gaugeWitnessNativeDerivation_quarkDown2_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_E11_V2

theorem gaugeWitnessNativeDerivation_gluon01_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon01))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 5 (-3) := by
  rw [gaugeWitnessNativeDerivation_gluon01_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_U0_V1

theorem gaugeWitnessNativeDerivation_gluon02_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon02))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 11 (-3) := by
  rw [gaugeWitnessNativeDerivation_gluon02_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_U0_V2

theorem gaugeWitnessNativeDerivation_gluon10_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon10))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 1 (-3) := by
  rw [gaugeWitnessNativeDerivation_gluon10_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_U1_V0

theorem gaugeWitnessNativeDerivation_gluon12_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon12))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 12 (-3) := by
  rw [gaugeWitnessNativeDerivation_gluon12_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_U1_V2

theorem gaugeWitnessNativeDerivation_gluon20_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon20))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 2 (-3) := by
  rw [gaugeWitnessNativeDerivation_gluon20_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_U2_V0

theorem gaugeWitnessNativeDerivation_gluon21_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon21))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 7 (-3) := by
  rw [gaugeWitnessNativeDerivation_gluon21_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_U2_V1

theorem gaugeWitnessNativeDerivation_cartan0_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan0))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 +
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 := by
  rw [gaugeWitnessNativeDerivation_cartan0_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_U0_V0

theorem gaugeWitnessNativeDerivation_cartan1_parameter_readout :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (gaugeWitnessNativeDerivation
            (InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan1))) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 (-2) +
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 := by
  rw [gaugeWitnessNativeDerivation_cartan1_canonical_readout]
  exact InfoGeometry.Lie.SplitOctonionStandardDerivation.standardColumn_U1_V1

noncomputable def gaugeWitnessCanonicalSpan :
    Submodule ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  Submodule.span ℝ (Set.range (fun g : GaugeGenerator =>
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
      (gaugeWitnessNativeDerivation g)))

private theorem gaugeWitnessCanonical_mem_span (g : GaugeGenerator) :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation g) ∈ gaugeWitnessCanonicalSpan :=
  Submodule.subset_span ⟨g, rfl⟩

private theorem gaugeWitness_parameterUnit_mem_of_readout
    (g : GaugeGenerator) (j : Fin 14) (r : ℝ) (hr : r ≠ 0)
    (hreadout :
      InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
          (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
            (gaugeWitnessNativeDerivation g)) =
        InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit j r) :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit j) ∈
      gaugeWitnessCanonicalSpan := by
  have hm := gaugeWitnessCanonicalSpan.smul_mem r⁻¹
    (gaugeWitnessCanonical_mem_span g)
  have heq : r⁻¹ •
      InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (gaugeWitnessNativeDerivation g) =
      InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit j) := by
    apply InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm.injective
    rw [map_smul, hreadout,
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit_eq_smul]
    simp [smul_smul, hr]
  rwa [heq] at hm

theorem gaugeWitness_parameterUnit_six_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6) ∈
      gaugeWitnessCanonicalSpan := by
  let A := InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
    (gaugeWitnessNativeDerivation
      InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan0)
  let B := InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
    (gaugeWitnessNativeDerivation
      InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan1)
  have hA : A ∈ gaugeWitnessCanonicalSpan := gaugeWitnessCanonical_mem_span _
  have hB : B ∈ gaugeWitnessCanonicalSpan := gaugeWitnessCanonical_mem_span _
  have hm := gaugeWitnessCanonicalSpan.smul_mem (1 / 3 : ℝ)
    (gaugeWitnessCanonicalSpan.sub_mem hA hB)
  have heq : (1 / 3 : ℝ) • (A - B) =
      InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6) := by
    apply InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm.injective
    rw [map_smul, map_sub]
    change (1 / 3 : ℝ) •
        (InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm A -
          InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm B) = _
    rw [show InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm A =
          InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 +
            InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 by
          exact gaugeWitnessNativeDerivation_cartan0_parameter_readout,
      show InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm B =
          InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 (-2) +
            InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 by
          exact gaugeWitnessNativeDerivation_cartan1_parameter_readout]
    funext i
    by_cases h6 : i = 6 <;> by_cases h13 : i = 13 <;>
      norm_num [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
        h6, h13, Fin.ext_iff]
  rwa [heq] at hm

theorem gaugeWitness_parameterUnit_thirteen_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13) ∈
      gaugeWitnessCanonicalSpan := by
  let A := InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
    (gaugeWitnessNativeDerivation
      InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan0)
  let B := InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
    (gaugeWitnessNativeDerivation
      InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.cartan1)
  have hA : A ∈ gaugeWitnessCanonicalSpan := gaugeWitnessCanonical_mem_span _
  have hB : B ∈ gaugeWitnessCanonicalSpan := gaugeWitnessCanonical_mem_span _
  have hm := gaugeWitnessCanonicalSpan.smul_mem (1 / 3 : ℝ)
    (gaugeWitnessCanonicalSpan.add_mem
      (gaugeWitnessCanonicalSpan.smul_mem (2 : ℝ) hA) hB)
  have heq : (1 / 3 : ℝ) • ((2 : ℝ) • A + B) =
      InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13) := by
    apply InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm.injective
    rw [map_smul, map_add, map_smul]
    change (1 / 3 : ℝ) •
        (2 • InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm A +
          InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm B) = _
    rw [show InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm A =
          InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 +
            InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 by
          exact gaugeWitnessNativeDerivation_cartan0_parameter_readout,
      show InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm B =
          InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 6 (-2) +
            InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 13 by
          exact gaugeWitnessNativeDerivation_cartan1_parameter_readout]
    funext i
    by_cases h6 : i = 6 <;> by_cases h13 : i = 13 <;>
      norm_num [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
        h6, h13, Fin.ext_iff]
  rwa [heq] at hm

theorem gaugeWitness_parameterUnit_zero_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 0) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkDown0
    0 1 (by norm_num)
    gaugeWitnessNativeDerivation_quarkDown0_parameter_readout

theorem gaugeWitness_parameterUnit_one_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 1) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon10
    1 (-3) (by norm_num)
    gaugeWitnessNativeDerivation_gluon10_parameter_readout

theorem gaugeWitness_parameterUnit_two_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 2) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon20
    2 (-3) (by norm_num)
    gaugeWitnessNativeDerivation_gluon20_parameter_readout

theorem gaugeWitness_parameterUnit_three_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 3) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkDown1
    3 1 (by norm_num)
    gaugeWitnessNativeDerivation_quarkDown1_parameter_readout

theorem gaugeWitness_parameterUnit_four_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 4) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkUp2
    4 (-1) (by norm_num)
    gaugeWitnessNativeDerivation_quarkUp2_parameter_readout

theorem gaugeWitness_parameterUnit_five_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 5) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon01
    5 (-3) (by norm_num)
    gaugeWitnessNativeDerivation_gluon01_parameter_readout

theorem gaugeWitness_parameterUnit_seven_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 7) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon21
    7 (-3) (by norm_num)
    gaugeWitnessNativeDerivation_gluon21_parameter_readout

theorem gaugeWitness_parameterUnit_eight_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 8) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkDown2
    8 1 (by norm_num)
    gaugeWitnessNativeDerivation_quarkDown2_parameter_readout

theorem gaugeWitness_parameterUnit_nine_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 9) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkUp1
    9 1 (by norm_num)
    gaugeWitnessNativeDerivation_quarkUp1_parameter_readout

theorem gaugeWitness_parameterUnit_ten_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 10) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.quarkUp0
    10 (-1) (by norm_num)
    gaugeWitnessNativeDerivation_quarkUp0_parameter_readout

theorem gaugeWitness_parameterUnit_eleven_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 11) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon02
    11 (-3) (by norm_num)
    gaugeWitnessNativeDerivation_gluon02_parameter_readout

theorem gaugeWitness_parameterUnit_twelve_mem :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
        (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit 12) ∈
      gaugeWitnessCanonicalSpan := by
  exact gaugeWitness_parameterUnit_mem_of_readout
    InfoGeometry.Algebra.CircularChiralDerivationsFourteen.GaugeGenerator.gluon12
    12 (-3) (by norm_num)
    gaugeWitnessNativeDerivation_gluon12_parameter_readout

set_option synthInstance.maxHeartbeats 200000 in
theorem gaugeWitnessCanonicalSpan_eq_top :
    gaugeWitnessCanonicalSpan = ⊤ := by
  have hunit : ∀ i : Fin 14,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
          (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit i) ∈
        gaugeWitnessCanonicalSpan := by
    intro i
    fin_cases i
    · exact gaugeWitness_parameterUnit_zero_mem
    · exact gaugeWitness_parameterUnit_one_mem
    · exact gaugeWitness_parameterUnit_two_mem
    · exact gaugeWitness_parameterUnit_three_mem
    · exact gaugeWitness_parameterUnit_four_mem
    · exact gaugeWitness_parameterUnit_five_mem
    · exact gaugeWitness_parameterUnit_six_mem
    · exact gaugeWitness_parameterUnit_seven_mem
    · exact gaugeWitness_parameterUnit_eight_mem
    · exact gaugeWitness_parameterUnit_nine_mem
    · exact gaugeWitness_parameterUnit_ten_mem
    · exact gaugeWitness_parameterUnit_eleven_mem
    · exact gaugeWitness_parameterUnit_twelve_mem
    · exact gaugeWitness_parameterUnit_thirteen_mem
  apply Submodule.eq_top_iff'.mpr
  intro D
  let E := InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv
  let p : InfoGeometry.Lie.CanonicalZornDerivationDimension.Params :=
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm D
  let U : Fin 14 → InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
    fun i => E (InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit i)
  have hp : p = ∑ i : Fin 14, p i •
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit i := by
    funext j
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit]
  have hD : D = Finset.univ.sum (fun i : Fin 14 => (p i : ℝ) • U i) := by
    rw [← E.apply_symm_apply D]
    change E p = _
    calc
      E p =
          E
            (∑ i : Fin 14, p i •
              InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit i) :=
        congrArg InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv hp
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul]
  rw [hD]
  exact Submodule.sum_mem gaugeWitnessCanonicalSpan
    (fun i _ => gaugeWitnessCanonicalSpan.smul_mem _ (hunit i))

noncomputable def gaugeWitnessNativeSpan :
    Submodule ℝ (InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)) :=
  Submodule.span ℝ (Set.range gaugeWitnessNativeDerivation)

theorem gaugeWitnessNativeSpan_eq_top :
    gaugeWitnessNativeSpan = ⊤ := by
  let E := InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
  have hmap : gaugeWitnessNativeSpan.map
      (E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ) →ₗ[ℝ]
        InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) = ⊤ := by
    rw [gaugeWitnessNativeSpan, Submodule.map_span]
    change Submodule.span ℝ
      (E '' Set.range gaugeWitnessNativeDerivation) = ⊤
    rw [← Set.range_comp]
    change Submodule.span ℝ
      (Set.range (fun g : GaugeGenerator => E (gaugeWitnessNativeDerivation g))) = ⊤
    exact gaugeWitnessCanonicalSpan_eq_top
  apply Submodule.eq_top_iff'.mpr
  intro D
  have hD : E (D : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)) ∈
      gaugeWitnessNativeSpan.map (E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ) →ₗ[ℝ]
        InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) := by
    rw [hmap]
    exact Submodule.mem_top
  obtain ⟨D', hD', hEq⟩ := hD
  have : D' = D := by
    apply E.injective
    simpa using hEq
  simpa [this] using hD'

theorem zornMatrixToCanonical_uPlus_readout :
    zornMatrixToCanonical (toZorn ℝ ChiralBasis.uPlus) =
      cartesianZornLinearEquiv (circularFrame 0) := by
  rw [show circularFrame 0 = scalarPlus by rfl]
  rw [cartesianZorn_scalarPlus]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem zornMatrixToCanonical_uMinus_readout :
    zornMatrixToCanonical (toZorn ℝ ChiralBasis.uMinus) =
      cartesianZornLinearEquiv (circularFrame 4) := by
  rw [show circularFrame 4 = scalarMinus by rfl]
  rw [cartesianZorn_scalarMinus]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem zornMatrixToCanonical_up_zero_readout :
    zornMatrixToCanonical (toZorn ℝ (ChiralBasis.up 0)) =
      cartesianZornLinearEquiv (circularFrame 1) := by
  rw [show circularFrame 1 = rootPlus 0 by rfl]
  rw [cartesianZorn_rootPlus]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem zornMatrixToCanonical_up_one_readout :
    zornMatrixToCanonical (toZorn ℝ (ChiralBasis.up 1)) =
      cartesianZornLinearEquiv (circularFrame 2) := by
  rw [show circularFrame 2 = rootPlus 1 by rfl]
  rw [cartesianZorn_rootPlus]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem zornMatrixToCanonical_up_two_readout :
    zornMatrixToCanonical (toZorn ℝ (ChiralBasis.up 2)) =
      cartesianZornLinearEquiv (circularFrame 3) := by
  rw [show circularFrame 3 = rootPlus 2 by rfl]
  rw [cartesianZorn_rootPlus]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem zornMatrixToCanonical_down_zero_readout :
    zornMatrixToCanonical (toZorn ℝ (ChiralBasis.down 0)) =
      cartesianZornLinearEquiv (circularFrame 5) := by
  rw [show circularFrame 5 = rootMinus 0 by rfl]
  rw [cartesianZorn_rootMinus]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem zornMatrixToCanonical_down_one_readout :
    zornMatrixToCanonical (toZorn ℝ (ChiralBasis.down 1)) =
      cartesianZornLinearEquiv (circularFrame 6) := by
  rw [show circularFrame 6 = rootMinus 1 by rfl]
  rw [cartesianZorn_rootMinus]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem zornMatrixToCanonical_down_two_readout :
    zornMatrixToCanonical (toZorn ℝ (ChiralBasis.down 2)) =
      cartesianZornLinearEquiv (circularFrame 7) := by
  rw [show circularFrame 7 = rootMinus 2 by rfl]
  rw [cartesianZorn_rootMinus]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

end InfoGeometry.Algebra.CircularChiralCarrierReadout
