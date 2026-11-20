/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Superalgebra.RealGradedZornCARBridge
import InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge

/-!
# Shared real carrier synthesis: circular CAR and Peirce translations

Both constructions act on the same real doubled-Krein carrier through the
three-factor Koszul-graded product of real `2 × 2` matrices. At unit time-like
momentum, their anticommutators have the same value, the identity. This is an
operator-level comparison of anticommutators; it does not identify the two
charge pairs term by term.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealChiralCARTranslationSynthesis

open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open InfoGeometry.Canonical.SplitCliffordTowerUnification
open InfoGeometry.Canonical.RealTetractysTranslationSolderingBridge
open InfoGeometry.Superalgebra.RealGradedZornCARBridge
open InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge
open InfoGeometry.Lie.SplitOctonionEllPolarization
open Matrix

local notation "FourSpace" => InfoGeometry.Canonical.RealDoubledChiralKreinFrame.FourSpace

/-- The unit time-like vector in the real `FourSpace` coordinate convention. -/
def unitTimeMomentum : FourSpace :=
  fourSpaceEquivVec22.symm (1, 0, 0, 0)

/-- Real Pauli soldering sends unit time momentum to the identity matrix. -/
theorem realMomentum_unitTime : realMomentum unitTimeMomentum = 1 := by
  unfold realMomentum unitTimeMomentum
  rw [fourSpaceEquivVec22.apply_symm_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Clifford.Soldering.soldering,
    InfoGeometry.Clifford.Soldering.sigma0,
    InfoGeometry.Clifford.Soldering.sigma1,
    InfoGeometry.Clifford.Soldering.sigma3,
    InfoGeometry.Clifford.Soldering.epsilon]

/-- The diagonal momentum block at unit time is the identity on the two
Peirce sheets. -/
theorem diagonalMomentumOperator_unitTime :
    diagonalMomentumOperator unitTimeMomentum =
      (1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ)) := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [diagonalMomentumOperator, realMomentum_unitTime,
      Matrix.zero_apply]

/-- The three-mode doubled-Krein representation of unit-time diagonal
momentum is the identity operator. -/
theorem realThreeKrein_unitTimeMomentum_is_one :
    realThreeMatrixTensorOnH4 (twoModeIntoThreeMode
      (twoMatrixGradedTensorMoritaEquiv.symm
        (diagonalMomentumOperator unitTimeMomentum))) = 1 := by
  rw [diagonalMomentumOperator_unitTime]
  simp

/-- On the common real doubled-Krein carrier, the circular split-octonion
root CAR anticommutator equals the anticommutator of the real Peirce
translation and its complementary charge at unit time-like momentum.

The theorem identifies the resulting operator-valued momentum readout (the
identity at this normalized point), not the individual root and translation
operators. -/
theorem circularRootCAR_matches_unitTime_translation (i : Fin 3) :
    realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootMinus i))) *
        realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootPlus i))) +
      realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootPlus i))) *
        realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor (rootMinus i))) =
      realThreeMatrixTensorOnH4
          (twoModeIntoThreeMode (translationInGradedTensor unitTimeMomentum)) *
        realThreeMatrixTensorOnH4
          (twoModeIntoThreeMode conjugatePeirceCharge) +
      realThreeMatrixTensorOnH4
          (twoModeIntoThreeMode conjugatePeirceCharge) *
        realThreeMatrixTensorOnH4
          (twoModeIntoThreeMode (translationInGradedTensor unitTimeMomentum)) := by
  rw [threeMode_supercolor_root_CAR i,
    realThreeKrein_translationCharge_anticommutator_eq_diagonalMomentum,
    realThreeKrein_unitTimeMomentum_is_one]

end InfoGeometry.Canonical.RealChiralCARTranslationSynthesis
