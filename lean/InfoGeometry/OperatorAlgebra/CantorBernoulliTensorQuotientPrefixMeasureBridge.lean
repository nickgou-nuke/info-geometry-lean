/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCylinderStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderProjectionBridge
import InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
import InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
import InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalGNSBridge

/-!
# Tensor-quotient diagonal matrix units and projective-prefix mass

This theorem composes the existing quotient representation, its finite
matrix-unit readback, the spatial-state cylinder readout, and the Bernoulli
prefix-fiber mass.  It concerns diagonal matrix units only; it does not
identify the spatial vector state with the gauge-KMS state on arbitrary Cuntz
words, nor assert star preservation of the algebraic quotient map.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge

open InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderProjectionBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCylinderStateBridge
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalGNSBridge

/-- The spatial state of the represented diagonal matrix unit from the actual
binary Cuntz tensor quotient is the Bernoulli mass of the corresponding
projective-limit prefix fiber. -/
theorem tensorQuotient_diagonalUnit_spatialState_eq_prefixFiberMass
    (n : ℕ) (u : Fin n → Bool) :
    spatialState.functional
        (cantorBernoulliTensorLift
          (cuntzWordShift
              (List.ofFn fun i : Fin n => finTwoEquivBool.symm (u i)) *
            cuntzWordShiftDag
              (List.ofFn fun i : Fin n => finTwoEquivBool.symm (u i)))) =
      ((projectiveLimitMeasure {q : PrefixProjectiveLimit | π n q = u}).toReal : ℂ) := by
  rw [cantorBernoulliTensorLift_bitWordMatrixUnit,
    bitWordUnit_diag_eq_projection,
    spatialState_operatorCylinderProjection_word]
  congr 1
  rw [μC_wordBranchSet, List.length_ofFn,
    projectiveLimitMeasure_apply_prefix_fiber]

open InfoGeometry.Physics.ComplexStarCuntzRedesign

/-- The word shift in the conjugate-linear-star complexification of the real
Cuntz quotient. -/
def complexStarWord : List Bool → ComplexStarCuntzAlg Bool
  | [] => 1
  | b :: w => Sℂ b * complexStarWord w

/-- The genuine complex star-algebra lift sends a source word shift to the
corresponding concrete Bernoulli branch operator. -/
theorem cantorBernoulliComplexStarLift_word (w : List Bool) :
    cantorBernoulliComplexStarLift (complexStarWord w) =
      InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWord w := by
  induction w with
  | nil =>
      simp only [complexStarWord, map_one]
      simp [InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWord,
        ContinuousLinearMap.one_def]
  | cons b w ih =>
      rw [complexStarWord, map_mul,
        InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge.cantorBernoulliComplexStarLift_Sℂ,
        ih]
      rfl

/-! The corrected quotient also reads arbitrary word-pair matrix units, not
    only diagonal cylinder projections.  The finite `BitWord` specialization
    is the off-diagonal companion
    to the diagonal bridge below and reuses the existing `complexStarWord`
    owner rather than introducing a second word representation. -/

theorem complexStarQuotient_word_pair_eq_boundaryMatrixUnit
    (u v : List Bool) :
    cantorBernoulliComplexStarLift
        (complexStarWord u * star (complexStarWord v)) =
      operatorMatrixUnit u v := by
  rw [map_mul, cantorBernoulliComplexStarLift_word, map_star,
    cantorBernoulliComplexStarLift_word]
  rw [← operatorWordDag_eq_star]
  rfl

theorem complexStarQuotient_bitWordMatrixUnit_eq_boundaryMatrixUnit
    (n : ℕ) (u v : Fin n → Bool) :
    cantorBernoulliComplexStarLift
        (complexStarWord (List.ofFn u) *
          star (complexStarWord (List.ofFn v))) =
      bitWordUnit n u v := by
  rw [complexStarQuotient_word_pair_eq_boundaryMatrixUnit]
  rfl

/-- The corrected complexified-real quotient's diagonal word projection has
the Bernoulli mass of the corresponding projective-limit prefix fiber after
the concrete representation and spatial-state readout. This is a statement
about the represented spatial state on diagonal words, not a gauge-KMS state
extension on the full quotient. -/
theorem complexStarQuotient_diagonalWord_spatialState_eq_prefixFiberMass
    (n : ℕ) (u : Fin n → Bool) :
    spatialState.functional
        (cantorBernoulliComplexStarLift
          (complexStarWord (List.ofFn u) *
            star (complexStarWord (List.ofFn u)))) =
      ((projectiveLimitMeasure {q : PrefixProjectiveLimit | π n q = u}).toReal : ℂ) := by
  rw [map_mul, map_star,
    cantorBernoulliComplexStarLift_word]
  rw [← InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWordDag_eq_star]
  change spatialState.functional
    (InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorCylinderProjection
      (List.ofFn u)) = _
  rw [spatialState_operatorCylinderProjection_word]
  congr 1
  rw [μC_wordBranchSet, List.length_ofFn,
    projectiveLimitMeasure_apply_prefix_fiber]

/-- The proper complex-* quotient's represented diagonal word agrees as a
bounded operator with the corresponding finite BitWord matrix-unit image.
This is an operator-readout equality between the two carriers, not a map from
the full Cuntz quotient into the UHF matrix stage. -/
theorem complexStarQuotient_diagonalWord_eq_boundaryMatrixUnit
    (n : ℕ) (u : Fin n → Bool) :
    cantorBernoulliComplexStarLift
        (complexStarWord (List.ofFn u) *
          star (complexStarWord (List.ofFn u))) =
      InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.boundaryRep n
        (Matrix.single u u (1 : ℂ)) := by
  rw [map_mul, map_star,
    cantorBernoulliComplexStarLift_word]
  rw [← InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWordDag_eq_star]
  change InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorCylinderProjection
      (List.ofFn u) =
    InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.boundaryRep n
      (Matrix.single u u (1 : ℂ))
  rw [InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.matrixUnit_generator_transport,
    InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.correspondingCuntzWord,
    InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge.bitWordUnit_diag_eq_projection]

/-- Every finite diagonal matrix readout is the represented image of the same
finite sum of diagonal word projections in the proper complex-* quotient.
Thus the corrected quotient, the finite BitWord diagonal stage, and their
concrete boundary representation agree on the entire finite diagonal stage. -/
theorem complexStarQuotient_diagonalStage_eq_boundaryRep
    (n : ℕ) (f : InfoGeometry.Canonical.UHFInductiveColimitBoundary.DiagAlg n) :
    (∑ u : InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord n, f u •
      cantorBernoulliComplexStarLift
        (complexStarWord (List.ofFn u) *
          star (complexStarWord (List.ofFn u)))) =
      InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.boundaryRep n
        (Matrix.diagonal f) := by
  rw [InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.boundaryRep_diagonal]
  apply Finset.sum_congr rfl
  intro u hu
  rw [complexStarQuotient_diagonalWord_eq_boundaryMatrixUnit]
  rw [InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.matrixUnit_generator_transport,
    InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.correspondingCuntzWord,
    InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge.bitWordUnit_diag_eq_projection]

/-- The represented finite diagonal observable from the proper complex-*
quotient has the projective-limit Bernoulli integral as its spatial-state
readout. This composes the finite-stage carrier comparison with the existing
UHF trace/projective-integral theorem. -/
theorem complexStarQuotient_diagonalStage_spatialState_eq_projectiveIntegral
    (n : ℕ) (f : InfoGeometry.Canonical.UHFInductiveColimitBoundary.DiagAlg n) :
    spatialState.functional
        (∑ u : InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord n, f u •
          cantorBernoulliComplexStarLift
            (complexStarWord (List.ofFn u) *
              star (complexStarWord (List.ofFn u)))) =
      ∫ q, f (π n q) ∂projectiveLimitMeasure := by
  rw [complexStarQuotient_diagonalStage_eq_boundaryRep]
  exact spatialState_boundaryRep_diagonal_projective_integral n f

end InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
