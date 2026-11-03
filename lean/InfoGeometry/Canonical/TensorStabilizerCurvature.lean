/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorLieStabilizerTransport
import InfoGeometry.Canonical.TensorExactCurvatureNonzero

/-! # The cut stabilizer and exact CE curvature

The exact one-form `dP` vanishes on derivations stabilizing the cut; the
curvature consequently vanishes when either argument is in the stabilizer.
The dense matrix witness shows that the curvature is not identically zero.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorStabilizerCurvature

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorLieStabilizerTransport
open InfoGeometry.Canonical.TensorExactCurvatureNonzero
open InfoGeometry.Examples.RealMatrixModeWitness

/-- Every cut-stabilizing derivation annihilates the exact curvature in its
first argument, against an arbitrary algebraic derivation direction. -/
theorem exactCurvature_zero_of_left_stabilizer (P : Limit)
    (D E : limitDerivationsLane.L) (hD : D ∈ limitCutStabilizer P) :
    connectionCurvature limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) D E = 0 := by
  rw [limit_exactCurvature_all_directions]
  change D.1 P = 0 at hD
  change D.1 P * E.1 P - E.1 P * D.1 P = 0
  rw [hD, zero_mul, mul_zero, sub_self]

/-- The same kernel statement holds in the second curvature argument. -/
theorem exactCurvature_zero_of_right_stabilizer (P : Limit)
    (D E : limitDerivationsLane.L) (hE : E ∈ limitCutStabilizer P) :
    connectionCurvature limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) D E = 0 := by
  rw [limit_exactCurvature_all_directions]
  change E.1 P = 0 at hE
  change D.1 P * E.1 P - E.1 P * D.1 P = 0
  rw [hE, zero_mul, mul_zero, sub_self]

/-- A stabilizing direction has zero covariant-derivation commutator defect
against every other derivation and every colimit element. -/
theorem covariant_commutator_flat_along_stabilizer (P a : Limit)
    (D E : limitDerivationsLane.L) (hD : D ∈ limitCutStabilizer P) :
    covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) D
        (covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) E a) -
      covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) E
        (covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P) D a) -
      covariantDerivative limitDerivationsLane (exteriorDerivativeZero limitDerivationsLane P)
        ⁅D, E⁆ a = 0 := by
  rw [covariantDerivative_commutator, exactCurvature_zero_of_left_stabilizer P D E hD,
    zero_mul, mul_zero, sub_self]

/-- The two dense witness directions both lie outside the stabilizer, as
forced by their previously proved nonzero exact CE curvature. -/
theorem dense_nonzero_curvature_excludes_stabilizer :
    limitInnerLieHom (ofStage 2 x) ∉ limitCutStabilizer (ofStage 2 p) ∧
      limitInnerLieHom (ofStage 2 (star x)) ∉ limitCutStabilizer (ofStage 2 p) := by
  constructor
  · intro h
    apply denseMode_limitExactCurvature_ne_zero
    exact exactCurvature_zero_of_left_stabilizer _ _ _ h
  · intro h
    apply denseMode_limitExactCurvature_ne_zero
    exact exactCurvature_zero_of_right_stabilizer _ _ _ h

end InfoGeometry.Canonical.TensorStabilizerCurvature

end
