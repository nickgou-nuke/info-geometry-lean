/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCylinderStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNonSeparatingBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical interface for the concrete boundary matrix-stage morphism

The operator-algebra owners construct the genuine finite-stage `StarAlgHom`.
This file exposes that construction under the canonical generator-level names
used by the matrix-tower contract.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialCylinderStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNonSeparatingBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge

abbrev Stage (n : ℕ) := BitWordMatrixStage n

abbrev BoundaryOperator :=
  InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.BoundedL2Operator

def boundaryRep (n : ℕ) : Stage n →⋆ₐ[ℂ] BoundaryOperator :=
  bitWordMatrixStarRepresentation n

def correspondingCuntzWord (n : ℕ) (i j : BitWord n) : BoundaryOperator :=
  bitWordUnit n i j

theorem matrixUnit_generator_transport (n : ℕ) (i j : BitWord n) :
    boundaryRep n (Matrix.single i j 1) = correspondingCuntzWord n i j := by
  exact bitWordMatrixStarRepresentation_apply_single n i j

/-! The finite boundary representation is a genuinely noncommutative matrix
readout.  In particular, its definition is controlled by every matrix unit,
not only by the diagonal cylinder projections. -/

theorem boundaryRep_matrix_unit_expansion
    (n : ℕ) (A : Stage n) :
    boundaryRep n A =
      ∑ u : BitWord n, ∑ v : BitWord n,
        A u v • correspondingCuntzWord n u v := by
  rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hA :
      (∑ i, ∑ j, Matrix.single i j (A i j)) u v = A u v := by
    exact congrArg (fun M => M u v) (Matrix.matrix_eq_sum_single A).symm
  rw [hA]
  rw [show Matrix.single u v (A u v) =
      A u v • Matrix.single u v (1 : ℂ) by
        ext i j
        simp [Matrix.single]]
  rw [map_smul, matrixUnit_generator_transport]

/-- The finite matrix representation sends every diagonal matrix to the
corresponding finite linear combination of Cuntz cylinder projections. -/
theorem boundaryRep_diagonal (n : ℕ) (f : BitWord n → ℂ) :
    boundaryRep n (Matrix.diagonal f) =
      ∑ u : BitWord n, f u • operatorCylinderProjection (List.ofFn u) := by
  rw [show Matrix.diagonal f =
      ∑ u : BitWord n, Matrix.single u u (f u) by
        rw [← Matrix.sum_single_eq_diagonal f]]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [show Matrix.single u u (f u) =
      f u • Matrix.single u u (1 : ℂ) by
        ext i j
        simp [Matrix.single]]
  simp only [map_smul, matrixUnit_generator_transport,
    correspondingCuntzWord, bitWordUnit_diag_eq_projection]

/-- The spatial Bernoulli vector state restricted to the represented finite
diagonal matrix stage is the normalized matrix trace. -/
theorem spatialState_boundaryRep_diagonal_eq_matrixTrace
    (n : ℕ) (f : BitWord n → ℂ) :
    spatialState.functional (boundaryRep n (Matrix.diagonal f)) =
      bitWordMatrixTraceFunctional n (Matrix.diagonal f) := by
  calc
    spatialState.functional (boundaryRep n (Matrix.diagonal f)) =
        bitWordMatrixGaugeReadout n (Matrix.diagonal f) := by
      rw [boundaryRep_diagonal]
      change spatialState.functional
          (∑ u : BitWord n,
            f u • operatorCylinderProjection (List.ofFn u)) = _
      rw [map_sum]
      simp_rw [map_smul,
        spatialState_eq_canonicalGaugeState_on_projection]
      simp [bitWordMatrixGaugeReadout, Matrix.diagonal]
    _ = bitWordMatrixTraceFunctional n (Matrix.diagonal f) :=
      bitWordMatrixGaugeReadout_eq_trace n (Matrix.diagonal f)

/-! The spatial boundary vector state is not the normalized matrix trace on the
full finite matrix carrier.  This is the canonical matrix-stage form of the
off-diagonal separation theorem; it prevents extending the diagonal theorem
above to arbitrary matrices. -/

theorem spatialState_boundaryRep_offDiagonal_ne_matrixTrace :
    spatialState.functional
        (boundaryRep 1
          (Matrix.single (fun _ : Fin 1 => false) (fun _ : Fin 1 => true) 1)) ≠
      bitWordMatrixTraceFunctional 1
        (Matrix.single (fun _ : Fin 1 => false) (fun _ : Fin 1 => true) 1) := by
  rw [matrixUnit_generator_transport]
  change cantorVacuumState (vLeft * star vRight) ≠ _
  have hne : (fun _ : Fin 1 => false) ≠ (fun _ : Fin 1 => true) := by
    intro h
    have h0 := congrFun h ⟨0, by omega⟩
    cases h0
  rw [spatialState_offDiagonal_generator,
    bitWordMatrixTraceFunctional_single]
  simp [hne]

/-! The spatial vacuum readout of a matrix unit is not the gauge matrix-unit
    coefficient.  This is proved on arbitrary words of one common length. -/

lemma prependBitLp_vacuum_eq (b : Bool) :
    prependBitLp b vacuumL2 = vacuumL2 := by
  apply MeasureTheory.Lp.ext
  dsimp [prependBitLp, prependBitFunction]
  have hpre := (prependBitFunction_memLp b vacuumL2).coeFn_toLp
  have hvac := vacuumL2_coeFn
  have hcomp := vacuumL2_comp_prependBit b
  filter_upwards [hpre, hvac, hcomp] with x hprex hvacx hcompx
  rw [hprex]
  change (vacuumL2 : Boundary → ℂ) (CuntzCantorBoundaryShift.prependBit b x) =
    (vacuumL2 : Boundary → ℂ) x
  rw [hcompx, hvacx]

lemma operatorWordDag_vacuum (w : List Bool) :
    operatorWordDag w vacuumL2 =
      (prependBitLpNormFactor : ℂ) ^ w.length • vacuumL2 := by
  induction w with
  | nil => simp [operatorWordDag]
  | cons b w ih =>
      cases b with
      | false =>
          change operatorWordDag w ((star vLeft) vacuumL2) = _
          rw [show (star vLeft) vacuumL2 =
            (prependBitLpNormFactor : ℂ) • prependBitLp false vacuumL2 by
              exact normalizedPrependBitLpAdjoint_apply false vacuumL2]
          rw [prependBitLp_vacuum_eq, map_smul, ih]
          simp [pow_succ, smul_smul, mul_comm]
      | true =>
          change operatorWordDag w ((star vRight) vacuumL2) = _
          rw [show (star vRight) vacuumL2 =
            (prependBitLpNormFactor : ℂ) • prependBitLp true vacuumL2 by
              exact normalizedPrependBitLpAdjoint_apply true vacuumL2]
          rw [prependBitLp_vacuum_eq, map_smul, ih]
          simp [pow_succ, smul_smul, mul_comm]

theorem spatialState_correspondingCuntzWord_eq
    (n : ℕ) (i j : BitWord n) :
    spatialState.functional (correspondingCuntzWord n i j) =
      (1 / 2 : ℂ) ^ n := by
  change cantorVacuumState (operatorMatrixUnit (List.ofFn i) (List.ofFn j)) = _
  unfold cantorVacuumState operatorMatrixUnit
  change inner ℂ vacuumL2
    (operatorWord (List.ofFn i)
      (operatorWordDag (List.ofFn j) vacuumL2)) = _
  rw [← ContinuousLinearMap.adjoint_inner_left (operatorWord (List.ofFn i))]
  rw [← ContinuousLinearMap.star_eq_adjoint,
    ← operatorWordDag_eq_star (List.ofFn i),
    operatorWordDag_vacuum, operatorWordDag_vacuum]
  rw [inner_smul_left, inner_smul_right, vacuumL2_inner_self]
  have hlen : (List.ofFn i).length = n := by simp
  have hlen' : (List.ofFn j).length = n := by simp
  rw [hlen, hlen']
  simp only [Complex.conj_ofReal, map_pow, mul_one]
  rw [← mul_pow, ← pow_two]
  rw [show (prependBitLpNormFactor : ℂ) ^ 2 = (1 / 2 : ℂ) by
    rw [← Complex.ofReal_pow, prependBitLpNormFactor_sq]
    norm_num]

theorem spatialState_boundaryRep_eq_uniformMatrixCoefficientSum
    (n : ℕ) (A : Stage n) :
    spatialState.functional (boundaryRep n A) =
      (1 / 2 : ℂ) ^ n * ∑ u : BitWord n, ∑ v : BitWord n, A u v := by
  rw [boundaryRep_matrix_unit_expansion]
  simp only [map_sum, map_smul]
  simp_rw [spatialState_correspondingCuntzWord_eq, smul_eq_mul]
  calc
    (∑ u : BitWord n, ∑ v : BitWord n, A u v * (1 / 2 : ℂ) ^ n) =
        ∑ u : BitWord n, (∑ v : BitWord n, A u v) * (1 / 2 : ℂ) ^ n := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_mul]
    _ = (∑ u : BitWord n, ∑ v : BitWord n, A u v) * (1 / 2 : ℂ) ^ n := by
      rw [Finset.sum_mul]
    _ = (1 / 2 : ℂ) ^ n * ∑ u : BitWord n, ∑ v : BitWord n, A u v := by
      ring

theorem boundaryRep_bond_compatible (n : ℕ) (A : Stage n) :
    boundaryRep n A = boundaryRep (n + 1) (dyadicMatrixEmbedding n A) := by
  exact bitWordMatrixStarRepresentation_refinement n A

theorem boundaryRep_matrixUnit_bond_compatible (n : ℕ) (i j : BitWord n) :
    correspondingCuntzWord n i j =
      boundaryRep (n + 1)
        (dyadicMatrixEmbedding n (Matrix.single i j 1)) := by
  rw [← matrixUnit_generator_transport n i j]
  exact boundaryRep_bond_compatible n (Matrix.single i j 1)

end InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
