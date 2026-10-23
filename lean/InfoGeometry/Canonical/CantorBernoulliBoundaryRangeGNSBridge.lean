/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
import InfoGeometry.Canonical.ConcreteCompatibleCuntzFaithfulness
import InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
import InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge
import InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy
import InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalHilbertSchmidt

/-!
# Finite boundary range and native GNS trace

The concrete boundary representation and the native filtered GNS representation
have different ambient operator spaces.  This owner compares them on their
common finite matrix source by passing through the actual range of the
boundary representation.  It does not identify the spatial boundary vector
state with the gauge state; those states are different on off-diagonal words.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.CantorBernoulliBoundaryRangeGNSBridge

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.Canonical.ConcreteCompatibleCuntzFaithfulness
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalHilbertSchmidt
open scoped ComplexOrder InnerProductSpace

abbrev Stage (n : ℕ) := BitWordMatrixStage n

abbrev BoundaryRange (n : ℕ) :=
  LinearMap.range (bitWordMatrixLinearRepresentation n)

def boundaryRangeEquiv (n : ℕ) :
    Stage n ≃ₗ[ℂ] BoundaryRange n :=
  LinearEquiv.ofBijective
    (bitWordMatrixLinearRepresentation n).rangeRestrict
    ⟨by
      intro A B h
      apply bitWordMatrixLinearRepresentation_injective n
      exact congrArg Subtype.val h,
      LinearMap.surjective_rangeRestrict _⟩

def boundaryRangeElement (n : ℕ) (A : Stage n) : BoundaryRange n :=
  ⟨boundaryRep n A, ⟨A, rfl⟩⟩

def boundaryRangeTrace (n : ℕ) : BoundaryRange n →ₗ[ℂ] ℂ :=
  (bitWordMatrixTraceFunctional n).comp
    (boundaryRangeEquiv n).symm.toLinearMap

theorem boundaryRangeTrace_stage (n : ℕ) (A : Stage n) :
    boundaryRangeTrace n (boundaryRangeElement n A) =
      bitWordMatrixTraceFunctional n A := by
  rw [boundaryRangeTrace]
  change bitWordMatrixTraceFunctional n
    ((boundaryRangeEquiv n).symm (boundaryRangeElement n A)) = _
  rw [show boundaryRangeElement n A = boundaryRangeEquiv n A by rfl]
  simp

/-! The pulled-back trace on the actual boundary range is compatible with the
native full-matrix `StarAlgHom` successor.  This statement is about arbitrary
matrix stages: no diagonalization, normality, or eigenbasis is used. -/

theorem boundaryRangeTrace_starTransition
    (n : ℕ) (A : Stage n) :
    boundaryRangeTrace (n + 1)
        (boundaryRangeElement (n + 1)
          (bitWordDyadicStarEmbedding n A)) =
      boundaryRangeTrace n (boundaryRangeElement n A) := by
  rw [boundaryRangeTrace_stage, boundaryRangeTrace_stage]
  exact bitWordDyadicStarEmbedding_trace_compatible n A

/-! The projective-limit measure sees the diagonal readout of an arbitrary
finite matrix through the normalized trace.  The source remains the full
noncommutative matrix stage; only this scalar functional factors through
`diagonalPart`. -/

theorem boundaryRangeTrace_projectiveDiagonalReadout
    (n : ℕ) (A : Stage n) :
    boundaryRangeTrace n (boundaryRangeElement n A) =
      ∫ q, diagonalPart n A (π n q) ∂projectiveLimitMeasure := by
  rw [boundaryRangeTrace_stage]
  calc
    bitWordMatrixTraceFunctional n A =
        bitWordMatrixTraceFunctional n
          (Matrix.diagonal (diagonalPart n A)) := by
      rw [bitWordMatrixTraceFunctional_apply,
        bitWordMatrixTraceFunctional_apply]
      simp [Matrix.trace, diagonalPart]
    _ = DiagTrace n (diagonalPart n A) :=
      bitWordMatrixTraceFunctional_diagonal n (diagonalPart n A)
    _ = ∫ q, diagonalPart n A (π n q) ∂projectiveLimitMeasure :=
      (projectiveLimitMeasure_integral_prefix_eq_DiagTrace n
        (diagonalPart n A)).symm

/-! The same finite-stage trace is recovered by the native GNS colimit on
every matrix, including nonnormal and nondiagonalizable matrices. -/

theorem boundaryRangeTrace_gaugeGNS_readout (n : ℕ) (A : Stage n) :
    boundaryRangeTrace n (boundaryRangeElement n A) =
      ⟪gaugeGNSColimitVacuum,
        globalStageRepresentationStarAlgHom
          gaugeStage gaugeSystem gaugeStateFamily n
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n A))
          gaugeGNSColimitVacuum⟫_ℂ := by
  rw [boundaryRangeTrace_stage]
  calc
    bitWordMatrixTraceFunctional n A =
        bitWordMatrixGaugeReadout n A :=
      (bitWordMatrixGaugeReadout_eq_trace n A).symm
    _ = complexStarFiniteStageTrace n A := by
      rw [complexStarFiniteStageTrace_eq_matrixTrace,
        bitWordMatrixGaugeReadout_eq_trace]
    _ =
        ⟪gaugeGNSColimitVacuum,
          globalStageRepresentationStarAlgHom
            gaugeStage gaugeSystem gaugeStateFamily n
            (CStarMatrix.ofMatrixStarAlgEquiv
              (bitWordStageStarAlgEquiv n A))
            gaugeGNSColimitVacuum⟫_ℂ :=
      (gaugeGNSColimitVacuum_complexStarFiniteStage_expectation n A).symm

end InfoGeometry.Canonical.CantorBernoulliBoundaryRangeGNSBridge
