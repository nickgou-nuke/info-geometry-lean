/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSMatrixAnalyticKMS

/-!
# Analytic KMS correlations of the completed finite-seed Gibbs state

The state, Hilbert space, operator algebra, and real-time flow are the existing
filtered GNS constructions.  This file specializes the proved native analytic
assembly and discharges its algebraic twisted premise from the actual Gibbs
state.  No KMS identity, state invariance, or analytic continuation is assumed.

The proof-valued definitions below are inferred specializations of the named
generic theorems.  Their argument order and conclusions are preserved without
reconstructing normed dictionaries for the fully expanded finite-seed state.
The bounded Gibbs density unit is not identified with a standard-form modular
operator or with an unbounded thermodynamic-limit generator.
-/

noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSVacuumReadback
open CStarStateColimit.Native.FilteredGNSMatrixAnalyticKMS
open CuntzMatrixTowerInstantiation CantorBernoulliCStarMatrixTraceState
open FiniteMatrixGibbsFunctional FiniteSeedRepresentedKMS FiniteSeedRepresentedRealTime
open AlgebraicKMSStateColimit

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

variable {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
local notation "ωseed" => finiteSeedCompatibleStageStates H hH β

/-- The existing operator-norm closure of the represented algebraic colimit. -/
abbrev Carrier : Type :=
  representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem ωseed

/-- The existing normalized positive vacuum functional on that same carrier. -/
def seedFunctional (v : ℕ) :=
  representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem ωseed v

def seedComplexTime :=
  matrixComplexTime CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH

def seedCorrelation :=
  matrixCorrelation CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH

/-- Specialization of the proved native mapped-density exponential theorem. -/
def representedDensityUnit_eq_exp :=
  matrixDensityUnit_eq_exp CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH β

/-- Specialization of the proved inverse-density exponential theorem. -/
def representedDensityUnit_inv_eq_exp :=
  matrixDensityUnit_inv_eq_exp CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH β

/-- The generic algebraic premise is discharged by the actual finite-seed
Gibbs-colimit theorem and the existing native density-unit alignment. -/
def seedFunctional_twisted (v : ℕ) :=
  matrixFunctionalTwisted_of_algebraic CStarMatrixStage cstarMatrixInductiveSystem
    ωseed H hH β k v
    (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k).toStarAlgHom
    (seedDensityUnit H hH β) (seedDensityUnit_eq_stage_map H hH β)
    (finiteSeed_representedVacuumTwistedCyclic H hH β v)

def seedComplexTime_ofReal :=
  matrixComplexTime_ofReal CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH

def seedComplexTime_analyticAt :=
  matrixComplexTime_analyticAt CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH

def seedCorrelation_analyticAt :=
  matrixCorrelation_analyticAt CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH

def seedCorrelation_lower_boundary :=
  matrixCorrelation_lower_boundary CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH

def seedCorrelation_upper_boundary (v : ℕ) :=
  matrixCorrelation_upper_boundary CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH β v (seedFunctional_twisted H hH β v)

def seedCorrelation_continuousOn_closedStrip :=
  matrixCorrelation_continuousOn_closedStrip CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH β

def seedCorrelation_differentiableOn_openStrip :=
  matrixCorrelation_differentiableOn_openStrip CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH β

def seedCorrelation_bounded_closedStrip :=
  matrixCorrelation_bounded_closedStrip CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH β

/-- The actual native state satisfies the analytic KMS condition at positive
inverse temperature.  Every generic premise is proved in this specialization. -/
def finiteSeedKMSState (hβ : 0 < β) (v : ℕ) :=
  matrixKMSState CStarMatrixStage cstarMatrixInductiveSystem ωseed
    (seedStageHom H hH β) H hH β hβ v (seedFunctional_twisted H hH β v)

end InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS
