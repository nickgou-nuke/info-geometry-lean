import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredColimitDiracIndexBridge
import InfoGeometry.Canonical.DiracHeatSemigroupBridge

/-!
# Finite-dimensional continuous realization of the algebraic Dirac owner

This file is only the carrier adapter between `FiniteDiracData`, whose
operator is a linear map, and the bounded heat-flow owner, whose operator is a
continuous linear map.  No continuity is added to the generic algebraic
definition: finite dimensionality is an explicit hypothesis here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteDiracContinuousAdapter

open InfoGeometry.Canonical.FilteredColimitDiracIndexBridge
open InfoGeometry.Canonical.DiracHeatSemigroupBridge

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- The bounded realization of an algebraic finite-stage Dirac operator. -/
noncomputable def continuousDirac (D : FiniteDiracData V) : V →L[ℝ] V :=
  D.diracOp.toContinuousLinearMap

theorem continuousDirac_intertwines
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W]
    (DV : FiniteDiracData V) (DW : FiniteDiracData W)
    (f : V →ₗ[ℝ] W)
    (h_comm : DW.diracOp.comp f = f.comp DV.diracOp) :
    (f.toContinuousLinearMap).comp (continuousDirac DV) =
      (continuousDirac DW).comp f.toContinuousLinearMap := by
  ext x
  simpa [continuousDirac] using congrArg (fun g => g x) h_comm.symm

theorem continuousDirac_square_intertwines
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W]
    (DV : FiniteDiracData V) (DW : FiniteDiracData W)
    (f : V →ₗ[ℝ] W)
    (h_comm : DW.diracOp.comp f = f.comp DV.diracOp) :
    (f.toContinuousLinearMap).comp (diracSquareEnd (continuousDirac DV)) =
      (diracSquareEnd (continuousDirac DW)).comp f.toContinuousLinearMap := by
  exact diracSquareEnd_intertwines
    (continuousDirac DV) (continuousDirac DW) f.toContinuousLinearMap
    (continuousDirac_intertwines DV DW f h_comm)

theorem finiteDiracHeatFlow_intertwines
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [FiniteDimensional ℝ W]
    (DV : FiniteDiracData V) (DW : FiniteDiracData W)
    (f : V →ₗ[ℝ] W)
    (h_comm : DW.diracOp.comp f = f.comp DV.diracOp)
    (t : ℝ) (x : V) :
    f.toContinuousLinearMap
        (diracHeatFlow (continuousDirac DV) t x) =
      diracHeatFlow (continuousDirac DW) t (f x) := by
  exact diracHeatFlow_intertwines
    (continuousDirac DV) (continuousDirac DW) f.toContinuousLinearMap
    (continuousDirac_intertwines DV DW f h_comm) t x

end InfoGeometry.Canonical.FiniteDiracContinuousAdapter
