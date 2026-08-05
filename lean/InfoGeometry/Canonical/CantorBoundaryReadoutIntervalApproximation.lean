import InfoGeometry.Canonical.CantorBoundaryDyadicCover

/-!
# Interval-valued binary readout approximation

The binary boundary readout has a genuine finite-prefix approximation theorem.
This file lifts that theorem to the subtype `Set.Icc 0 1`; it does not turn
approximation into surjectivity or identify the quotient with the interval.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation

open InfoGeometry.Canonical.CantorBoundaryDyadicCover
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def intervalReadout (w : InfiniteBinaryWordSpace) : UnitInterval :=
  ⟨realBinaryReadout w, realBinaryReadout_mem_unitInterval w⟩

theorem intervalReadout_approximation
    (x : UnitInterval) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : InfiniteBinaryWordSpace,
      dist x (intervalReadout w) < ε := by
  obtain ⟨w, hw⟩ := exists_realBinaryReadout_close x.1 x.2 hε
  refine ⟨w, ?_⟩
  simpa [intervalReadout, Real.dist_eq] using hw

theorem intervalReadout_mem_closure_range (x : UnitInterval) :
    x ∈ closure (Set.range intervalReadout) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨w, hw⟩ := intervalReadout_approximation x hε
  exact ⟨intervalReadout w, ⟨w, rfl⟩, hw⟩

end InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation
