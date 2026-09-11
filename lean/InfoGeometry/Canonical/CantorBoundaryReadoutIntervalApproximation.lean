import InfoGeometry.Canonical.CantorBoundaryDyadicCover
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Interval-valued binary readout approximation

The binary boundary readout has a genuine finite-prefix approximation theorem.
This file lifts that theorem to the subtype `Set.Icc 0 1`; it does not turn
approximation into surjectivity or identify the quotient with the interval.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation

open InfoGeometry.Canonical.CantorBoundaryDyadicCover
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

local instance unitIntervalT2 : T2Space UnitInterval :=
  TopologicalSpace.t2Space_of_metrizableSpace

def intervalReadout (w : (ℕ → Bool)) : UnitInterval :=
  ⟨realBinaryReadout w, realBinaryReadout_mem_unitInterval w⟩

theorem continuous_intervalReadout :
    Continuous intervalReadout := by
  exact Continuous.subtype_mk continuous_realBinaryReadout (fun w =>
    realBinaryReadout_mem_unitInterval w)

theorem intervalReadout_approximation
    (x : UnitInterval) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : (ℕ → Bool),
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

theorem closure_range_intervalReadout :
    closure (Set.range intervalReadout) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact intervalReadout_mem_closure_range x

theorem denseRange_intervalReadout :
    DenseRange intervalReadout := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  exact intervalReadout_approximation x hε

theorem isCompact_intervalReadout_range :
    IsCompact (Set.range intervalReadout) := by
  letI : CompactSpace (ℕ → Bool) := ⟨cantorBoundary_compact⟩
  simpa only [Set.image_univ] using
    (isCompact_univ.image continuous_intervalReadout)

theorem intervalReadout_surjective :
    Function.Surjective intervalReadout := by
  intro x
  have hclosed : IsClosed (Set.range intervalReadout) :=
    isCompact_intervalReadout_range.isClosed
  have hsubset :
      closure (Set.range intervalReadout) ⊆ Set.range intervalReadout :=
    hclosed.closure_subset_iff.mpr (by
      intro y hy
      exact hy)
  exact hsubset (intervalReadout_mem_closure_range x)

theorem intervalReadout_range_eq_univ :
    Set.range intervalReadout = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact intervalReadout_surjective x

theorem realBinaryReadout_range_eq_unitInterval :
    Set.range realBinaryReadout = Set.Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact realBinaryReadout_mem_unitInterval w
  · intro hy
    let x : UnitInterval := ⟨y, hy⟩
    obtain ⟨w, hw⟩ := intervalReadout_surjective x
    refine ⟨w, ?_⟩
    exact congrArg Subtype.val hw

end InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation
