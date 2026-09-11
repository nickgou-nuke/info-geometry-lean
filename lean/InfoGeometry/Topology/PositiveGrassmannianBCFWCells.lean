import Mathlib.Topology.LocallyClosed
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import InfoGeometry.Topology.PositiveGrassmannianAmplituhedronTopological

/-!
# Finite minor-signature cells

This file records a finite, chart-level proxy for a BCFW cell: selected
maximal minors are required to be positive or zero.  It does not identify
these sets with positroid cells, prove a cell decomposition, or assert a
BCFW tiling theorem.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical
open Matrix

variable {k n : ℕ}

structure MinorCellSpec (k n : ℕ) where
  positiveCount : ℕ
  vanishingCount : ℕ
  positiveIndex : Fin positiveCount → Fin k → Fin n
  vanishingIndex : Fin vanishingCount → Fin k → Fin n

def positiveMinorLocus (spec : MinorCellSpec k n) :
    Set (Matrix (Fin k) (Fin n) ℝ) :=
  {C | ∀ r, 0 < maximalMinor C (spec.positiveIndex r)}

def vanishingMinorLocus (spec : MinorCellSpec k n) :
    Set (Matrix (Fin k) (Fin n) ℝ) :=
  {C | ∀ r, maximalMinor C (spec.vanishingIndex r) = 0}

/-- The finite BCFW-style cell locus obtained by imposing positive and vanishing
minor constraints simultaneously. -/
def minorCellLocus (spec : MinorCellSpec k n) :
    Set (Matrix (Fin k) (Fin n) ℝ) :=
  positiveMinorLocus spec ∩ vanishingMinorLocus spec

theorem isOpen_positiveMinorLocus (spec : MinorCellSpec k n) :
    IsOpen (positiveMinorLocus spec) := by
  rw [show positiveMinorLocus spec =
      ⋂ r : Fin spec.positiveCount,
        (fun C : Matrix (Fin k) (Fin n) ℝ =>
          maximalMinor C (spec.positiveIndex r)) ⁻¹' Set.Ioi 0 by
    ext C
    simp [positiveMinorLocus]]
  apply isOpen_iInter_of_finite
  intro r
  exact isOpen_Ioi.preimage (continuous_maximalMinor (spec.positiveIndex r))

theorem isClosed_vanishingMinorLocus (spec : MinorCellSpec k n) :
    IsClosed (vanishingMinorLocus spec) := by
  rw [show vanishingMinorLocus spec =
      ⋂ r : Fin spec.vanishingCount,
        (fun C : Matrix (Fin k) (Fin n) ℝ =>
          maximalMinor C (spec.vanishingIndex r)) ⁻¹' ({0} : Set ℝ) by
    ext C
    simp [vanishingMinorLocus]]
  apply isClosed_iInter
  intro r
  exact isClosed_singleton.preimage
    (continuous_maximalMinor (spec.vanishingIndex r))

theorem isLocallyClosed_minorCellLocus (spec : MinorCellSpec k n) :
    IsLocallyClosed (minorCellLocus spec) := by
  unfold minorCellLocus
  exact (isOpen_positiveMinorLocus spec).isLocallyClosed.inter
    (isClosed_vanishingMinorLocus spec).isLocallyClosed

/-- The BCFW-style minor cell locus is locally compact inside the ambient
matrix chart. -/
instance minorCellLocus_locallyCompactSpace (spec : MinorCellSpec k n) :
    LocallyCompactSpace (minorCellLocus spec) := by
  haveI : LocallyCompactSpace (Matrix (Fin k) (Fin n) ℝ) := by
    change LocallyCompactSpace (Fin k → Fin n → ℝ)
    infer_instance
  exact (isLocallyClosed_minorCellLocus spec).locallyCompactSpace

end InfoGeometry.Topology
