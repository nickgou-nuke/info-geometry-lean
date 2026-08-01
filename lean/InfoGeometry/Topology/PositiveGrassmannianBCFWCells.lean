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

end InfoGeometry.Topology
