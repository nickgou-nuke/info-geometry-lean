import InfoGeometry.Topology.PositiveGrassmannianAmplituhedronTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compact bounded matrix charts for the finite amplituhedron map

This layer adds only a box-constrained finite matrix chart.  It does not
identify the chart with a Grassmannian quotient and does not assert a
canonical form or a boundary-residue theorem.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical
open Matrix

variable {k n m : ℕ}

/-- Entrywise box of matrices whose coordinates lie in `[a,b]`. -/
def matrixBox (a b : ℝ) : Set (Matrix (Fin k) (Fin n) ℝ) :=
  Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc a b))

theorem isCompact_matrixBox (a b : ℝ) :
    IsCompact (matrixBox (k := k) (n := n) a b) := by
  unfold matrixBox
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))

theorem isCompact_boundedPositiveGrassmannianChart (a b : ℝ) :
    IsCompact
      (matrixBox (k := k) (n := n) a b ∩
        positiveGrassmannianChart (k := k) (n := n)) := by
  exact (isCompact_matrixBox (k := k) (n := n) a b).of_isClosed_subset
    ((isCompact_matrixBox (k := k) (n := n) a b).isClosed.inter
      isClosed_positiveGrassmannianChart)
    Set.inter_subset_left

theorem isCompact_boundedPositiveAmplituhedronImage_box (a b : ℝ)
    (Z : Matrix (Fin n) (Fin m) ℝ) :
    IsCompact
      (amplituhedronMap (k := k) (n := n) (m := m) Z ''
        (matrixBox (k := k) (n := n) a b ∩
          positiveGrassmannianChart (k := k) (n := n))) := by
  exact (isCompact_boundedPositiveGrassmannianChart (k := k) (n := n) a b).image
    (continuous_amplituhedronMap (k := k) (n := n) (m := m) Z)

theorem isClosed_boundedPositiveAmplituhedronImage (a b : ℝ)
    (Z : Matrix (Fin n) (Fin m) ℝ) :
    IsClosed
      (amplituhedronMap (k := k) (n := n) (m := m) Z ''
        (matrixBox (k := k) (n := n) a b ∩
          positiveGrassmannianChart (k := k) (n := n))) := by
  exact (isCompact_boundedPositiveAmplituhedronImage_box
    (k := k) (n := n) (m := m) a b Z).isClosed

end InfoGeometry.Topology
