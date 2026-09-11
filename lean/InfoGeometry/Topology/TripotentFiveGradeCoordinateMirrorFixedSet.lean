import InfoGeometry.Topology.TripotentFiveGradeCoordinateOrbitClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.TripotentFiveGradeCoordinateMirrorFixedSet

open InfoGeometry.Physics.Algebra
open InfoGeometry.Topology
open InfoGeometry.Topology.TripotentFiveGradeMirrorTopological
open InfoGeometry.Topology.TripotentFiveGradeCoordinateModularFlow
open InfoGeometry.Topology.TripotentFiveGradeCoordinateOrbitClosure

def coordinateMirrorFixedPointSet : Set (FiveGrade → ℝ) :=
  symbolicLatentInvolutionFixedPointSet fiveGradeCoordinateMirrorInvolution

theorem mem_coordinateMirrorFixedPointSet_iff (f : FiveGrade → ℝ) :
    f ∈ coordinateMirrorFixedPointSet ↔
      ∀ k : FiveGrade, f (fiveGradeMirror k) = f k := by
  rw [coordinateMirrorFixedPointSet,
    mem_symbolicLatentInvolutionFixedPointSet]
  exact coordinateMirror_fixedPoint_iff f

theorem isClosed_coordinateMirrorFixedPointSet :
    IsClosed coordinateMirrorFixedPointSet := by
  unfold coordinateMirrorFixedPointSet
  exact isClosed_symbolicLatentInvolutionFixedPointSet
    fiveGradeCoordinateMirrorInvolution

theorem coordinateMirrorFixedPointSet_eq :
    coordinateMirrorFixedPointSet =
      {f : FiveGrade → ℝ | ∀ k : FiveGrade,
        f (fiveGradeMirror k) = f k} := by
  ext f
  exact mem_coordinateMirrorFixedPointSet_iff f

theorem coordinateMirrorFixedPointSet_zero_mem :
    (0 : FiveGrade → ℝ) ∈ coordinateMirrorFixedPointSet := by
  rw [mem_coordinateMirrorFixedPointSet_iff]
  intro k
  simp

end InfoGeometry.Topology.TripotentFiveGradeCoordinateMirrorFixedSet
